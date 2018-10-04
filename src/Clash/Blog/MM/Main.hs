{-# LANGUAGE QuasiQuotes        #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric      #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Clash.Blog.MM.Main where

import           Clash.Blog.MM.Zip45
import           Clash.Prelude

import Data.Tuple (swap)
import Data.Int (Int8)
import Control.DeepSeq (force, NFData, deepseq)
import Data.Foldable (forM_)
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.Singletons (TyFun, Apply, Proxy(Proxy), type (@@))
import GHC.Stack (HasCallStack)
import qualified Prelude as P
import Debug.Trace
import GHC.Generics (Generic)

-- | Put /n/ registers after given signal.
delayN
  :: forall n dom gated synchronous a
   . HiddenClockReset dom gated synchronous
  => a
  -- ^ Default value register
  -> SNat n
  -- ^ Number of registers to insert
  -> Signal dom a
  -- ^ Signal to delay
  -> Signal dom a
  -- ^ Delayed signal
delayN dflt n@SNat signal =
  foldl (\s _ -> register dflt s) signal (replicate n ())

-- | A single, generalized processing element for a systolic array.
--
--                TB_i   BT_(i+1)
--                  ↓        ↑
--              |---------------|
--   RL_(i-1) ← |               | ←   RL_i
--              |      P_i      |
--     LR_i   → |               | → LR_(i+1)
--              |---------------|
--                  ↓        ↑
--               TB_(i+1)   BT_i
--
type LinearProcessingElement dom m n lr rl tb bt
   = ( (Index m, Index n)
     , Signal dom lr
     , Signal dom rl
     , Signal dom tb
     , Signal dom bt
     )
  -> ( Signal dom lr
     , Signal dom rl
     , Signal dom tb
     , Signal dom bt
     )

-- | Creates a systolic array by chaining multiple LinearProcessingElements. It
-- is up to the user to manage delays.
--
--                 b20   b21   b22
--                 b10   b11   b12
--                 b00   b01   b02
--   a02 a01 a00 |  1  |  2  |  3  →
--   a12 a11 a10 |  2  |  3  |  4  →
--   a22 a21 a20 |  3  |  4  |  5  →
--                  ↓     ↓     ↓
--
systolicArray2D
  :: forall m m0 n n0 lr rl tb bt dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => KnownNat m
  => KnownNat n
  => Show lr
  => Show rl
  => Show tb
  => Show bt
  => NFData lr
  => NFData rl
  => NFData tb
  => NFData bt
  => m ~ (m0 + 1)
  => n ~ (n0 + 1)
  => lr
  -- ^ Default for left registers
  -> rl
  -- ^ Default for right registers
  -> tb
  -- ^ Default for top registers
  -> bt
  -- ^ Default for bottom registers
  -> LinearProcessingElement dom m n lr rl tb bt
  -- ^ Processing element. First argument is the element coming from its left
  -- neighbor. The second argument is the argument coming from its upper neighbor.
  -> Signal dom (Vec m lr)
  -- ^ Inputs from the left
  -> Signal dom (Vec m rl)
  -- ^ Inputs from the right
  -> Signal dom (Vec n tb)
  -- ^ Inputs from the top
  -> Signal dom (Vec n bt)
  -- ^ Inputs from the bottom
  -> ( Signal dom (Vec m lr)
     , Signal dom (Vec m rl)
     , Signal dom (Vec n tb)
     , Signal dom (Vec n bt)
     )
  -- ^ (rights, lefts, bottoms, tops)
systolicArray2D lr rl tb bt pelem lrs rls tbs bts = (lrs''', rls''', tbs''', bts''')
  where
    -- From `Signal dom (Vec m a)` to `Vec m (Signal dom a)`:
    (lrs', rls', tbs', bts') =
      (unbundle lrs, unbundle rls, unbundle tbs, unbundle bts)

    -- Tie PE columns together:
    (lrss', rlss', tbs'', bts'') =
      unzip4 $ map syscol $ zip5 indicesI lrss rlss tbs' bts'

    lrss  = lrs' :> init lrss'
    rlss  = tail rlss' :< rls'
    lrs'' = last lrss'
    rls'' = head rlss'

    -- From `Vec m (Signal dom a)` to `Signal dom (Vec m a)`:
    (lrs''', rls''', tbs''', bts''') =
      (bundle lrs'', bundle rls'', bundle tbs'', bundle bts'')

    pelem' = delayPelem pelem lr rl tb bt

    syscol (n, lrs, rls, tb, bt) = (lrs', rls', tb', bt')
      where
        mn = zip indicesI (repeat n)

        (lrs', rls', tbs', bts') =
          unzip4 $ map pelem' $ zip5 mn lrs rls tbs bts

        tbs = tb :> init tbs'
        bts = tail bts' :< bt
        tb' = last tbs'
        bt' = head bts'


-- | Creates a systolic array, but manages delays such that input from the left
-- and top arrive at the same time at specific cells. Inputs from the right and
-- bottom are unmanaged.
--
--                                     b22
--                               b21   b12
--                         b20   b11   b02
--                         b10   b01    ?
--                         b00    ?     ?
--           a02 a01 a00 |  1  |  2  |  3   ?   ?  →
--       a12 a11 a10  ?  |  2  |  3  |  4   ?   →
--   a22 a21 a20  ?   ?  |  3  |  4  |  5   →
--                          ?     ?     ↓
--                          ?     ↓
--                          ↓
--
-- Registers are inserted at the question marks. This causes a10 and b00 to
-- arrive at the same time in the cell labelled '2' in the first column, just
-- like a20 and b00 arrive in '3' at the same time.
--
-- A total of /m^2 - m + n^2 - n + 2/ registers will be added.
systolicArray2Dd
  :: forall m m0 n n0 lr rl tb bt dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => KnownNat m
  => KnownNat n
  => Show lr
  => Show rl
  => Show tb
  => Show bt
  => NFData lr
  => NFData rl
  => NFData tb
  => NFData bt
  => m ~ (m0 + 1)
  => n ~ (n0 + 1)
  => lr
  -- ^ Default for left registers
  -> rl
  -- ^ Default for right registers
  -> tb
  -- ^ Default for top registers
  -> bt
  -- ^ Default for bottom registers
  -> LinearProcessingElement dom m n lr rl tb bt
  -- ^ Processing element. First argument is the element coming from its left
  -- neighbor. The second argument is the argument coming from its upper neighbor.
  -> Signal dom (Vec m lr)
  -- ^ Inputs from the left
  -> Signal dom (Vec m rl)
  -- ^ Inputs from the right
  -> Signal dom (Vec n tb)
  -- ^ Inputs from the top
  -> Signal dom (Vec n bt)
  -- ^ Inputs from the bottom
  -> ( Signal dom (Vec m lr)
     , Signal dom (Vec m rl)
     , Signal dom (Vec n tb)
     , Signal dom (Vec n bt)
     )
  -- ^ (rights, lefts, bottoms, tops)
systolicArray2Dd lr rl tb bt pelem lrs rls tbs bts = (lrs''', rls''', tbs''', bts''')
  where
    -- Append delays to array inputs
    lrs' = bundle (smap (delayN lr) (unbundle lrs))
    rls' = bundle (smap (delayN rl) (unbundle rls))
    tbs' = bundle (smap (delayN tb) (unbundle tbs))
    bts' = bundle (smap (delayN bt) (unbundle bts))

    -- Create systolic array without delays of outputs
    (lrs'', rls'', tbs'', bts'') =
      systolicArray2D lr rl tb bt pelem lrs' rls' tbs' bts'

    -- Append delays to array outputs
    lrs''' = bundle $ reverse $ smap (delayN lr) (reverse $ unbundle lrs'')
    rls''' = bundle $ reverse $ smap (delayN rl) (reverse $ unbundle rls'')
    tbs''' = bundle $ reverse $ smap (delayN tb) (reverse $ unbundle tbs'')
    bts''' = bundle $ reverse $ smap (delayN bt) (reverse $ unbundle bts'')


-- | Creates a systolic array, and [d]elays for one set of inputs, but keeps
-- it [u]ndelayed for others.
systolicArray2Dud
  :: forall m m0 n n0 lru lrd rlu rld tbu tbd btu btd bru brd dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => KnownNat m
  => KnownNat n
  => Show lru
  => Show lrd
  => Show rlu
  => Show rld
  => Show tbu
  => Show tbd
  => Show btu
  => Show btd
  => NFData lru
  => NFData lrd
  => NFData rlu
  => NFData rld
  => NFData tbu
  => NFData tbd
  => NFData btu
  => NFData btd
  => m ~ (m0 + 1)
  => n ~ (n0 + 1)
  => (lru, lrd)
  -- ^ Default for left registers
  -> (rlu, rld)
  -- ^ Default for right registers
  -> (tbu, tbd)
  -- ^ Default for top registers
  -> (btu, btd)
  -- ^ Default for bottom registers
  -> LinearProcessingElement dom m n (lru, lrd) (rlu, rld) (tbu, tbd) (btu, btd)
  -- ^ Processing element. First argument is the element coming from its left
  -- neighbor. The second argument is the argument coming from its upper neighbor.
  -> Signal dom (Vec m lru)
  -- ^ Undelayed inputs from the left
  -> Signal dom (Vec m lrd)
  -- ^ Delayed inputs from the left
  -> Signal dom (Vec m rlu)
  -- ^ Undelayed inputs from the right
  -> Signal dom (Vec m rld)
  -- ^ Delayed inputs from the right
  -> Signal dom (Vec n tbu)
  -- ^ Undelayed inputs from the top
  -> Signal dom (Vec n tbd)
  -- ^ Delayed inputs from the top
  -> Signal dom (Vec n btu)
  -- ^ Undelayed inputs from the bottom
  -> Signal dom (Vec n btd)
  -- ^ Delayed inputs from the bottom
  -> ( Signal dom (Vec m lru)
     , Signal dom (Vec m lrd)
     , Signal dom (Vec m rlu)
     , Signal dom (Vec m rld)
     , Signal dom (Vec n tbu)
     , Signal dom (Vec n tbd)
     , Signal dom (Vec n btu)
     , Signal dom (Vec n btd)
     )
  -- ^ (rights, lefts, bottoms, tops)
systolicArray2Dud
  lr@(lru, lrd)
  rl@(rlu, rld)
  tb@(tbu, tbd)
  bt@(btu, btd)
  pelem
  lrus lrds
  rlus rlds
  tbus tbds
  btus btds =
  (lrus', lrds''', rlus', rlds''', tbus', tbds''', btus', btds''')
  where
    -- Append delays to array inputs
    lrds' = bundle (smap (delayN lrd) (unbundle lrds))
    rlds' = bundle (smap (delayN rld) (unbundle rlds))
    tbds' = bundle (smap (delayN tbd) (unbundle tbds))
    btds' = bundle (smap (delayN btd) (unbundle btds))

    -- Bundle delayed and undelayed signals
    lrs = zip <$> lrus <*> lrds'
    rls = zip <$> rlus <*> rlds'
    tbs = zip <$> tbus <*> tbds'
    bts = zip <$> btus <*> btds'

    -- Create systolic array without delays of outputs
    (lrs', rls', tbs', bts') =
      systolicArray2D lr rl tb bt pelem lrs rls tbs bts

    -- Unbundle delayed and undelayed signals
    (lrus', lrds'') = (fmap fst <$> lrs', fmap snd <$> lrs')
    (rlus', rlds'') = (fmap fst <$> rls', fmap snd <$> rls')
    (tbus', tbds'') = (fmap fst <$> tbs', fmap snd <$> tbs')
    (btus', btds'') = (fmap fst <$> bts', fmap snd <$> bts')

    -- Append delays to array outputs
    lrds''' = bundle $ reverse $ smap (delayN lrd) (reverse $ unbundle lrds'')
    rlds''' = bundle $ reverse $ smap (delayN rld) (reverse $ unbundle rlds'')
    tbds''' = bundle $ reverse $ smap (delayN tbd) (reverse $ unbundle tbds'')
    btds''' = bundle $ reverse $ smap (delayN btd) (reverse $ unbundle btds'')


-- | Instruction for matrix multiplication element when communicating upwards.
data InstrPEUp
  = Clear
  -- ^ Clear state, push old state to upper neighbor
  | Data
  -- ^ Move data from neighbor below to upper neighbor
    deriving (Generic, Show, Eq, NFData)

-- | Instructions sent synchronously to a column of processing elements
data SyncInstrPEDown
  = Pass
  -- ^ Take data from upper neighbor, pass to lower neighbor
  | Inject
  -- ^ Discard data from upper neighbor, pass own storage to lower neighbor
    deriving (Generic, Show, Eq, NFData)

-- | Instructions sent asynchronously to a column of processing elements
data AsyncInstrPEDown
  = Accum
  -- ^ Accumulate products of incoming signals
  | Store
  -- ^ Move current result to storage
    deriving (Generic, Show, Eq, NFData)


-- |
generalMatrixMultiplicationDown
  :: forall a n m p dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => Num a
  => Show a
  => NFData a
  => KnownNat m
  => KnownNat p
  => SNat (n + 1)
  -- ^ Number of columns / rows of left matrix / right matrix
  -> Signal dom (Vec (m + 1) a)
  -- ^ Columns of left matrix
  -> Signal dom (Vec (p + 1) a)
  -- ^ Rows of right matrix
  -> Signal dom (Vec (p + 1) a)
  -- ^ Rows of result matrix, in reverse order
generalMatrixMultiplicationDown n@SNat cols rows = fmap snd <$> tbs'
  where
    -- Determine inputs for systolic array:
    counter :: Signal dom (Index (n + 1))
    counter = register minBound (satPlus SatWrap 1 <$> counter)

    sysCmd n
      | n == maxBound = (repeat Inject, repeat Store)
      | otherwise     = (repeat Pass,   repeat Accum)

    (lrus, dcmds) = unbundle (sysCmd <$> counter)

    -- Pass columns and delayed commands from the left, and the rows and dummy
    -- passthrough values from the top:
    lrds = zip <$> cols <*> dcmds
    tbds = zip <$> rows <*> pure (repeat 0)

    -- nothingP and nothingM differ in vector length, thus having different
    -- types, explaining the seemingly duplicate definitions:
    nothingP = pure $ repeat ()
    nothingM = pure $ repeat ()

    -- Create actual array:
    (_, _, _, _, _, tbs', _, _) =
      systolicArray2Dud
        -- Defaults for registers
        (Inject, (0, Store)) ((), ()) ((), (0, 0)) ((), ())
        -- Processing element
        pelemDown
        -- Inputs:
        lrus     lrds
        nothingM nothingM
        nothingP tbds
        nothingP nothingP

    -- Processing element:
    pelemDown ((m, n), lrs, rls, tbs, bts) = (lrs, rls, tbs'', bts)
      where
        tbs'  = mealy pelem' (0, 0) $ bundle (lrs, snd <$> tbs)
        tbs'' = liftA2 (,) (fst <$> tbs) tbs'

        pelem' (s1, s2)  ((Pass,   (a, Accum)), (b, res))  = ((s1+a*b, s2    ),  (b, res))
        pelem' (s1, _s2) ((Pass,   (a, Store)), (b, res))  = ((0,      s1+a*b),  (b, res))
        pelem' (s1, s2)  ((Inject, (a, Accum)), (b, _res)) = ((s1+a*b, s2    ),  (b, s2))
        pelem' (s1, s2)  ((Inject, (a, Store)), (b, res))  = ((0,      s1+a*b),  (b, s2))


-- | Matrix multiplications can be calculated using systolic arrays, as shown
-- in various papers - including the following presentation:
--
--   http://web.cecs.pdx.edu/~mperkows/temp/May22/0020.Matrix-multiplication-systolic.pdf
--
-- This systolic matrix multiplication algorithm slightly modifies the algorithm
-- shown in the presentation by extending the processing element to also move its
-- results to its upper neighbor. Multiplications of two square matrices († see
-- footnote) have the nice property of each processing element producing exactly
-- one result every /n/ cycles, where /n/ is the number of rows/columns of the
-- matrices. By strategically moving results to their upper neighbors, processing
-- elements can get their data to the borders of the systolic array without
-- sacrificing performance.
--
-- Depending on whether the matrices have an even or odd number of rows a slightly
-- different scheduling is needed. This changes the API, so please see
-- `oddSquareMatrixMultiplicationUp` and `evenSquareMatrixMultiplicationUp` for more
-- info.
--
-- † its not only square matrices which have this property. Similar properties
-- exist for any multiplications where `A ~ m x n` and `B ~ n x p` and `n ~ im`
-- when moving results from bottom to top. When moving results from right to
-- left, `n ~ ip` would suffice.
--
squareMatrixMultiplicationUp
  :: forall period a n n0 i dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => Num a
  => Show a
  => NFData a
  => KnownNat n
  => n ~ (n0 + 1)
  => Signal dom (Vec n (InstrPEUp, a), Vec n a)
  -- ^ Instructions to feed to systolic array
  -> Signal dom (Vec n a)
  -- ^ Rows of result matrix. Alternates between the nth and (n+1)th matrix.
squareMatrixMultiplicationUp instrs = bts'
  where
    -- Create systolic array:
    bts             = pure (repeat 0)
    rls             = pure (repeat ())
    (lrs, tbs)      = unbundle $ instrs

    (_, _, _, bts') =
      systolicArray2Dd
        -- defaults:
        (Clear, 0) () undefined undefined
        -- processing element:
        pelem
        -- inputs:
        lrs rls tbs bts

    -- | Processing element:
    pelem ((m, n), lrs, rls, tbs, bts) = (lrs, rls, tbs, bts')
      where
        bts' = mealy pelemUp 0 $ bundle (lrs, tbs, bts)
        pelemUp c ((Clear, a), b, _bt) = (0,       a*b + c)
        pelemUp c ((Data, a),  b, bt)  = (a*b + c, bt)



-- | Multiplies matrices where both input matrices are square, and their number
-- of rows odd. Rows and columns must continuously be supplied. Input and output
-- corresponds as follows:
--
--   input | output
--   --------------
--   m0    |
--   m0    |
--   m0    |
--   m1    |
--   m1    | m0
--   m1    |
--   m2    | m0
--   m2    | m1
--   m2    | m0
--   m3    | m1
--   m3    | m2
--   m3    | m1
--   ...   | ...
--
--  .. for matrices with 3 rows. In general, for matrices with /n/ rows it holds
-- that /n-1/ cycles after supplying the last row/column of a matrix the first
-- result row will be returned. The next one will appear two cycles later, etc.
--
-- Latency: 2n - 1
--
-- Registers needed:
--   * Delays at sides (left, 2 * top): ³/₂(n²-n)
--   * Storage in processing elements:  2n²
--
-- Processing element utilization: 100%
--
oddSquareMatrixMultiplicationUp
  :: forall a n i dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => Num a
  => Show a
  => NFData a
  => KnownNat n
  => n ~ ((2*i) + 1)
  => Signal dom (Vec n a)
  -- ^ Columns of left matrix
  -> Signal dom (Vec n a)
  -- ^ Rows of right matrix
  -> Signal dom (Vec n a)
  -- ^ Rows of result matrix. Alternates
oddSquareMatrixMultiplicationUp cols rows = bts
  where
    bts = squareMatrixMultiplicationUp (sysInput <$> counter <*> cols <*> rows)

    -- Determine inputs for systolic array:
    counter :: Signal dom (Index n)
    counter = register minBound (satPlus SatWrap 1 <$> counter)

    sysInput n col row
      | n == maxBound = (zip (repeat Clear) col, row)
      | otherwise     = (zip (repeat Data)  col, row)

-- | Multiplies matrices where both input matrices are square, and their number
-- of rows is even. Rows and columns must continuously be supplied, with a cycle
-- of rest between every matrix. Input and output corresponds as follows:
--
--   input | output
--   --------------
--   m0    |
--   m0    |
--   m0    |
--   m0    |
--   XXXX  |
--   m1    |
--   m1    |
--   m1    |
--   m1    | m0
--   XXXX  |
--   m2    | m0
--   m2    |
--   m2    | m0
--   m2    | m1
--   XXXX  | m0
--   m3    | m1
--   m3    | XXXX
--   m3    | m1
--   m3    | m2
--   XXXX  | m1
--   ...   | ...
--
--  .. for matrices with 4 rows. In general, for matrices with /n/ rows it holds
-- that n cycles after supplying the last row/column of a matrix the first
-- result row will be returned. The next one will appear two cycles later, etc.
--
-- Latency: 2n
--
-- Registers needed:
--   * Delays at sides (left, 2 * top): ³/₂(n²-n)
--   * Storage in processing elements:  2n²
--
-- Processing element utilization for number of rows:
--
--   2:   0.66
--   8:   0.88
--   16:  0.94
--   64:  0.98
--   256: 0.99
--   n:   n/(n+1)
--
evenSquareMatrixMultiplicationUp
  :: forall a n i dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => Num a
  => Show a
  => NFData a
  => KnownNat n
  => n ~ (2+(2*i))
  => Signal dom (Vec n a)
  -- ^ Columns of left matrix
  -> Signal dom (Vec n a)
  -- ^ Rows of right matrix
  -> Signal dom (Vec n a)
  -- ^ Rows of result matrix. Alternates
evenSquareMatrixMultiplicationUp cols rows = bts
  where
    bts = squareMatrixMultiplicationUp (sysInput <$> counter <*> cols <*> rows)

    -- Determine inputs for systolic array:
    counter :: Signal dom (Index (n+1))
    counter = register minBound (satPlus SatWrap 1 <$> counter)

    sysInput n col row
      | n == maxBound = (zip (repeat Clear) col, row)
      | otherwise     = (zip (repeat Data) col,  row)

-- Builds a single column for 'triangularSystolicArray'
triangularColumn
  :: forall tb dg lr n dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => KnownNat n
  => (Signal dom tb -> Signal dom dg -> (Signal dom dg, Signal dom lr))
  -- ^ Function for ○
  -> (Signal dom tb -> Signal dom lr -> (Signal dom tb, Signal dom lr))
  -- ^ Function for ◻
  -> (tb, dg, lr)
  -- ^ Register defaults
  -> Signal dom tb
  -- ^ Vertical input
  -> Signal dom dg
  -- ^ Diagonal input
  -> Signal dom (Vec n lr)
  -- ^ Horizontal input
  -> ( Signal dom dg
     , Signal dom (Vec (n + 1) lr) )
triangularColumn edgeF innerF (tb, dg, lr) top diagonal (unbundle -> lefts) =
  (diagonal', bundle $ rights :< right)
    where
      -- Simple helper function to delay tuples
      bidelay (adflt, bdflt) (a, b) = (register adflt a, register bdflt b)

      -- Apply inner functions
      (bottom, rights) = mapAccumL innerF' top lefts
      innerF' top left = bidelay (tb, lr) (innerF top left)

      -- Terminate with edge function
      (diagonal', right) = bidelay (dg, lr) $ edgeF bottom diagonal


data
  TriangularMotive
    (dg :: *)
    (lr :: *)
    (dom :: Domain)
    (f :: TyFun Nat *) :: *

type instance Apply (TriangularMotive dg lr dom) n =
  (Signal dom dg, Signal dom (Vec n lr))


-- | Systolic array needed for algorithms described in:
--
--      Matrix triangularization by systolic arrays
--
--   by:
--
--      W.M. Gentleman, H.T. Kung
--
--  Visualized:
--
--      O   O   O   O   O
--      ↓   ↓   ↓   ↓   ↓
--      O   O   O   O   .
--      ↓   ↓   ↓   ↓   ↓
--      O   O   O   .   .
--      ↓   ↓   ↓   ↓   ↓
--      O   O   .   .   .
--      ↓   ↓   ↓   ↓   ↓
--      O   .   .   .   .
--      ↓   ↓   ↓   ↓   ↓
--      ○ → ◻ → ◻ → ◻ → ◻ →
--          ↓   ↓   ↓   ↓
--          ○ → ◻ → ◻ → ◻ →
--              ↓   ↓   ↓
--              ○ → ◻ → ◻ →
--                  ↓   ↓
--                  ○ → ◻ →
--                      ↓
--                      ○ →
--
--
triangularSystolicArray
  :: forall n tb dg lr dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => KnownNat n
  => (Signal dom tb -> Signal dom dg -> (Signal dom dg, Signal dom lr))
  -- ^ Function for ○
  -> (Signal dom tb -> Signal dom lr -> (Signal dom tb, Signal dom lr))
  -- ^ Function for ◻
  -> (tb, dg, lr)
  -- ^ Register defaults
  -> Signal dom (Vec n tb)
  -- ^ Input from top
  -> Signal dom dg
  -- ^ Input for first ○
  -> (Signal dom dg, Signal dom (Vec n lr))
  -- ^ (right outputs, diagonal output of last ○)
triangularSystolicArray edgeF innerF dflts@(tbdflt, _, _) tops diagonal =
  (diagonal', rights)
    where
      -- Add delays to top inputs, as described in paper
      tops' = smap (delayN tbdflt) (unbundle tops)

      -- Fold over top inputs, progressively expanding the triangular array
      (diagonal', rights) =
        dfold
          (Proxy @ (TriangularMotive dg lr dom))
          go
          (diagonal, pure Nil)
          tops'

      -- Simple wrapping function around 'triangularColumn'. Explicit types are
      -- needed to not confuse the type checker.
      go
        :: forall l
         . SNat l
        -> Signal dom tb
        -> (Signal dom dg, Signal dom (Vec l lr))
        -> (Signal dom dg, Signal dom (Vec (l + 1) lr))
      go l@SNat tb (dg, lrs) =
        triangularColumn edgeF innerF dflts tb dg lrs

safeQuot :: Integral a => a -> a -> a
safeQuot a 0 = 0
safeQuot a b = quot a b

neighborPivotTriangularization
  :: forall n a dom gated synchronous
   . HiddenClockReset dom gated synchronous
  => Integral a
  => KnownNat n
  => Signal dom (Vec n a)
  -- ^ Rows of matrix
  -> Signal dom (Vec n a)
neighborPivotTriangularization rows = fmap fst <$> lrs
  where
    -- Instantiate systolic array
    (_, lrs) =
      triangularSystolicArray
        -- Processing elements:
        edgeF' innerF'
        -- Defaults for registers:
        (0, (), (0, False))
        -- Top-bottom input:
        rows
        -- Diagonal input:
        (pure ())

    -- Turn mealy machines into signal constructs
    edgeF' tb dg  = (dg, mealy edgeF 0 tb)
    innerF' tb lr = (mealy innerF 0 (liftA2 (,) tb lr), lr)

    -- "Internal cell" as mealy machine
    innerF x (x', (m', True))  = (x', x  + (m' * x'))
    innerF x (x', (m', False)) = (x,  x' + (m' * x ))

    -- "Boundary cell" as mealy machine
    edgeF x x'
      | abs x' >= abs x = (x', (safeQuot x x',          True))
      | otherwise       = (x,  (negate $ safeQuot x' x, False))

delayPelem pelem lrdflt rldflt tbdflt btdflt input =
  ( register lrdflt lr'
  , register rldflt rl'
  , register tbdflt tb'
  , register btdflt bt' )
  where
    (lr', rl', tb', bt') = pelem input

defaultPelem ((m, n), lrs, rls, tbs, bts) = (lrs, rls, tbs+lrs, bts)

main :: IO ()
main =
  withClockReset systemClockGen systemResetGen main'

ex1
  :: HiddenClockReset dom gated synchronous
  => HasCallStack
  => IO ()
ex1 = do
  let lrs = [1 :> 2 :> 3 :> 4 :> Nil] P.++ P.repeat (repeat 0) :: [Vec 4 Int]
  let rls = [5 :> 6 :> 7 :> 8 :> Nil] P.++ P.repeat (repeat 0) :: [Vec 4 Int]
  let tbs = [9 :> 0 :> 1 :> 2 :> Nil] P.++ P.repeat (repeat 0) :: [Vec 4 Int]
  let bts = [3 :> 4 :> 5 :> 6 :> Nil] P.++ P.repeat (repeat 0) :: [Vec 4 Int]

  let
    (lrs', rls', tbs', bts') =
      systolicArray2D
        0 0 0 0
        defaultPelem
        (fromList lrs)
        (fromList rls)
        (fromList tbs)
        (fromList bts)

  putStrLn $ show $ sampleN 5 lrs'
  putStrLn $ show $ sampleN 5 rls'
  putStrLn $ show $ sampleN 5 tbs'
  putStrLn $ show $ sampleN 5 bts'

ex2
  :: HiddenClockReset dom gated synchronous
  => HasCallStack
  => IO ()
ex2 = do
  let o = 0 :: Int8

  -- First set of matrices:
  let
    matrixA1 =
      (1 :> 2 :> 1 :> Nil) :>
      (o :> 1 :> o :> Nil) :>
      (2 :> 3 :> 4 :> Nil) :> Nil

  let
    matrixA1T =
      transpose matrixA1

  let
    matrixB1 =
      (2 :> 5 :> 1 :> Nil) :>
      (6 :> 7 :> 1 :> Nil) :>
      (1 :> 8 :> 1 :> Nil) :> Nil

  let
    matrixC1 =
      (15 :> 27 :> 4 :> Nil) :>
      (6  :> 7  :> 1 :> Nil) :>
      (26 :> 63 :> 9 :> Nil) :> Nil

  -- Second set of matrices:
  let
    matrixA2 =
      (5 :> 8 :> 0 :> Nil) :>
      (4 :> 6 :> 9 :> Nil) :>
      (2 :> 3 :> 7 :> Nil) :> Nil

  let
    matrixA2T =
      transpose matrixA2

  let
    matrixB2 =
      (1 :> 5 :> 1 :> Nil) :>
      (5 :> 2 :> 5 :> Nil) :>
      (3 :> 5 :> 3 :> Nil) :> Nil

  let
    matrixC2 =
      (45 :> 41 :> 45 :> Nil) :>
      (61 :> 77 :> 61 :> Nil) :>
      (38 :> 51 :> 38 :> Nil) :> Nil

  let
    cols =
      [ matrixA1T !! 0
      , matrixA1T !! 1
      , matrixA1T !! 2
      , matrixA2T !! 0
      , matrixA2T !! 1
      , matrixA2T !! 2
      ] P.++ (P.repeat $ repeat 0)

  let
    rows =
      [ matrixB1  !! 0
      , matrixB1  !! 1
      , matrixB1  !! 2
      , matrixB2  !! 0
      , matrixB2  !! 1
      , matrixB2  !! 2
      ] P.++ (P.repeat $ repeat 0)

  let cols'   = fromList cols
  let rows'   = fromList rows
  let results = oddSquareMatrixMultiplicationUp cols' rows'

  putStrLn $ showX $ sampleN 15 results

ex3
  :: HiddenClockReset dom gated synchronous
  => HasCallStack
  => IO ()
ex3 = do
  let o = 0 :: Int8

  -- First set of matrices:
  let
    matrixA1 =
      (1 :> 2 :> 1 :> 7 :> Nil) :>
      (o :> 2 :> o :> 5 :> Nil) :>
      (2 :> 3 :> 4 :> 9 :> Nil) :>
      (2 :> 2 :> 9 :> 3 :> Nil) :> Nil

  let
    matrixA1T =
      transpose matrixA1

  let
    matrixB1 =
      (2 :> 5 :> 3 :> 1 :> Nil) :>
      (6 :> 7 :> 4 :> 7 :> Nil) :>
      (1 :> 8 :> 1 :> 5 :> Nil) :>
      (0 :> 5 :> 5 :> 1 :> Nil) :> Nil

  let
    matrixC1 =
      (15 :> 62  :> 47 :> 27 :> Nil) :>
      (12 :> 39  :> 33 :> 19 :> Nil) :>
      (26 :> 108 :> 67 :> 52 :> Nil) :>
      (25 :> 111 :> 38 :> 64 :> Nil) :> Nil

  -- Second set of matrices:
  let
    matrixA2 =
      (1 :> 2 :> 1 :> 7 :> Nil) :>
      (o :> 1 :> o :> 5 :> Nil) :>
      (2 :> 3 :> 1 :> 9 :> Nil) :>
      (2 :> 2 :> 9 :> 1 :> Nil) :> Nil

  let
    matrixA2T =
      transpose matrixA2

  let
    matrixB2 =
      (1 :> 5 :> 3 :> 1 :> Nil) :>
      (6 :> 1 :> 4 :> 7 :> Nil) :>
      (1 :> 8 :> 1 :> 5 :> Nil) :>
      (0 :> 5 :> 5 :> 1 :> Nil) :> Nil

  let
    matrixC2 =
      (14 :> 50 :> 47 :> 27 :> Nil) :>
      (6  :> 26 :> 29 :> 12 :> Nil) :>
      (21 :> 66 :> 64 :> 37 :> Nil) :>
      (23 :> 89 :> 28 :> 62 :> Nil) :> Nil

  let
    cols =
      [ matrixA1T !! 0
      , matrixA1T !! 1
      , matrixA1T !! 2
      , matrixA1T !! 3
      , undefined
      , matrixA2T !! 0
      , matrixA2T !! 1
      , matrixA2T !! 2
      , matrixA2T !! 3
      , undefined
      , matrixA1T !! 0
      , matrixA1T !! 1
      , matrixA1T !! 2
      , matrixA1T !! 3
      , undefined
      , matrixA2T !! 0
      , matrixA2T !! 1
      , matrixA2T !! 2
      , matrixA2T !! 3
      , undefined
      ] P.++ (P.repeat $ repeat 0)

  let
    rows =
      [ matrixB1  !! 0
      , matrixB1  !! 1
      , matrixB1  !! 2
      , matrixB1  !! 3
      , undefined
      , matrixB2  !! 0
      , matrixB2  !! 1
      , matrixB2  !! 2
      , matrixB2  !! 3
      , undefined
      , matrixB1  !! 0
      , matrixB1  !! 1
      , matrixB1  !! 2
      , matrixB1  !! 3
      , undefined
      , matrixB2  !! 0
      , matrixB2  !! 1
      , matrixB2  !! 2
      , matrixB2  !! 3
      , undefined
      ] P.++ (P.repeat $ repeat 0)

  let cols'   = fromList cols
  let rows'   = fromList rows
  let results = evenSquareMatrixMultiplicationUp cols' rows'

  putStrLn $ showX $ sampleN 25 results

ex4
  :: HiddenClockReset dom gated synchronous
  => HasCallStack
  => IO ()
ex4 = do
  let o = 0 :: Int8

  -- First set of matrices:
  let
    matrixA1 =
      (1 :> 2 :> 1 :> Nil) :>
      (o :> 1 :> o :> Nil) :>
      (2 :> 3 :> 4 :> Nil) :> Nil

  let
    matrixA1T =
      transpose matrixA1

  let
    matrixB1 =
      (2 :> 5 :> 1 :> Nil) :>
      (6 :> 7 :> 1 :> Nil) :>
      (1 :> 8 :> 1 :> Nil) :> Nil

  let
    matrixC1 =
      (15 :> 27 :> 4 :> Nil) :>
      (6  :> 7  :> 1 :> Nil) :>
      (26 :> 63 :> 9 :> Nil) :> Nil

  -- Second set of matrices:
  let
    matrixA2 =
      (5 :> 8 :> 0 :> Nil) :>
      (4 :> 6 :> 9 :> Nil) :>
      (2 :> 3 :> 7 :> Nil) :> Nil

  let
    matrixA2T =
      transpose matrixA2

  let
    matrixB2 =
      (1 :> 5 :> 1 :> Nil) :>
      (5 :> 2 :> 5 :> Nil) :>
      (3 :> 5 :> 3 :> Nil) :> Nil

  let
    matrixC2 =
      (45 :> 41 :> 45 :> Nil) :>
      (61 :> 77 :> 61 :> Nil) :>
      (38 :> 51 :> 38 :> Nil) :> Nil

  let
    cols =
      [ matrixA1T !! 0
      , matrixA1T !! 1
      , matrixA1T !! 2
      , matrixA2T !! 0
      , matrixA2T !! 1
      , matrixA2T !! 2
      ] P.++ (P.repeat $ repeat 0)

  let
    rows =
      [ matrixB1  !! 0
      , matrixB1  !! 1
      , matrixB1  !! 2
      , matrixB2  !! 0
      , matrixB2  !! 1
      , matrixB2  !! 2
      ] P.++ (P.repeat $ repeat 0)

  let cols'   = fromList cols
  let rows'   = fromList rows
  let results = generalMatrixMultiplicationDown (SNat @ 3) cols' rows'

  putStrLn $ showX $ sampleN 15 results

main'
  :: HiddenClockReset dom gated synchronous
  => HasCallStack
  => IO ()
main' = do
--   ex1
--   ex2
--   ex3
  ex4

