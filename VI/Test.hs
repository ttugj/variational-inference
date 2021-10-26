{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, DerivingStrategies, GeneralizedNewtypeDeriving, RankNTypes #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Test ( -- * General classes
                 Test(..), TestM(..), doTest'
               , withTolerance
                 -- * Assorted tests
                 -- ** Domains
               , Pair
               , simplexRetractionT, simplexIntervalT
               , trInvolutiveT, symRetractionT
               , mmAssociativeT, mTmT
               , mixSimplexIntervalT
               ) where

import VI.Categories
import VI.Jets
import VI.Domains

import Control.Applicative
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.Reader

import Data.Bool
import Data.Maybe
import Data.Kind
import Prelude (($), uncurry)

import GHC.TypeLits
import GHC.Types
import GHC.Classes
import GHC.Num

-- import Debug.Trace

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'

import qualified System.Random.MWC            as MWC
import           System.Random.Stateful

import qualified Data.Vector.Generic          as G

class Monad m ⇒ TestM m where
    sample ∷ KnownNat n ⇒ m (LA.R n)
    judgeR ∷ KnownNat n ⇒ LA.R n → m Bool
    judgeL ∷ (KnownNat n, KnownNat k) ⇒ LA.L n k → m Bool

class Test a where
    doTest ∷ TestM m ⇒ a → a → m Bool 

instance (Test a, Test b) ⇒ Test (a, b) where
    doTest (a,b) (a',b') = (&&) <$> doTest a a' <*> doTest b b'

instance KnownNat n ⇒ Test (LA.R n) where
    doTest u v = judgeR (u - v) 

instance (KnownNat n, KnownNat k) ⇒ Test (LA.L n k) where
    doTest a b = judgeL (a - b)

instance (KnownNat n, Test a) ⇒ Test (LA.R n → a) where
    doTest f g = sample >>= doTest <$> f <*> g 

instance (KnownNat n, KnownNat k) ⇒ Test (Jet n k) where
    doTest (Jet φ) (Jet ψ) = doTest φ ψ 

instance (Domain x, Domain y) ⇒ Test (Mor x y) where
    doTest (Mor φ) (Mor ψ) = doTest φ ψ

doTest' ∷ (TestM m, Test a) ⇒ (a, a) → m Bool
doTest' = uncurry doTest

data TestContext m = TestContext { gen ∷ MWC.Gen (PrimState m)
                                 , tol ∷ Double
                                 }
instance PrimMonad m ⇒ TestM (ReaderT (TestContext m) m) where
    sample ∷ ∀ n. KnownNat n ⇒ ReaderT (TestContext m) m (LA.R n)
    sample = do
                let n = intVal @n
                g ← asks gen 
                ~(Just xu) ← LA.create <$> G.replicateM n (MWC.uniformRM (-2,2) g)
                return $ 2*xu - 1
    judgeR x = asks tol >>= \ε → return $ G.all (\c → abs c < ε) (LA.extract x) 
    judgeL a = asks tol >>= \ε → return $ G.all (\c → abs c < ε) (LA'.flatten $ LA.extract a) 

withTolerance ∷ Double → (∀ m'. TestM m' ⇒ m' a) → IO a 
withTolerance ε α = MWC.createSystemRandom >>= \g → runReaderT α (TestContext @IO g ε)

type Pair x y = (Mor x y, Mor x y)

simplexRetractionT ∷ KnownNat n ⇒ Pair (Δ n) (Δ n)
simplexRetractionT = (simplexProjection . emb, id)

simplexIntervalT ∷ Pair (Δ 1) (ℝp 2)
simplexIntervalT = (iso . f . iso, emb) where
                        f ∷ Mor (I 1) (ℝp 1, ℝp 1)
                        f = fromPoints $ \x → (emb ▶ x) × ((emb . invol) ▶ x)

trInvolutiveT ∷ (KnownNat m, KnownNat n) ⇒ Pair (M m n) (M m n)
trInvolutiveT = (tr . tr, id)

symRetractionT ∷ (KnownNat n, 1 <= n) ⇒ Pair (Σ n) (Σ n)
symRetractionT = (sym . emb, id)

mmAssociativeT ∷ (KnownNat n, KnownNat m, KnownNat l, KnownNat k) ⇒ Pair ((M n m, M m l), M l k) (M n k)
mmAssociativeT = (mm . (bimap mm id), mm . (bimap id mm) . asR)

mTmT ∷ (KnownNat m, KnownNat n, 1 <= n) ⇒ Pair (M m n) (M n n)
mTmT = (emb . mTm, mm . (bimap tr id) . (id × id))

mixSimplexIntervalT ∷ Pair (I 1, (Δ 1, Δ 1)) (ℝp 1) 
mixSimplexIntervalT = (pr1 . osi @(ℝp 1, ℝp 1) . emb @(Δ 1) @(ℝp 2) . mix, emb . mix @(I 1) . bimap id (bimap iso iso))
