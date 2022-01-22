{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, DerivingStrategies, GeneralizedNewtypeDeriving, RankNTypes #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Test ( -- * General classes for tests  
        -- 
        -- |
        -- This module provides a rudimentary testing framework,
        -- where a typical property is expressed as an equality
        -- between two morphisms of domains.
        --
        -- The class 'Test' is instantiated by testable types, in particular @'Mor' x y@.
        --
        -- A typical test is of the form
        -- @someT ∷ Pair x y@, and can be run as
        --
        -- @ withTolerance ε (doTest' someT) ∷ IO Bool @
        --
        -- where @ε ∷ Double@ is a reasonably minuscule positive real number.
                 Test(..), TestM(..), doTest'
               , withTolerance
                 -- * Assorted tests
                 -- ** Domains
               , Pair
               , simplexRetractionT, simplexIntervalT
               , trInvolutiveT, symRetractionT
               , mmAssociativeT, mmTT
               , lerpSimplexIntervalT
               , cholInverseT
                 -- ** Quasiarrows
               , standardGaussianT 
                 -- * Debugging
               , valueAtPoint, gradAtPoint, evalAtPoint, getMatrix', randomPoint
               ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Quasiarrows

import Control.Applicative
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.Reader

import Data.Bool
import Data.Maybe
import Data.Kind
import Prelude (($), uncurry, undefined)

import GHC.TypeNats
import GHC.Types
import GHC.Classes
import GHC.Num
import GHC.Real

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'

import qualified System.Random.MWC            as MWC
import           System.Random.Stateful

import qualified Data.Vector.Generic          as G

class Monad m ⇒ TestM m where
    sampleR ∷ KnownNat n ⇒ m (LA.R n)
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
    doTest f g = sampleR >>= doTest <$> f <*> g 

instance (KnownNat n, KnownNat k) ⇒ Test (J n k) where
    doTest (J φ) (J ψ) = doTest φ ψ 

instance (Domain x, Domain y) ⇒ Test (Mor x y) where
    doTest (Mor φ) (Mor ψ) = doTest φ ψ

doTest' ∷ (TestM m, Test a) ⇒ (a, a) → m Bool
doTest' = uncurry doTest

data TestContext m = TestContext { gen ∷ MWC.Gen (PrimState m)
                                 , tol ∷ Double
                                 }
instance PrimMonad m ⇒ TestM (ReaderT (TestContext m) m) where
    sampleR ∷ ∀ n. KnownNat n ⇒ ReaderT (TestContext m) m (LA.R n)
    sampleR = do
                let n = intVal @n
                g ← asks gen 
                ~(Just xu) ← LA.create <$> G.replicateM n (MWC.uniformRM (-2,2) g)
                return xu
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
mmAssociativeT = (mm . (bimap mm id), mm . (bimap id mm) . assocR)

mmTT ∷ (KnownNat m, KnownNat n, 1 <= n) ⇒ Pair (M n m) (M n n)
mmTT = (emb . mmT, mm . (bimap id tr) . (id × id))

lerpSimplexIntervalT ∷ Pair (I 1, (Δ 1, Δ 1)) (ℝp 1) 
lerpSimplexIntervalT = (pr1 . osi @(ℝp 1, ℝp 1) . emb @(Δ 1) @(ℝp 2) . lerp, emb . lerp @(I 1) . bimap id (bimap iso iso))

cholInverseT ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Pair (Σp n) (Lo n)
cholInverseT = (mul . (cholInverse × chol), chol . basePoint . terminal)

standardGaussianT ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Pair (ℝ 1) (ℝp 1)
standardGaussianT = let Couple (Density p) _ = pull (real 0 × realp 1) gaussian
                        Couple (Density q) _ = standardGaussian
                        f                    = terminal × id
                     in (p . f, q . f)

valueAtPoint ∷ ∀ (x ∷ Type) (y ∷ Type) (n ∷ Nat) (m ∷ Nat). (Concrete n x, Concrete m y) ⇒ Mor x y → LA.R n → LA.R m
valueAtPoint φ p = getPoint $ φ . fromConcrete p

gradAtPoint ∷ ∀ (x ∷ Type) (y ∷ Type) (n ∷ Nat) (m ∷ Nat). (Concrete n x, Concrete m y) ⇒ Mor x y → LA.R n → LA.L m (Dim x)
gradAtPoint φ p = let Mor (J f) = toConcrete @m @y . φ
                      Mor (J g) = fromConcrete @n @x p
                      (p',_) = g undefined
                      (_, h) = f p'
                      e      = LA.eye @m
                      Just a = LA.create $ LA'.fromRows $ fmap (LA.extract . h) $ LA.toRows e
                   in a   

evalAtPoint ∷ ∀ (x ∷ Type) (y ∷ Type) (n ∷ Nat) (m ∷ Nat). (Concrete n x, Concrete m y) ⇒ Mor x y → LA.R n → (LA.R m, LA.L m (Dim x))
evalAtPoint φ p = (valueAtPoint φ p, gradAtPoint φ p)

getMatrix' ∷ ∀ m n (x ∷ Type). (KnownNat m, KnownNat n, x ⊂ M m n) ⇒ Point x → LA.L m n
getMatrix' p = let Mor (J f) = emb @x @(M m n) . p
                   (y, _)    = f undefined
                   Just z    = LA.create $ LA'.reshape (intVal @n) (LA.extract y)
                in z   

randomPoint ∷ ∀ x. Domain x ⇒ IO (Point x)
randomPoint = do
                gen ← MWC.createSystemRandom 
                Just xu ← LA.create <$> G.replicateM (intVal @(Dim x)) (MWC.uniformRM (-2,2) gen)
                return $ Mor $ point xu

tabularise ∷ ∀ x y. (Dim x ~ 1, Dim y ~ 1) ⇒ Double → Double → Int → Mor x y → [(Double, Double)]
tabularise lo hi n (Mor (J φ)) = let f ξ = pr1 . LA.headTail . pr1 . φ $ LA.konst ξ
                                     ξs  = [ lo + (hi - lo) * fromIntegral i / fromIntegral n| i ← [0..n]]
                                  in [ (ξ, f ξ) | ξ ← ξs ] 

