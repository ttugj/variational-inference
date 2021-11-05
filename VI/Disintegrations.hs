{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, FunctionalDependencies, RankNTypes, GeneralisedNewtypeDeriving, StandaloneDeriving #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Disintegrations ( -- * Disintegrations
                            Disintegration(..), mix', (◎)
                          , Couple(..)
                            -- * Disintegrations over domains
                            -- ** General types
                          , Density(..), pseudoConditional, SampleM(..), executeSample, Sampler(..), push 
                            -- ** Particular instances 
                          , gaussian, genericGaussian 
                            -- * Divergence
                          , divergenceSample
                          ) where

import Prelude (($), undefined)

import VI.Categories
import VI.Jets
import VI.Domains

import Data.Kind
import Data.Proxy
import Data.Maybe
import GHC.TypeLits

import Data.Functor
import Control.Applicative
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.Reader
import System.Random.Stateful
import System.IO

import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWC
import qualified Data.Vector.Generic             as G
import qualified Numeric.LinearAlgebra.Static    as LA

import GHC.Float 
import GHC.Real  
import GHC.Num   
import GHC.Classes
import GHC.Types

-- | A minimal structure for building joint likelihoods
class Cart ob c ⇒ Disintegration ob c p where
    -- | Contravariant functoriality in first argument
    pull   ∷ c x y → p y z → p x z
    -- | Mixture (a weak composition)
    mix    ∷ p x y → p (x, y) z → p x (y, z)
    -- | Compatibility with monoidal structure: associativity (left)
    pushAL ∷ (ob x, ob y, ob z) ⇒ p t (x,(y,z)) → p t ((x,y),z)
    -- | Compatibility with monoidal structure: associativity (right)
    pushAR ∷ (ob x, ob y, ob z) ⇒ p t ((x,y),z) → p t (x,(y,z))
    -- | Compatibility with monoidal structure: symmetry 
    pushS  ∷ (ob x, ob y) ⇒ p t (x,y) → p t (y,x)

data Couple p p' x y = Couple (p x y) (p' x y)

instance (Disintegration ob c p, Disintegration ob c p') ⇒ Disintegration ob c (Couple p p') where
    pull f (Couple μ μ') = Couple (pull f μ) (pull f μ')
    mix (Couple μ μ') (Couple ν ν') = Couple (mix @ob @c μ ν) (mix @ob @c μ' ν')
    pushAL (Couple μ μ') = Couple (pushAL @ob @c μ) (pushAL @ob @c μ') 
    pushAR (Couple μ μ') = Couple (pushAR @ob @c μ) (pushAR @ob @c μ') 
    pushS  (Couple μ μ') = Couple (pushS  @ob @c μ) (pushS  @ob @c μ') 

mix' ∷ ∀ ob c p x y z. (Disintegration ob c p, ob x, ob y, ob z) ⇒ p x y → p y z → p x (y, z)
mix' μ ν = mix @ob @c μ (pull @ob @c pr2 ν)

(◎) ∷ ∀ ob c p x y z. (Disintegration ob c p, ob x, ob y, ob z) ⇒ p x y → p x z → p x (y, z)
μ ◎ ν = mix @ob @c μ (pull @ob @c pr1 ν)

-- | A family of probability densities (with respect to Lebesgue measure induced by the canonical coordinate)
data Density x y where
    Density ∷ (Domain x, Domain y) ⇒ Mor (x, y) (ℝp 1) → Density x y

class Monad m ⇒ SampleM m where
    sample ∷ (∀ g m'. StatefulGen g m' ⇒ g → m' a) → m a

newtype SampleT m a = SampleT { runSampleT ∷ ReaderT (MWC.Gen (PrimState m)) m a } deriving (Functor, Applicative, Monad)

instance PrimMonad m ⇒ SampleM (SampleT m) where
    sample α = SampleT $ ask >>= α 

executeSample ∷ ∀ a. (∀ m. SampleM m ⇒ m a) → IO a
executeSample α = MWC.createSystemRandom >>= runReaderT (runSampleT (α ∷ SampleT IO a))

-- | A reparameterisable sampler (with differentiable samples)
data Sampler x y where
    Sampler ∷ (Domain x, Domain y) ⇒ (∀ m. SampleM m ⇒ m (Mor x y)) → Sampler x y 

instance Disintegration Domain Mor Density where
    pull f (Density p) = witness f $ Density $ p . bimap f id
    mix (Density p) (Density q) = Density $ fromPoints3 $ \x y z → (p ▶ x × y) ◀ mul $ q ▶ x × y × z
    pushAL (Density p) = Density $ p . bimap id assocR
    pushAR (Density p) = Density $ p . bimap id assocL
    pushS  (Density p) = Density $ p . bimap id swap

instance Disintegration Domain Mor Sampler where
    pull f (Sampler s) = witness f $ Sampler $ (. f) <$> s
    mix (Sampler s) (Sampler t) = Sampler $ do
                                    φ ← s
                                    ψ ← t
                                    return $ fromPoints $ \x → let y = φ ▶ x in y × (ψ ▶ (x × y))
    pushAL (Sampler s) = Sampler $ (assocL .) <$> s
    pushAR (Sampler s) = Sampler $ (assocR .) <$> s
    pushS  (Sampler s) = Sampler $ (swap   .) <$> s

pseudoConditional ∷ (Domain y, Domain z) ⇒ Density x (y, z) → Density (x, y) z
pseudoConditional (Density p) = Density $ p . assocR

push ∷ ∀ x y z. Mor y z → Sampler x y → Sampler x z
push f (Sampler s) = witness f $ Sampler $ (f .) <$> s

-- | General multivariate normal
gaussian ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Couple Density Sampler (ℝ n, Σp n) (ℝ n)
gaussian = Couple (Density p) (Sampler s) where
            {-
                z ~ N(0, I); φ(z) = (2π)^(-n/2) exp(-|z|²/2)
                x = x₀ + L z ~ N(x₀, LL*)
                log p(x) = log φ(L⁻¹(x-x₀)) - log det L
            -}
            -- normalising factor
            z = (2*pi) ** (-0.5 * (fromInteger $ natVal (Proxy ∷ Proxy n))) 
            -- standard normal pdf
            φ = fromPoints $ \x → let e = exp' ▶ (real (-0.5) ◀ mul $ x ∙ x)
                                   in e ◀ quo $ realp z
            -- transformed pdf
            p = fromPoints2 $ \par x → let loc = pr1 ▶ par
                                           cov = pr2 ▶ par
                                           z   = (cholInverse ▶ cov) ∙ (x ◀ sub $ loc)
                                        in (φ ▶ z) ◀ quo $ cholDet ▶ cov
            -- sampler
            s ∷ ∀ m. SampleM m ⇒ m (Mor (ℝ n, Σp n) (ℝ n))
            s = do
                   z ← sample $ \g → fromJust @(LA.R n) . LA.create <$> G.replicateM (intVal @n) (MWC.standard g) 
                   return $ fromPoints2 $ \loc cov → ((chol ▶ cov) ∙ (fromConcrete @n @(ℝ n) z . terminal)) ◀ add $ loc 

-- | This is the default variational family, employing a multivariate normal in the canonical coordinates on a domain.
genericGaussian ∷ ∀ x n. (Domain x, n ~ Dim x, 1 <= n) ⇒ Couple Density Sampler (x, Σp n) x
genericGaussian = case gaussian @n of
                     Couple (Density p) (Sampler s) → let p' = p . bimap (bimap f id) f
                                                          s' ∷ ∀ m. SampleM m ⇒ m (Mor (x, Σp n) x)  
                                                          s' = s >>= \φ → return (g . φ . bimap f id)
                                                       in Couple (Density p') (Sampler s')
                    where
                      f = (Mor id) ∷ Mor x (ℝ n)
                      g = (Mor id) ∷ Mor (ℝ n) x
                     

divergenceSample ∷ SampleM m ⇒ Couple Density Sampler t x → Density s x → m (Mor (t,s) (ℝ 1))
divergenceSample (Couple (Density q) (Sampler s)) (Density p) = go <$> s where
                                                                     -- q ∷ Mor (t,x) (ℝp 1) 
                                                                     -- p ∷ Mor (s,x) (ℝp 1) 
                                                                     -- φ ∷ Mor t x 
                                                                     go φ = fromPoints2 $ \θ σ → let ξ = φ ▶ θ
                                                                                                     π = σ ◀ p $ ξ
                                                                                                     ρ = θ ◀ q $ ξ
                                                                                                     d = ρ ◀ quo $ π
                                                                                                  in log' ▶ d 

