{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, FunctionalDependencies, RankNTypes #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Disintegrations ( -- * Disintegrations
                            Disintegration(..), mix', (◎)
                          , Couple(..)
                            -- * Disintegrations over domains
                            -- ** general
                          , Density(..), pseudoConditional, Sampler(..), push 
                            -- ** particular
                          , gaussian 
                            -- * Divergence
                          , divergenceSample
                          ) where

import Prelude (($), undefined)

import VI.Categories
import VI.Jets
import VI.Domains

import Data.Kind
import Data.Maybe
import GHC.TypeLits

import Data.Functor
import Control.Applicative
import Control.Monad
import System.Random.Stateful
import System.Random.MWC.Distributions

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
    sample ∷ (∀ g. StatefulGen g m ⇒ g → m a) → m a

-- | A reparameterisable sampler (with differentiable samples)
data Sampler x y where
    Sampler ∷ (Domain x, Domain y) ⇒ (∀ m. SampleM m ⇒ m (Mor x y)) → Sampler x y 

instance Disintegration Domain Mor Density where
    pull f (Density p) = witness f $ Density $ p . bimap f id
    mix (Density p) (Density q) = Density $ fromPoints3 $ \x y z → (p ▶ x × y) ◀ mul $ (q ▶ x × y × z)
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

push ∷ ∀ (x ∷ Type) (y ∷ Type) (z ∷ Type). Mor y z → Sampler x y → Sampler x z
push f (Sampler s) = witness f $ Sampler $ (f .) <$> s

{-

    x ~ N(0, I)
    z = x₀ + L x ~ N(x₀, LL*)   ⇒ Σ = LL* 
    
    log p~(z) = log p(L⁻¹(z-x₀)) - log det L

-}

-- | General multivariate normal
gaussian ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Couple Density Sampler (ℝ n, Σp n) (ℝ n)
gaussian = Couple (Density p) (Sampler s) where
            p = undefined
            s = undefined

divergenceSample ∷ SampleM m ⇒ Couple Density Sampler t x → Density s x → m (Mor (t,s) (ℝ 1))
divergenceSample (Couple (Density q) (Sampler s)) (Density p) = go <$> s where
                                                                     -- q ∷ Mor (t,x) (ℝp 1) 
                                                                     -- p ∷ Mor (s,x) (ℝp 1) 
                                                                     -- φ ∷ Mor t x 
                                                                     go φ = fromPoints2 $ \θ σ → let ξ = φ ▶ θ
                                                                                                     π = σ ◀ p $ ξ
                                                                                                     ρ = θ ◀ q $ ξ
                                                                                                     d = ρ ◀ quo $ π
                                                                                                  in logD ▶ d 
