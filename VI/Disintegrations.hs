{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, FunctionalDependencies, RankNTypes, GeneralisedNewtypeDeriving, StandaloneDeriving #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Disintegrations ( -- * Disintegrations
                            Disintegration(..), mix', (◎)
                          , Couple(..)
                            -- * Disintegrations over domains
                            -- ** Main disintegrations: densities and samplers 
                          , Density(..), pseudoConditional, SampleM(..), executeSample, Sampler(..), push 
                            -- ** Reparameterisation of disintegratoins
                          , Reparam(..), pullReparam, Reparameterisable(..)
                            -- ** Gaussians 
                          , standardGaussian, translationReparam, GaussianCovariance, gaussian, genericGaussian 
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
import GHC.TypeNats

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

-- | A family of diffeomorphisms @y → z@ parameterised by @x@
data Reparam x y z where
    Reparam ∷ (Domain x, Domain y, Domain z) 
            ⇒ Mor (x, y) z      -- ^ forward
            → Mor (x, z) y      -- ^ backward
            → Mor (x, z) (ℝp 1) -- ^ Jacobian
            → Reparam x y z

instance Domain x ⇒ Cat Domain (Reparam x) where
    id = Reparam pr2 pr2 (realp 1)
    (Reparam f g jac) . (Reparam f' g' jac') = Reparam (f . (pr1 × f')) (g' . (pr1 × g)) (jac ◀ mul $ jac' . (pr1 × g))
    witness (Reparam _ _ _) a = a 

-- | Base change for a family of reparameterisations
pullReparam ∷ Mor t x → Reparam x y z → Reparam t y z
pullReparam φ (Reparam f g jac) = witness φ $ Reparam (f . bimap φ id) (g . bimap φ id) (jac . bimap φ id)

class Disintegration Domain Mor p ⇒ Reparameterisable p where
    reparam ∷ Reparam x y z → p x y → p x z

instance Reparameterisable Density where
    reparam (Reparam _ f jac) (Density p) = Density $ p . (pr1 × f) ◀ quo $ jac

instance Reparameterisable Sampler where
    reparam (Reparam f _ _) (Sampler s) = Sampler $ (\g → f . (id × g)) <$> s

instance (Reparameterisable p, Reparameterisable q) ⇒ Reparameterisable (Couple p q) where
    reparam φ (Couple p q) = Couple (reparam φ p) (reparam φ q)

translationReparam ∷ KnownNat n ⇒ Reparam (ℝ n) (ℝ n) (ℝ n)
translationReparam = Reparam add (add . bimap neg id) (realp 1)

-- | This class enables polymorphic covariance parameterisation for 'gaussian'
class (KnownNat n, Domain x) ⇒ GaussianCovariance n x | x → n where
    covarianceReparam ∷ Reparam x (ℝ n) (ℝ n)

instance (KnownNat n, 1 <= n) ⇒ GaussianCovariance n (Σp n) where
    covarianceReparam = Reparam (dot . bimap chol id) (dot . bimap cholInverse id) (cholDet . pr1)

instance KnownNat n ⇒ GaussianCovariance n (ℝp n) where
    covarianceReparam = Reparam (mul . bimap emb id) (mul . bimap (emb . invol) id) (Mor $ linear (LA.konst 1))

standardGaussian ∷ ∀ n. KnownNat n ⇒ Couple Density Sampler Pt (ℝ n)
standardGaussian = Couple (Density p) (Sampler s) where
                    z = (2*pi) ** (-0.5 * (fromIntegral $ natVal (Proxy ∷ Proxy n))) 
                    p = fromPoints2 $ \_ x → let e = exp' ▶ (real (-0.5) ◀ mul $ x ∙ x)
                                              in e ◀ quo $ realp z
                    s ∷ ∀ m. SampleM m ⇒ m (Mor Pt (ℝ n))
                    s = do
                           z ← sample $ \g → fromJust @(LA.R n) . LA.create <$> G.replicateM (intVal @n) (MWC.standard g) 
                           return $ Mor $ point z

-- | General multivariate normal
gaussian ∷ ∀ n cov. GaussianCovariance n cov ⇒ Couple Density Sampler (ℝ n, cov) (ℝ n)
gaussian = reparam φ μ where
              φ = pullReparam pr1 translationReparam . pullReparam pr2 covarianceReparam
              μ = pull @Domain @Mor terminal standardGaussian

-- | This is the default variational family, employing a multivariate normal in the canonical coordinates on a domain.
genericGaussian ∷ ∀ x n cov. (Domain x, n ~ Dim x, GaussianCovariance n cov) ⇒ Couple Density Sampler (x, cov) x
genericGaussian = case gaussian @n of
                     Couple (Density p) (Sampler s) → let p' = p . bimap (bimap f id) f
                                                          s' ∷ ∀ m. SampleM m ⇒ m (Mor (x, cov) x)  
                                                          s' = s >>= \φ → return (g . φ . bimap f id)
                                                       in Couple (Density p') (Sampler s')
                    where
                      f = Mor id ∷ Mor x (ℝ n)
                      g = Mor id ∷ Mor (ℝ n) x
                     
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

