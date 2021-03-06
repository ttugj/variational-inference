{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, FunctionalDependencies, RankNTypes, GeneralisedNewtypeDeriving, StandaloneDeriving #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Quasiarrows ( -- * Quasiarrows

-- |
-- A quasiarrow on a Cartesian category \(C\) is
-- a map \( p : Ob(C) \times Ob(C)\to Set \), with \(p(x, y)\) interpreted 
-- as the set of families of probability distributions over @y@
-- parameterised by @x@, together with 
--
--  * base-change maps extending \( p(-, y) \) to a presheaf on \( C\),
--  * mixture maps \(p(x, y) \times p(x \times y, z) \to p(x ,y\times z)\)
--
-- satisfying suitable compatibility conditions with respect
-- to each other and the Cartesian structure. In particular,
-- mixture maps are associative, in the sense that the two
-- possible composites 
-- \[ p (x, y) \times p (x \times y, z) \times p (x \times y \times z, w) \to  p( x, y \times z \times w ) \] 
-- coincide.
--
-- Note that we do not model marginals (these would turn a quasiarrow
-- into a profunctor) and Dirac delta distributions (these would lift
-- morphisms into quasiarrows). Mixture maps provide just enough structure
-- to construct joint distributions over probabilistic programs.
                            Quasiarrow(..), mix', mix''
-- |
-- One may view quasiarrows over a fixed Cartesian category
-- as objects of a symmetric monoidal category. While we won't 
-- model quasiarrow morphisms, the monoidal structure is 
-- expressed by 'Trivial' and 'Couple': 
                          , Trivial(..), Couple(..)

                            -- * Quasiarrows over domains

                            -- ** Main quasiarrows
-- |
-- We consider two fundamental quasiarrows over domains:
--
--  * 'Density', expressing probability distributions in terms of densities  
--    with respect to the underlying volume measure induced by the
--    domain's identification with a Euclidean space;
--  * 'Sampler', expressing (families of) probability distributions by providing
--    (pramaterised) samplers.
--
-- The two representations have somewhat dual features: 'Sampler' admits marginals
-- via 'push', becoming a profunctor over the category of domains, while 'Density'
-- admits un-normalised conditionals via 'pseudoConditional'. 
--
-- For 'pseudoConditional' to
-- make sense, we need to allow families of un-normalised densities in @'Density' x y@. Still,
-- the normalisation constant is required to be actually constant within the family, so that
-- proper elements of @'Density' x y@ are morphisms
--  \(f : x \times y \to (0,\infty)\) of domains
-- such that the map \( x\ni\xi \mapsto \int f(\xi,\eta) d\eta \in [0,\infty] \) does not depend on \(\xi\). 
--
-- @'Sampler' x y@ produces a family of samples in @y@ parameterised by @x@, i.e. a morphism \(x \to y\), given 
-- access to some 'StatefulGen' in a suitable monad. This is implemented in terms of the class 'SampleM' of monads @m@
-- that can interpret computations of the form @??? g m'. StatefulGen g m' ??? g ??? m' a@ into @m a@.
-- Sampling computations should be composed in the context @??? m. 'SampleM' m@, and only finally
-- executed using 'executeSampleIO' (this creates a random generator in @'IO'@).
--
                          , (???)
                          , Density(..), pseudoConditional
                          , SampleM(..), executeSampleIO, Sampler(..), push 
                            -- ** Reparameterisation of disintegratoins
-- |
-- 'Reparameterisable' quasiarrows admit pushforwards along domain diffeomorphisms,
-- represented as a pair of mutually inverse morphisms together with a Jacobian. More
-- precisely, the 'Reparam' type encodes a family of diffeomorphisms between a pair of
-- domains, parameterised by a third domain. Upon fixing the latter, 'Reparam' becomes
-- a 'Cat'egory (and even a groupoid, i.e. 'Gpd').
--
-- Both 'Density' and 'Sampler' are 'Reparameterisable'.
-- This allows us for example to define the faimly of multivariate normal distributions in terms
-- of a standard one, transformed by an affine map with upper-triangular linear part.
--
-- We also use 'Reparameterisable' to implement some tautological isomorphisms: domains @x@, @y@
-- satisfying @x ??? y@ are canonically isomorphic via identity on underlying Euclidean spaces, and
-- distributions can be pushed from @x@ to @y@ using 'pushIso'/'pushOsi'.
                          , Reparam(..), pullReparam, Reparameterisable(..)
                          , type(???)(..), pushIso, pushOsi
                            -- ** Gaussians 
-- |
-- Gaussian, i.e. multivariate normal, distributions are provided in several flavours:
--
-- * 'standardGaussian' is the unique normal distribution on R^n with mean zero and identity covariance matrix,
-- * 'gaussian' is the complete family of (non-degenerate) multivariate normal distributions on R^n, parameterised
--   by mean and covariance,
-- * 'genericGaussian' defines a family of distributions on any n-dimensional domain, using its canonical identification 
--    with R^n.
--
-- Covariance may be parameterised either by the full covariance matrix (corresponding to the domain @'??p' n@), or
-- by its diagonal (corresponding to the domain @'Rp' n@). This is enabled by the 'GaussianCovariance' class. More 
-- concretely, 'gaussian' is defined starting with 'standardGaussian', pushing forward by 'covarianceReparam'
-- provided by a 'GaussianCovariance' instance (to adjust covariance), and by 'translationReparam' (to adjust mean).
                          , standardGaussian, translationReparam, GaussianCovariance(..), gaussian, genericGaussian, stdToPrecision 
                            -- ** Common densities
                          , gaussianD, gammaD
                            -- * Divergence
-- |
-- At the core of variational inference is the Kullback-Leibler divergence between a pair of
-- probability distributions, as a differentiable function of their parameters. In all but simplest cases
-- this divergence is estimated by averaging (differentiable) samples. This is implemented by 'divergenceSample',
-- taking a pair ??, ??  of probability measures and computing the logarithm of their Radon-Nikodym derivative at a point sampled from ??.
-- Accordingly, ?? is represented by a @'Couple' 'Density' 'Sampler'@, and ?? by @'Density'@. Averaging such samples produces
-- an estimate of the KL divergence
-- \[ D_{KL}(??\|??) = E_{\mu} \log \frac{d\mu}{d\nu}. \]
-- In practice, ?? will be the posterior distribution, and ?? the variational family; 'divergenceSample' is then
-- used to perform stochastic gradient descent on \(D_{KL}(??\|??)\). The 'Density' representations of ?? and ?? need not be
-- normalised: a global normalisation factor does not affect the gradient. In particular, ?? may be obtained as a
-- 'pseudoConditional' of a joint prior distribution with respect to observed data.
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
import Control.Monad.IO.Class
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
import GHC.Err (undefined)

-- | A minimal structure for building joint likelihoods
class Cart ob c ??? Quasiarrow ob c p where
    -- | Contravariant functoriality in first argument
    pull   ??? c x y ??? p y z ??? p x z
    -- | Mixture (a weak composition)
    mix    ??? p x y ??? p (x, y) z ??? p x (y, z)
    -- | Covariant functoriality for canonical Cartesian isomorphisms
    pushB  ??? Braid ob x y ??? p t x ??? p t y

data Trivial x y = Trivial

instance Cart ob c ??? Quasiarrow ob c Trivial where
    pull _ Trivial = Trivial
    mix Trivial Trivial = Trivial
    pushB _ Trivial = Trivial

data Couple p p' x y = Couple (p x y) (p' x y)

instance (Quasiarrow ob c p, Quasiarrow ob c p') ??? Quasiarrow ob c (Couple p p') where
    pull f (Couple ?? ??') = Couple (pull f ??) (pull f ??')
    mix (Couple ?? ??') (Couple ?? ??') = Couple (mix @ob @c ?? ??) (mix @ob @c ??' ??')
    pushB ?? (Couple ?? ??') = Couple (pushB @ob @c ?? ??) (pushB  @ob @c ?? ??') 

mix' ??? ??? ob c p x y z. (Quasiarrow ob c p, ob x, ob y, ob z) ??? p x y ??? p y z ??? p x (y, z)
mix' ?? ?? = mix @ob @c ?? (pull @ob @c pr2 ??)


mix'' ??? ??? ob c p x y z. (Quasiarrow ob c p, ob x, ob y, ob z) ??? p x y ??? p x z ??? p x (y, z)
mix'' ?? ??  = mix @ob @c ?? (pull @ob @c pr1 ??)

-- | Specialisation of 'mix''' 
(???) ??? ??? p x y z. (Quasiarrow Domain Mor p, Domain x, Domain y, Domain z) ??? p x y ??? p x z ??? p x (y, z)
(???) = mix'' @Domain @Mor @p @x @y @z 

-- | A family of probability densities (with respect to Lebesgue measure induced by the canonical coordinate)
data Density x y where
    Density ??? (Domain x, Domain y) ??? Mor (x, y) (???p 1) ??? Density x y

class Monad m ??? SampleM m where
    sample ??? (??? g m'. StatefulGen g m' ??? g ??? m' a) ??? m a

newtype SampleT m a = SampleT { runSampleT ??? ReaderT (MWC.Gen (PrimState m)) m a } deriving (Functor, Applicative, Monad)

instance PrimMonad m ??? SampleM (SampleT m) where
    sample ?? = SampleT $ ask >>= ?? 

instance MonadIO m ??? MonadIO (SampleT m) where
    liftIO ?? = SampleT $ liftIO ??

executeSampleIO ??? ??? a. (??? m. (SampleM m, MonadIO m) ??? m a) ??? IO a
executeSampleIO ?? = MWC.createSystemRandom >>= runReaderT (runSampleT (?? ??? SampleT IO a)) 

-- | A reparameterisable sampler (with differentiable samples)
data Sampler x y where
    Sampler ??? (Domain x, Domain y) ??? (??? m. SampleM m ??? m (Mor x y)) ??? Sampler x y 

instance Quasiarrow Domain Mor Density where
    pull f (Density p) = witness f $ Density $ p . bimap f id
    mix (Density p) (Density q) = Density $ fromPoints3 $ \x y z ??? (p ??? x ?? y) ??? mul $ q ??? x ?? y ?? z
    pushB ?? (Density p) = witness ?? $ Density $ p . bimap id (braid $ inv ??)

instance Quasiarrow Domain Mor Sampler where
    pull f (Sampler s) = witness f $ Sampler $ (. f) <$> s
    mix (Sampler s) (Sampler t) = Sampler $ do
                                    ?? ??? s
                                    ?? ??? t
                                    return $ fromPoints $ \x ??? let y = ?? ??? x in y ?? (?? ??? (x ?? y))
    pushB ?? (Sampler s) = witness ?? $ Sampler $ (braid ?? .) <$> s

pseudoConditional ??? (Domain y, Domain z) ??? Density x (y, z) ??? Density (x, y) z
pseudoConditional (Density p) = Density $ p . assocR

push ??? ??? x y z. Mor y z ??? Sampler x y ??? Sampler x z
push f (Sampler s) = witness f $ Sampler $ (f .) <$> s

-- | A family of diffeomorphisms @y ??? z@ parameterised by @x@
data Reparam x y z where
    Reparam ??? (Domain x, Domain y, Domain z) 
            ??? Mor (x, y) z      -- ^ forward
            ??? Mor (x, z) y      -- ^ backward
            ??? Mor (x, z) (???p 1) -- ^ Jacobian
            ??? Reparam x y z

instance Domain x ??? Cat Domain (Reparam x) where
    id = Reparam pr2 pr2 (realp 1)
    (Reparam f g jac) . (Reparam f' g' jac') = Reparam (f . (pr1 ?? f')) (g' . (pr1 ?? g)) (jac ??? mul $ jac' . (pr1 ?? g))
    witness (Reparam _ _ _) a = a 

instance Domain x ??? Gpd Domain (Reparam x) where
    inv (Reparam f g jac) = Reparam g f (rcp . jac . (pr1 ?? f))

-- | Base change for a family of reparameterisations
pullReparam ??? Mor t x ??? Reparam x y z ??? Reparam t y z
pullReparam ?? (Reparam f g jac) = witness ?? $ Reparam (f . bimap ?? id) (g . bimap ?? id) (jac . bimap ?? id)

-- | A relation for tautologically isomorphic domains (i.e. via identity on underlying Euclidean spaces)
class x ??? y ??? x ??? y where
    canonicalIso ??? ??? t. Domain t ??? Reparam t x y
    canonicalIso = pullReparam terminal $ Reparam @() (Mor id) (Mor id) (realp 1)

instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ??? (??? n, ??? m)   ??? ???  l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ??? (???p n, ???p m) ??? ???p l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ??? (I n, I m)   ??? I  l

instance Domain x ??? ((), x) ??? x
instance Domain x ??? (x, ()) ??? x
instance (Domain x, Domain y, Domain z) ??? (x, (y, z)) ??? ((x, y), z)

class Quasiarrow Domain Mor p ??? Reparameterisable p where
    reparam ??? Reparam x y z ??? p x y ??? p x z

instance Reparameterisable Density where
    reparam (Reparam _ f jac) (Density p) = Density $ p . (pr1 ?? f) ??? quo $ jac

instance Reparameterisable Sampler where
    reparam (Reparam f _ _) (Sampler s) = Sampler $ (\g ??? f . (id ?? g)) <$> s

instance Reparameterisable Trivial where
    reparam _ Trivial = Trivial

instance (Reparameterisable p, Reparameterisable q) ??? Reparameterisable (Couple p q) where
    reparam ?? (Couple p q) = Couple (reparam ?? p) (reparam ?? q)

pushIso ??? (Domain t, x ??? y, Reparameterisable p) ??? p t x ??? p t y
pushIso = reparam canonicalIso
pushOsi ??? (Domain t, x ??? y, Reparameterisable p) ??? p t y ??? p t x
pushOsi = reparam (inv canonicalIso)

translationReparam ??? KnownNat n ??? Reparam (??? n) (??? n) (??? n)
translationReparam = Reparam add (add . bimap neg id) (realp 1)

-- | This class enables polymorphic covariance parameterisation for 'gaussian'
class (KnownNat n, Domain x) ??? GaussianCovariance n x | x ??? n where
    covarianceReparam ??? Reparam x (??? n) (??? n)

instance (KnownNat n, 1 <= n) ??? GaussianCovariance n (??p n) where
    covarianceReparam = Reparam (dot . bimap chol id) (dot . bimap cholInverse id) (cholDet . pr1)

instance KnownNat n ??? GaussianCovariance n (???p n) where
    covarianceReparam = Reparam (mul . bimap emb id) (mul . bimap (emb . invol) id) (prodP . pr1)

-- | This is useful for converting between stdev and precision
-- parameterisation (forward takes \(\sigma\) to  \(\sigma^{-2}\)).
stdToPrecision ??? ??? t n. (Domain t, KnownNat n) ??? Reparam t (???p n) (???p n) 
stdToPrecision = Reparam (Mor (fromPoints $ \s ??? (-2) * s) . pr2)
                         (Mor (fromPoints $ \s ??? (-0.5) * s) . pr2)
                         (realp 2) 

standardGaussian ??? ??? n. KnownNat n ??? Couple Density Sampler () (??? n)
standardGaussian = Couple (Density p) (Sampler s) where
                    z = (2*pi) ** (0.5 * (fromIntegral $ natVal (Proxy ??? Proxy n))) 
                    p = fromPoints2 $ \_ x ??? let e = exp' ??? (real (-0.5) ??? mul $ x ??? x)
                                              in e ??? quo $ realp z
                    s ??? ??? m. SampleM m ??? m (Point (??? n))
                    s = do
                           z ??? sample $ \g ??? fromJust @(LA.R n) . LA.create <$> G.replicateM (intVal @n) (MWC.standard g) 
                           return $ Mor $ point z

-- | General multivariate normal
gaussian ??? ??? n cov. GaussianCovariance n cov ??? Couple Density Sampler (??? n, cov) (??? n)
gaussian = reparam ?? ?? where
              ?? = pullReparam pr1 translationReparam . pullReparam pr2 covarianceReparam
              ?? = pull @Domain @Mor terminal standardGaussian

-- | The 'Density' component of 'gaussian'
gaussianD ??? ??? n cov. GaussianCovariance n cov ??? Density (??? n, cov) (??? n)
gaussianD = let Couple ?? _ = gaussian in ??

-- | This is the default variational family, employing a multivariate normal in the canonical coordinates on a domain.
genericGaussian ??? ??? x n cov. (Domain x, n ~ Dim x, GaussianCovariance n cov) ??? Couple Density Sampler (x, cov) x
genericGaussian = case gaussian @n of
                     Couple (Density p) (Sampler s) ??? let p' = p . bimap (bimap f id) f
                                                          s' ??? ??? m. SampleM m ??? m (Mor (x, cov) x)  
                                                          s' = s >>= \?? ??? return (g . ?? . bimap f id)
                                                       in Couple (Density p') (Sampler s')
                    where
                      f = Mor id ??? Mor x (??? n)
                      g = Mor id ??? Mor (??? n) x

-- | Gamma distribution
gammaD ??? ??? n. KnownNat n ??? Density (???p n, ???p n) (???p n)
gammaD = Density $ fromPoints2 $ \ab x ??? let a = pr1 . ab
                                             b = pr2 . ab
                                             a'= emb . a ??? sub $ real 1 
                                             expTerm = exp' . neg . emb . (b ??? mul $ x)   -- exp(-bx)
                                             powTerm = exp' . (a' ??? mul $ log' . x)       -- x^{a-1}
                                             btoa    = exp' . (emb . a ??? mul $ log' . b)  -- b^a
                                             coef    = btoa ??? quo $ gamma . a             -- b^a / ??(a)
                                          in prodP . (coef ??? mul $ powTerm ??? mul $ expTerm)

divergenceSample ??? SampleM m ??? Couple Density Sampler t x ??? Density s x ??? m (Mor (t,s) (??? 1))
divergenceSample (Couple (Density q) (Sampler s)) (Density p) = go <$> s where
                                                                     -- q ??? Mor (t,x) (???p 1) 
                                                                     -- p ??? Mor (s,x) (???p 1) 
                                                                     -- ?? ??? Mor t x 
                                                                     go ?? = fromPoints2 $ \?? ?? ??? let ?? = ?? ??? ??
                                                                                                     ?? = ?? ??? p $ ??
                                                                                                     ?? = ?? ??? q $ ??
                                                                                                     d = ?? ??? quo $ ??
                                                                                                  in log' ??? d 


