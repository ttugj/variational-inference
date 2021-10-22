{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Domains ( -- * Cartesian category of domains

-- |
-- A domain is a space together with a chosen identification 
-- with R^n for some natural n; that is, a global coordinate.
--
-- Morphisms between domains are specified as 1-jets
-- of differentiable maps between corresponding R^n's.
-- Domains form a Cartesian category (see 'Cart'), with '(,)' as product,
-- equivalent to 'Jet'. The additional structure comes in the form of
-- distinguished embeddings (see '⊂') and a other structural maps. The purpose
-- is to serve as parameter domains as well as target spaces for families 
-- of probability distributions.
--
-- For reference, we exhibit basic domains as open subsets
-- of (possibly a subspace in) some R^m, and specify the
-- coordinate:
--
-- [@ℝ n@] All of R^n, with identity coordinate.
-- [@ℝp n@] Positive orthant of R^n, with elementwise logarithm coordinate.
-- [@I n@] Positive unit cube in R^n, with elementwise logit coordinate.
-- [@Δ n@] The n-simplex in R^{n+1}, with coordinate p -> log p - 1/(n+1) Σ log p mapping onto the hyperplane orthogonal to (1,...,1) in R^{n+1}.
-- [@M n m@] All n × m matrices, identified with R^{nm} with row-major order.
-- [@Σ n@] Symmetric n × n matrices, identified with R^{n(n+1)/2} using upper triangular part with row-major order.
-- [@Σp n@] Positive n × n matrices, identified with R^{n(n+1)/2} using upper triangular Cholesky factor, with row-major order and logarithm applied to diagonal elements.
--
                    Dim, Domain, Mor
                    -- * Basic domains
                  , ℝ, ℝp, I, Δ, M, Σ, Σp
                    -- * Basic operations
                  , type(⊂)(..), type(≌)(..)
                  , Add(..), Mul(..), ScaleP(..), Scale(..), Mix(..), Invol(..)
                  , simplexProjection
                    -- * test
                  , test, test'
                  ) where

import VI.Categories
import VI.Jets
import VI.Util

import Prelude                  (uncurry, ($))

import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Maybe
import Data.Functor
import Control.Applicative

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'

import GHC.Float 
import GHC.Real  
import GHC.Num   
import GHC.Classes

-- | Dimension of a domain
type family Dim (x ∷ k) ∷ Nat

type instance Dim (x,y) = (Dim x) + (Dim y)
type instance Dim '()   = 0

class    KnownNat (Dim x) ⇒ Domain x
instance KnownNat (Dim x) ⇒ Domain x

-- | Morphisms between domains
data Mor x y = Mor (Jet (Dim x) (Dim y))

instance Cat Domain Mor where
    id = Mor id
    Mor φ . Mor ψ = Mor (φ . ψ)

instance Cart Domain Mor where
    pr1 ∷ ∀ x y. (Domain x, Domain y, Domain (x,y)) ⇒ Mor (x,y) x
    pr1 = Mor pr1' 
    pr2 ∷ ∀ x y. (Domain x, Domain y, Domain (x,y)) ⇒ Mor (x,y) y
    pr2 = Mor pr2' 
    Mor φ × Mor ψ = Mor (φ ⊙ ψ)

data ℝ  (n ∷ Nat)
data ℝp (n ∷ Nat)
data I  (n ∷ Nat)
data Δ  (n ∷ Nat)
data M  (m ∷ Nat) (n ∷ Nat)
data Σ  (n ∷ Nat)
data Σp (n ∷ Nat)
data U  (n ∷ Nat)

type instance Dim (ℝ  n  ) = n
type instance Dim (ℝp n  ) = n
type instance Dim (I  n  ) = n
type instance Dim (Δ  n  ) = n
type instance Dim (M  m n) = m * n
type instance Dim (Σ  n  ) = (n * (1 + n)) `Div` 2
type instance Dim (Σp n  ) = (n * (1 + n)) `Div` 2
type instance Dim (U  n  ) = (n * (1 + n)) `Div` 2

-- | Canonical isomorphism
class (Domain x, Domain y, Dim x ~ Dim y) ⇒ x ≌ y where
    iso ∷ Mor x y
    osi ∷ Mor y x
    iso = Mor id
    osi = Mor id

instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (ℝ n, ℝ m)   ≌ ℝ  l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (ℝp n, ℝp m) ≌ ℝp l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (I n, I m)   ≌ I  l

-- | Canonical subdomain embedding
class (Domain x, Domain y) ⇒ x ⊂ y where
    emb ∷ Mor x y

instance Domain x ⇒ x ⊂ x where
    emb = id

instance {-# OVERLAPPABLE #-} (x ⊂ y, y ⊂ x, Dim x ~ Dim y) ⇒ x ≌ y where
    iso = emb
    osi = emb

instance (x ⊂ y, x' ⊂ y') ⇒ (x,x') ⊂ (y,y') where
    emb = bimap emb emb

instance KnownNat n ⇒ ℝp n ⊂ ℝ n where
    emb = Mor $ fromPoints exp

instance KnownNat n ⇒ I n ⊂ ℝp n where
    emb = Mor $ fromPoints $ \x → let y = exp x in y / (1 + y)

instance KnownNat n ⇒ Σ n ⊂ M n n where
    emb = let n = intVal @n in Mor . law . mkFin' $ uncurry (ixΣ n) <$> lixM n

instance KnownNat n ⇒ U n ⊂ M n n where
    emb = let n = intVal @n 
              ι ∷ Jet ((Dim (U n)) + 1) (Dim (M n n))
              ι = law . mkFin' $ fromMaybe ((n*(n+1)) `div` 2) . uncurry (ixU n) <$> lixM n 
           in Mor $ ι . (id ⊙ 0)

-- | Upper-triangular Cholesky factor
chol ∷ KnownNat n ⇒ Mor (Σp n) (U n)
chol = Mor . Jet $ cholU 

-- | Additive domains 
class Domain x ⇒ Add x where
    add ∷ Mor (x, x) x

-- | Multiplicative domains
class Domain x ⇒ Mul x where
    mul ∷ Mor (x, x) x

-- | Convex domains
class Domain x ⇒ Mix x where
    mix ∷ Mor (I 1, x, x) x

-- | Conical domains
class Domain x ⇒ ScaleP x where
    scalep ∷ Mor (ℝp 1, x) x

-- | Projective domains
class Domain x ⇒ Scale x where
    scale ∷ Mor (ℝ 1, x) x

-- | Involutive domains
class Domain x ⇒ Invol x where
    -- | by default, invol corresponds to negation in canonical coordinates
    invol ∷ Mor x x
    invol = Mor $ fromPoints negate

instance {-# OVERLAPPABLE #-} Scale x ⇒ ScaleP x where
    scalep = scale . bimap emb id

instance KnownNat n ⇒ Add (ℝ n) where
    add = Mor $ fromPoints2' (+)

instance KnownNat n ⇒ Add (ℝp n) where
    add = Mor $ fromPoints2' $ \x y → log (exp x + exp y)

instance KnownNat n ⇒ Mul (ℝ n) where
    mul = Mor $ fromPoints2' (*)

instance KnownNat n ⇒ Mul (ℝp n) where
    mul = Mor $ fromPoints2' (+)

instance KnownNat n ⇒ Mul (I n) where
    mul = Mor $ fromPoints2' $ \x y → x + y - log (1 + exp x + exp y)  

instance KnownNat n ⇒ ScaleP (ℝp n) where
    scalep = Mor $ fromPoints2' $ \c x → (expand ▶ c) + x
              
instance KnownNat n ⇒ Scale (ℝ n) where
    scale  = Mor $ fromPoints2' $ \c x → (expand ▶ c) * x

instance KnownNat n ⇒ Invol (ℝ  n) 
instance KnownNat n ⇒ Invol (ℝp n) 
instance KnownNat n ⇒ Invol (I  n) 

simplexProjection ∷ ∀ n. KnownNat n ⇒ Mor (ℝp (n + 1)) (Δ n) 
simplexProjection = Mor $ linear (LA.tr basisH)

instance (KnownNat n, KnownNat m, m ~ (n + 1)) ⇒ Δ n ⊂ ℝp m where
    emb = Mor $ fromPoints $ \x → let y = linear basisH ▶ x
                                      s = log (linear 1 ▶ exp y)
                                   in y - (expand ▶ s)

test ∷ KnownNat n ⇒ Mor (Δ n) (Δ n)
test = simplexProjection . emb

test' = let Mor (Jet f) = test @3
            g = pr1 . f
         in g . LA.fromList <$> [[0,1,2],[1,2,3],[2,3,4],[6,6,6]]

{-

-- |  
--mTm ∷ KnownNat n ⇒ Mor (M n n) (Σ n)

instance KnownNat n ⇒ Σp n ⊂ Σ n where
    -- we factor Σp n ⊂ Σ n through the space of upper-triangular matrices
 --   emb = mTm . emb . chol

-- instance Δ 1 ≌ I 1 where

{-
-}

{-
instance KnownNat n ⇒ Mix (ℝ  n) where
instance KnownNat n ⇒ Mix (ℝp n) where
instance KnownNat n ⇒ Mix (I  n) where
instance KnownNat n ⇒ Mix (Δ  n) where
-}

{-
instance (KnownNat m, KnownNat n) ⇒ Add (M m n)
instance KnownNat n ⇒ Add (Σ n)
instance KnownNat n ⇒ Add (Σp n)

instance KnownNat n ⇒ Mul (M n n)

instance (KnownNat m, KnownNat n) ⇒ Scale (M m n)
instance KnownNat n ⇒ Scale (Σ n)
instance KnownNat n ⇒ ScaleP (Σp n)

mTm' ∷ k >= n ⇒ M k n → Σp n
mmT' ∷ k >= n ⇒ M n k → Σp n
-}

-}

