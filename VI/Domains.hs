{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Domains ( -- * Cartesian category of domains

-- |
-- A domain is a space together with a canonical
-- identification with R^n for some natural n; that is,
-- a global coordinate.
--
-- Morphisms between domains are specified as 1-jets
-- of differentiable maps between corresponding R^n's.
-- Domains form a Cartesian category (see 'Cart'), with '(,)' as product.
--
-- For reference, we exhibit basic domains as open subsets
-- of (possibly a subspace in) some R^m, and specify the
-- coordinate:
--
-- [@ℝ n@] All of R^n, with identity coordinate.
-- [@ℝp n@] Positive orthant of R^n, with elementwise logarithm coordinate.
-- [@I n@] Positive unit cube in R^n, with elementwise logit coordinate.
-- [@Δ n@] The n-simplex in R^{n+1}, TODO.
-- [@M n m@] All n × m matrices, identified with R^{nm} with row-major order.
-- [@Σ n@] Symmetric n × n matrices, identified with R^{n(n+1)/2} using upper triangular part with row-major order.
-- [@Σp n@] Positive n × n matrices, identified with R^{n(n+1)/2} using upper triangular Cholesky factor, with row-major order and logarithm applied to diagonal elements.
--
                    Dim, Domain
                  , Ob, Mor
                  , fromLinear, fromAffine
                    -- * Basic domains
                  , ℝ, ℝp, I, {- Δ, -} M, Σ, Σp
                    -- * Basic operations
                  , type(⊂)(..), type(≌)(..), Add(..), Mul(..), ScaleP(..), Scale(..), Mix(..), Invol(..)
                  ) where

import VI.Categories
import VI.Util

import Prelude                  (uncurry, ($))

import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Functor
import Control.Applicative

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'
import qualified GHC.Float as F
import qualified GHC.Real  as F
import qualified GHC.Num   as F


-- | Dimension of a domain
type family Dim (x ∷ k) ∷ Nat

type instance Dim (x,y) = (Dim x) + (Dim y)
type instance Dim '()   = 0

type Domain d x = (KnownNat d, d ~ Dim x)

-- | @Ob x@ is equivalent to @∃ d. Domain d x@
class    KnownNat (Dim x) ⇒ Ob x
instance KnownNat (Dim x) ⇒ Ob x


-- | Morphisms between domains
data Mor x y where
    Mor ∷ (Domain n x, Domain m y) ⇒ (LA.R n → (LA.R m, LA.L m n)) → Mor x y

instance Cat Ob Mor where
    id = Mor $ \x → (x, LA.eye)
    Mor φ . Mor ψ = Mor $ \x → let (y, dψ) = ψ x
                                   (z, dφ) = φ y
                                in (z, dφ LA.<> dψ)

instance Cart Ob Mor where
    pr1 ∷ ∀ x y. (Ob x, Ob y, Ob (x,y)) ⇒ Mor (x,y) x
    pr1 = Mor $ \x → (pr1 $ LA.split @(Dim x) x, LA.eye LA.||| 0)
    pr2 ∷ ∀ x y. (Ob x, Ob y, Ob (x,y)) ⇒ Mor (x,y) y
    pr2 = Mor $ \x → (pr2 $ LA.split @(Dim x) x, 0 LA.||| LA.eye)
    Mor φ × Mor ψ = Mor $ \x → let (y, dφ) = φ x
                                   (z, dψ) = ψ x
                                in (y LA.# z, dφ LA.=== dψ)

-- | A morphism represented as a linear map in canonical coordinates
fromLinear ∷ (Domain n x, Domain m y) ⇒ LA.L m n → Mor x y
fromLinear a = Mor $ \x → (a LA.#> x, a)

-- | A morphism represented as an affine map in canonical coordinates
fromAffine ∷ (Domain n x, Domain m y) ⇒ LA.R m → LA.L m n → Mor x y
fromAffine y a = Mor $ \x → (y F.+ a LA.#> x, a)


-- | Unconstrained real vectors, coordinate: @id@
data ℝ  (n ∷ Nat)
-- | Positive orthant in @ℝ n@, coordinate: @log x@
data ℝp (n ∷ Nat)
-- | [0,1]^n, coordinate: @log x/(1-x)@
data I  (n ∷ Nat)

{-
-- | standard simplex in @ℝ (n+1)@ (TODO)
data Δ  (n ∷ Nat)
-}

-- | Unconstrained real matrices
data M  (m ∷ Nat) (n ∷ Nat)
-- | Symmetric real matrices
data Σ  (n ∷ Nat)
-- | Positive real matrices
data Σp (n ∷ Nat)
-- | Upper-triangular real matrices
data U  (n ∷ Nat)

type instance Dim (ℝ  n  ) = n
type instance Dim (ℝp n  ) = n
type instance Dim (I  n  ) = n
-- type instance Dim (Δ  n  ) = n
type instance Dim (M  m n) = m * n
type instance Dim (Σ  n  ) = (n * (1 + n)) `Div` 2
type instance Dim (Σp n  ) = (n * (1 + n)) `Div` 2
type instance Dim (U  n  ) = (n * (1 + n)) `Div` 2

-- | Canonical isomorphism
class (Ob x, Ob y, Dim x ~ Dim y) ⇒ x ≌ y where
    iso ∷ Mor x y
    osi ∷ Mor y x
    iso = Mor $ \x → (x, LA.eye)
    osi = Mor $ \x → (x, LA.eye)

instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (ℝ n, ℝ m)   ≌ ℝ  l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (ℝp n, ℝp m) ≌ ℝp l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (I n, I m)   ≌ I  l

-- | Canonical subdomain embedding 
class (Ob x, Ob y) ⇒ x ⊂ y where
    emb ∷ Mor x y

instance Ob x ⇒ x ⊂ x where
    emb = id

instance {-# OVERLAPPABLE #-} (x ⊂ y, y ⊂ x, Dim x ~ Dim y) ⇒ x ≌ y where
    iso = emb
    osi = emb

instance (x ⊂ y, x' ⊂ y') ⇒ (x,x') ⊂ (y,y') where
    emb = bimap emb emb

instance KnownNat n ⇒ ℝp n ⊂ ℝ n where
    emb = Mor $ \x → let y = F.exp x in (y, LA.diag y)

instance KnownNat n ⇒ I n ⊂ ℝp n where
    emb = Mor $ \x → let y = F.exp x
                         z = y F./ (1 F.+ y)
                      in (F.log z, LA.diag $ 1 F.- z)

-- instance (KnownNat n, KnownNat n', n' ~ n + 1) ⇒ Δ n ⊂ I n' where

instance KnownNat n ⇒ Σ n ⊂ M n n where
    emb = fromLinear (embΣM @n)

instance KnownNat n ⇒ U n ⊂ M n n where
    emb = fromLinear (embUM @n)    

-- | Upper-triangular Cholesky factor
chol ∷ KnownNat n ⇒ Mor (Σp n) (U n)
chol = Mor cholU 
       

-- |  
mTm ∷ KnownNat n ⇒ Mor (M n n) (Σ n)
mTm = Mor $ \x → _ -- TODO

instance KnownNat n ⇒ Σp n ⊂ Σ n where
    -- we factor Σp n ⊂ Σ n through the space of upper-triangular matrices
    emb = mTm . emb . chol

-- instance Δ 1 ≌ I 1 where

{-
simplexProjection ∷ Mor (ℝp n) (Δ n) 
-}


-- | Additive domains 
class Add x where
    add ∷ Mor (x, x) x

-- | Multiplicative domains
class Mul x where
    mul ∷ Mor (x, x) x

-- | Convex domains
class Mix x where
    mix ∷ Mor (I 1, x, x) x

-- | Conical domains
class ScaleP x where
    scalep ∷ Mor (ℝp 1, x) x

-- | Projective domains
class Scale x where
    scale ∷ Mor (ℝ 1, x) x

-- | Involutive domains
class Invol x where
    -- | by default, invol corresponds to negation in canonical coordinates
    invol ∷ Mor x x
    default invol ∷ Ob x ⇒ Mor x x
    invol = Mor $ \x → (F.negate x, LA.diag (-1))

instance {-# OVERLAPPABLE #-} (Scale x, Ob x) ⇒ ScaleP x where
    scalep = scale . bimap emb id

instance KnownNat n ⇒ Add (ℝ  n) where
    add = Mor $ \x → (uncurry (F.+) $ LA.split x, LA.eye LA.||| LA.eye)

instance KnownNat n ⇒ Add (ℝp n) where
    add = Mor $ \x → let (y1,y2) = LA.split (F.exp x)
                         z       = y1 F.+ y2
                      in (F.log z, LA.diag (y1 F./ z) LA.||| LA.diag (y2 F./ z))

instance KnownNat n ⇒ Mul (ℝ  n) where
    mul = Mor $ \x → let (x1,x2) = LA.split x in (x1 F.* x2, LA.diag x1 LA.||| LA.diag x2)

instance KnownNat n ⇒ Mul (ℝp n) where
    mul = Mor $ \x → (uncurry (F.+) $ LA.split x, LA.eye LA.||| LA.eye)

instance KnownNat n ⇒ Mul (I  n) where
    mul = Mor $ \x → let (x1,x2) = LA.split x
                         (y1,y2) = LA.split $ F.exp x
                         z       = 1 F.+ y1 F.+ y2
                      in ( x1 F.+ x2 F.- F.log z
                         , LA.diag (1 F.- y1 F./ z) LA.||| LA.diag (1 F.- y2 F./ z)
                         )   

{-
instance KnownNat n ⇒ Mix (ℝ  n) where
instance KnownNat n ⇒ Mix (ℝp n) where
instance KnownNat n ⇒ Mix (I  n) where
instance KnownNat n ⇒ Mix (Δ  n) where
-}

instance KnownNat n ⇒ Invol (ℝ  n) 
instance KnownNat n ⇒ Invol (ℝp n) 
instance KnownNat n ⇒ Invol (I  n) 

{-
-- don't need this
instance KnownNat n ⇒ ScaleP (ℝ  n) where
    scalep = Mor $ \x → let (c, x') = LA.headTail x
                            e       = LA.konst $ F.exp c
                            x''     = e F.* x'
                         in (x'', LA.col x'' LA.||| LA.diag e)     
-}

instance KnownNat n ⇒ ScaleP (ℝp n) where
    scalep = Mor $ \x → let (c, x') = LA.headTail x
                         in (x' F.+ LA.konst c, 1 LA.||| LA.eye)

instance KnownNat n ⇒ Scale (ℝ  n) where
    scale = Mor $ \x → let (c, x') = LA.headTail x
                           c'      = LA.konst c
                        in (c' F.* x', LA.col x' LA.||| LA.diag c')

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
