{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Domains (
                  ) where

import VI.Categories

import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Functor
import Control.Applicative

import qualified Numeric.LinearAlgebra.Static as LA
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
    Mor ∷ (Domain n x, Domain m y) ⇒ (LA.R n → LA.R m) → (LA.R n → LA.L m n) → Mor x y

instance Cat Ob Mor where
    id = Mor id (\x → LA.diag 1)
    Mor f df . Mor g dg = Mor (f . g) ((LA.<>) <$> (df . g) <*> dg)

instance Cart Ob Mor where
    pr1 = Mor (pr1 . LA.split) (\x → LA.diag 1 LA.||| 0) 
    pr2 ∷ ∀ x y. (Ob x, Ob y, Ob (x,y)) ⇒ Mor (x,y) y
    pr2 = Mor (pr2 . LA.split @(Dim x)) (\x → 0 LA.||| LA.diag 1) 
    Mor f df × Mor g dg = Mor ((LA.#) <$> f <*> g) ((LA.===) <$> df <*> dg)

-- | Unconstrained real vectors, coordinate: @id@
data ℝ  (n ∷ Nat)
-- | Positive orthant in @ℝ n@, coordinate: @log x@
data ℝp (n ∷ Nat)
-- | [0,1]^n, coordinate: @log x/(1-x)@
data I  (n ∷ Nat)
-- | standard simplex in @ℝ (n+1)@ 
data Δ  (n ∷ Nat)
-- | Unconstrained real matrices
data M  (m ∷ Nat) (n ∷ Nat)
-- | Symmetric real matrices
data Σ  (n ∷ Nat)
-- | Positive real matrices
data Σp (n ∷ Nat)

type instance Dim (ℝ  n  ) = n
type instance Dim (ℝp n  ) = n
type instance Dim (I  n  ) = n
type instance Dim (Δ  n  ) = n
type instance Dim (M  m n) = m * n
type instance Dim (Σ  n  ) = (n * (1 + n)) `Div` 2
type instance Dim (Σp n  ) = (n * (1 + n)) `Div` 2

-- | Canonical subdomain embedding
class (Ob x, Ob y) ⇒ x ⊂ y where
    emb ∷ Mor x y

instance (x ⊂ y, x' ⊂ y') ⇒ (x,x') ⊂ (y,y') where
    emb = bimap emb emb

instance Ob x ⇒ x ⊂ x where
    emb = id

instance KnownNat n ⇒ ℝp n ⊂ ℝ n where
    emb = Mor F.exp (LA.diag . F.exp)

instance KnownNat n ⇒ I n ⊂ ℝp n where
    emb = Mor (F.log . (\x → x F./ (1 F.+ x)) . F.exp)
              (LA.diag . (1 F.-) . (\x → x F./ (1 F.+ x)) . F.exp)

instance (KnownNat n, KnownNat n', n' ~ n + 1) ⇒ Δ n ⊂ I n' where

instance KnownNat n ⇒ Σ n ⊂ M n n where

instance KnownNat n ⇒ Σp n ⊂ Σ n where

-- | Canonical isomorphism
class x ≌ y where
    iso ∷ Mor x y
    osi ∷ Mor y x

instance Δ 1 ≌ I 1 where

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
class ScaleP x ⇒ Scale x where
    scale ∷ Mor (ℝ 1, x) x

-- | Involutive domains
class Invol x where
    invol ∷ Mor x x

instance KnownNat n ⇒ Add (ℝ  n) where
instance KnownNat n ⇒ Add (ℝp n) where

instance KnownNat n ⇒ Mul (ℝ  n) where
instance KnownNat n ⇒ Mul (ℝp n) where
instance KnownNat n ⇒ Mul (I  n) where

instance KnownNat n ⇒ Mix (ℝ  n) where
instance KnownNat n ⇒ Mix (ℝp n) where
instance KnownNat n ⇒ Mix (I  n) where
instance KnownNat n ⇒ Mix (Δ  n) where

instance KnownNat n ⇒ Invol (ℝ  n) where
instance KnownNat n ⇒ Invol (ℝp n) where
instance KnownNat n ⇒ Invol (I  n) where

instance KnownNat n ⇒ ScaleP (ℝ  n) where
instance KnownNat n ⇒ ScaleP (ℝp n) where

instance KnownNat n ⇒ Scale (ℝ  n) where

