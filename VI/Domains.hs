{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, FunctionalDependencies #-}

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
-- [@U n@] Upper-triangular n × n matrices, indentified with R^{(n(n+1)/2} with diag-major order.
-- [@Σ n@] Symmetric n × n matrices, identified with R^{n(n+1)/2} using upper triangular part.
-- [@Σp n@] Positive n × n matrices, identified with R^{n(n+1)/2} using upper triangular Cholesky factor, with logarithm applied to diagonal elements.
--
-- The latter three require 1 <= n to make KnownNat inference simpler. 
--
                    Dim, Domain, Mor(..)
                    -- * Basic domains
                  , Pt, ℝ, ℝp, I, Δ, M, Σ, Σp, U
                    -- * Concrete presentation
                  , Concrete(..), getPoint
                    -- * Basic operations
                  , type(⊂)(..), type(≌)(..)
                  , Add(..), Mul(..), ScaleP(..), Scale(..), Mix(..), Invol(..)
                  , simplexProjection
                    -- * Matrix operations
                  , tr, sym, mm, mTm
                  ) where

import VI.Categories
import VI.Jets
import VI.Util

import Prelude                  (uncurry, flip, ($), undefined)

import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Maybe
import Data.Functor
import Control.Applicative

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'
import qualified Data.Vector.Generic          as G

import GHC.Float 
import GHC.Real  
import GHC.Num   
import GHC.Classes
import GHC.Types

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
    asR = Mor id
    asL = Mor id

data Pt
data ℝ  (n ∷ Nat)
data ℝp (n ∷ Nat)
data I  (n ∷ Nat)
data Δ  (n ∷ Nat)
data M  (m ∷ Nat) (n ∷ Nat)
data Σ  (n ∷ Nat)
data Σp (n ∷ Nat)
data U  (n ∷ Nat)

type instance Dim Pt       = 0
type instance Dim (ℝ  n  ) = n
type instance Dim (ℝp n  ) = n
type instance Dim (I  n  ) = n
type instance Dim (Δ  n  ) = n
type instance Dim (M  m n) = m * n
type instance Dim (Σ  n  ) = n + ((n * (n - 1)) `Div` 2)
type instance Dim (Σp n  ) = n + ((n * (n - 1)) `Div` 2)
type instance Dim (U  n  ) = n + ((n * (n - 1)) `Div` 2)

-- | Concrete presentation
class (Domain x, KnownNat n) ⇒ Concrete (n ∷ Nat) (x ∷ Type) | x → n where
    toConcrete      ∷ Mor x (ℝ n)    
    fromConcrete    ∷ LA.R n → Mor Pt x

instance {-# OVERLAPPABLE #-} (Concrete n x, Concrete m y, KnownNat l, l ~ n + m) ⇒ Concrete l (x, y) where
    toConcrete      = iso . bimap (toConcrete @n @x) (toConcrete @m @y)
    fromConcrete p  = uncurry (×) $ bimap (fromConcrete @n @x) (fromConcrete @m @y) $ LA.split @n p

instance KnownNat n ⇒ Concrete n (ℝ n) where
    toConcrete      = id
    fromConcrete x  = Mor $ point x
   
getPoint ∷ ∀ (n ∷ Nat) (x ∷ Type). Concrete n x ⇒ Mor Pt x → LA.R n
getPoint p = let Mor (Jet f) = toConcrete . p
                 (y, _)      = f undefined
              in y

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
    emb = Mor $ fromPoints $ \x → x - log (1 + exp x) 

instance (KnownNat n, 1 <= n) ⇒ Σ n ⊂ M n n where
    emb = let n = intVal @n in Mor . law . mkFin' $ uncurry (ixΣ n) <$> lixM n n

instance (KnownNat n, 1 <= n) ⇒ U n ⊂ M n n where
    emb = let n = intVal @n 
              ι ∷ Jet ((Dim (U n)) + 1) (Dim (M n n))
              ι = law . mkFin' $ fromMaybe ((n*(n+1)) `div` 2) . uncurry (ixU n) <$> lixM n n 
           in Mor $ ι . (id ⊙ 0)

-- | Upper-triangular Cholesky factor
chol ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (Σp n) (U n)
chol = Mor $ bimap' @Jet @n @((n * (n - 1)) `Div` 2) (fromPoints exp) id

instance KnownNat n ⇒ Concrete n (ℝp n) where
    toConcrete      = emb
    fromConcrete x  = Mor $ point (log x)

instance KnownNat n ⇒ Concrete n (I n) where
    toConcrete      = emb @(ℝp n) . emb
    fromConcrete x  = Mor $ point (log $ x / (1-x)) 

instance (KnownNat n, KnownNat m, m ~ n + 1) ⇒ Concrete m (Δ n) where
    toConcrete      = emb @(ℝp m) . emb
    fromConcrete x  = Mor $ point (LA.tr (basisH @n) LA.#> log x)

-- | Additive domains 
class Domain x ⇒ Add x where
    add ∷ Mor (x, x) x

-- | Multiplicative domains
class Domain x ⇒ Mul x where
    mul ∷ Mor (x, x) x

-- | Convex domains
class Domain x ⇒ Mix x where
    mix ∷ Mor (I 1, (x, x)) x

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
    scalep = Mor $ fromPoints2' $ \c x → (diag ▶ c) + x
              
instance KnownNat n ⇒ Scale (ℝ n) where
    scale  = Mor $ fromPoints2' $ \c x → (diag ▶ c) * x

instance KnownNat n ⇒ Invol (ℝ  n) 
instance KnownNat n ⇒ Invol (ℝp n) 
instance KnownNat n ⇒ Invol (I  n) 

-- | The simplex @Δ n@ is a retract of @ℝ (n+1)@, so that 
--
-- @
-- simplexProjection . emb = id
-- @
simplexProjection ∷ ∀ n. KnownNat n ⇒ Mor (ℝp (n + 1)) (Δ n) 
simplexProjection = Mor $ linear (LA.tr basisH)

instance (KnownNat n, KnownNat m, m ~ (n + 1)) ⇒ Δ n ⊂ ℝp m where
    emb = Mor $ fromPoints $ \x → let y = linear basisH ▶ x
                                      s = log (linear 1 ▶ exp y)
                                   in y - (diag ▶ s)

instance Δ 1 ≌ I 1 where
    iso = Mor $ linear (LA.konst (sqrt 2) * LA.eye)
    osi = Mor $ linear (LA.konst (recip $ sqrt 2) * LA.eye)


instance (KnownNat m, KnownNat n) ⇒ Add (M m n) where
    add = Mor $ fromPoints2' (+)

instance (KnownNat n, 1 <= n) ⇒ Add (Σ n) where
    add = Mor $ fromPoints2' (+)

instance (KnownNat n, 1 <= n) ⇒ Add (U n) where
    add = Mor $ fromPoints2' (+)

tr ∷ ∀ m n. (KnownNat m, KnownNat n) ⇒ Mor (M m n) (M n m) 
tr = let n = intVal @n
         m = intVal @m
      in Mor . law $ mkFin' $ uncurry (flip (ixM n)) <$> lixM n m      


sym ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (M n n) (Σ n)
sym = let n = intVal @n
       in Mor . law $ mkFin' $ uncurry (ixM n) <$> lixΣ n


mm ∷ ∀ m n l. (KnownNat m, KnownNat n, KnownNat l) ⇒ Mor (M m n, M n l) (M m l)
mm = let m = intVal @m
         n = intVal @n
         l = intVal @l
      in Mor $ Jet $ \x → let (af, bf) = LA.split @(m * n) x
                              a ∷ LA.L m n = fromRtoL af
                              b ∷ LA.L n l = fromRtoL bf
                              y ∷ LA.R (m * l) = fromLtoR $ a LA.<> b
                              g dy = let δ  ∷ LA.L m l= fromRtoL dy 
                                         d1 ∷ LA.R (m * n) = fromLtoR $ δ LA.<> (LA.tr b)
                                         d2 ∷ LA.R (n * l) = fromLtoR $ (LA.tr a) LA.<> δ
                                         dx = d1 LA.# d2
                                      in dx
                           in (y, g)

mTm ∷ ∀ m n. (KnownNat m, KnownNat n, 1 <= n) ⇒ Mor (M m n) (Σ n)
mTm = sym . mm @n @m @n . bimap tr id . (id × id)

instance (KnownNat n, 1 <= n) ⇒ Σp n ⊂ Σ n where
    emb = mTm @n @n  . emb . chol    -- we factor Σp n ⊂ Σ n through the space of upper-triangular matrices

instance (KnownNat n, 1 <= n) ⇒ Mul (M n n) where
    mul = mm

instance (KnownNat m, KnownNat n) ⇒ Scale (M m n) where
    scale  = Mor $ fromPoints2' $ \c x → (diag ▶ c) * x

instance (KnownNat n, 1 <= n) ⇒ Scale (Σ n) where
    scale  = Mor $ fromPoints2' $ \c x → (diag ▶ c) * x

instance (KnownNat n, 1 <= n) ⇒ Scale (U n) where
    scale  = Mor $ fromPoints2' $ \c x → (diag ▶ c) * x

instance {-# OVERLAPPABLE #-} (ScaleP x, Add x) ⇒ Mix x where
    mix = fromPoints3 $ \c x x' → let k  = emb ▶ c
                                      k' = emb ▶ invol ▶ c
                                      y  = k  ◀ scalep $ x'
                                      y' = k' ◀ scalep $ x
                                   in y ◀ add $ y'

instance KnownNat n ⇒ Mix (Δ  n) where
    mix = fromPoints3 $ \c x x' → let k  = emb ▶ c
                                      k' = emb ▶ invol ▶ c
                                      y  = k  ◀ scalep $ emb ▶ x'
                                      y' = k' ◀ scalep $ emb ▶ x
                                   in simplexProjection ▶ (y ◀ add $ y')

instance KnownNat n ⇒ Mix (I  n) where
    mix = Mor $ fromPoints3' $ \c x x' → let e z = let w = exp z in w / (1 + w)
                                             d   = e (diag ▶ c)
                                             y   = e x
                                             y'  = e x'
                                             y'' = (1-d) * y + d * y'
                                          in log $ y'' / (1 - y'')
         
{-

{-
instance KnownNat n ⇒ Add (Σp n)
instance KnownNat n ⇒ ScaleP (Σp n)

mTm' ∷ k >= n ⇒ M k n → Σp n
mmT' ∷ k >= n ⇒ M n k → Σp n
-}

-}

