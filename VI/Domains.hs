{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, FunctionalDependencies, IncoherentInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Domains ( -- * Cartesian category of domains

-- |
-- A domain is a space together with a distinguished identification 
-- with the Euclidean space \(\mathbb{R}^n\) for some natural \(n\); that is, a global coordinate.
--
-- Morphisms (see 'Mor') between domains are specified as 1-jets
-- of differentiable maps between corresponding Euclidean spaces.
-- Domains form a Cartesian category (see 'Cat' and 'Cart'), with '(,)' as product,
-- equivalent to 'J'. 
-- Their purpose
-- is to serve as parameter domains as well as target spaces for families 
-- of probability distributions.
                    Dim, Domain, Mor(..), Point
                    -- * Basic domains
-- |
-- We present basic domains as open subsets
-- of (possibly a subspace in) some \(\mathbb{R}^m\), and specify the
-- coordinate:
--
-- [@ℝ n@] All of \(\mathbb{R}^n\), with identity coordinate.
-- [@ℝp n@] Positive orthant of \(\mathbb{R}^n\), with elementwise logarithm coordinate.
-- [@I n@] Positive unit cube in \(\mathbb{R}^n\), with elementwise logit coordinate.
-- [@Δ n@] The n-simplex in \(\mathbb{R}^{n+1}\), with coordinate \(p \mapsto \log p - \frac{1}{n+1} \sum\log p\) mapping onto the hyperplane orthogonal to \((1,...,1)\) in \(\mathbb{R}^{n+1}\).
-- [@M n m@] All n × m matrices, identified with \(\mathbb{R^{nm}}\) with row-major order.
-- [@Lo n@] Lower-triangular n × n matrices, indentified with \(\mathbb{R}^{\frac{n(n+1)}{2}}\) with diag-major order.
-- [@Σ n@] Symmetric n × n matrices, identified with \(\mathbb{R}^{\frac{n(n+1)}{2}}\) using lower triangular part.
-- [@Σp n@] Positive n × n matrices, identified with \(\mathbb{R}^{\frac{n(n+1)}{2}}\) using lower triangular Cholesky factor, with logarithm applied to diagonal elements.
--
-- The above concrete presentations are accessible via the class 'Concrete'. In particular, a morphism from the point '()' into a domain,
-- viewed as a concrete point of the ambient Euclidean space, has coordinates given by 'getPoint'. Two auxiliary functions, 'real' and 'realp',
-- convert concrete real (resp. positive real) numbers into constant morphisms into @ℝ 1@ (resp. @ℝp 1@).
                  , ℝ, ℝp, I, Δ, M, Σ, Σp, Lo
                  , Concrete(..), getPoint, real, realp, getMatrix
                    -- * General structures 
-- |
-- Additional structures on domains are expressed in terms of several type classes:
--
-- * '≃' and '⊂' define canonical isomorphisms and embeddings;
-- * 'Based' defines canonical basepoints;
-- * 'Add' defines an additive semigroup structure, extended by 'Ab' to an abelian group structure;
-- * 'Mul' defines a multiplicative semigroup structure, extended by 'AbM' to an abelian group structure;
-- * 'ScaleP' defines a multiplicative action of @ℝp 1@, extended by 'Scale' to an action of @ℝ 1@;
-- * 'Lerp' defines a convex structure;
-- * 'Invol' defines a distinguished involution.
--
-- Furthermore, the class 'Dot' is used to introduce a highly overloaded operator '∙' expressing
-- various multiplicative pairings, including matrix multiplication. It is best used in pointful style (see '◀').
                  , type(≃)(..)
                  , type(⊂)(..)
                  , Based(..)
                  , Add(..), Ab(..), Mul(..), AbM(..), ScaleP(..), Scale(..), Lerp(..), Invol(..)
                  , Dot(..), (∙)
                  , Square(..)
                    -- * Individual morphisms
-- |
-- Many other natural morphisms, not covered by the above classes, are defined in what follows.
-- These include:
--
--   * standard diffeomorphisms between @ℝp@, @ℝ@ and @I@ (logarithm, the logistic function, and their inverses),
--   * special functions for use in probaiblity densities (gamma, beta)
--   * basic linear algebra.
                  , log', exp', logit, logistic, gamma
                  , simplexProjection
                  , tr, sym, tril, chol, cholInverse, cholDet, prodP, mm, mmT
                  , toNil, decomposeChol, composeChol 
                  ) where

import VI.Categories
import VI.Jets
import VI.Util

import Prelude                  (uncurry, flip, ($), undefined)

import GHC.TypeNats
import Data.Maybe
import Data.Functor
import Control.Applicative

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'
import qualified Numeric.GSL.Special.Gamma    as GSL
import qualified Numeric.GSL.Special.Psi      as GSL
import qualified Data.Vector.Generic          as G

import GHC.Float 
import GHC.Real  
import GHC.Num   
import GHC.Classes
import GHC.Types

{-
 -  Basic definitions
 -}

-- | Dimension of a domain
type family Dim (x ∷ Type) ∷ Nat

type instance Dim (x,y) = (Dim x) + (Dim y)
type instance Dim ()    = 0

class    KnownNat (Dim x) ⇒ Domain (x ∷ Type)
instance KnownNat (Dim x) ⇒ Domain x

-- | Morphisms between domains
data Mor x y = Mor (J (Dim x) (Dim y))

instance Cat Domain Mor where
    id = Mor id
    Mor φ . Mor ψ = Mor (φ . ψ)
    witness (Mor (J _)) a = a

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
data Lo (n ∷ Nat)

type instance Dim ()       = 0
type instance Dim (ℝ  n  ) = n
type instance Dim (ℝp n  ) = n
type instance Dim (I  n  ) = n
type instance Dim (Δ  n  ) = n
type instance Dim (M  m n) = m * n
type instance Dim (Σ  n  ) = n + ((n * (n - 1)) `Div` 2)
type instance Dim (Σp n  ) = n + ((n * (n - 1)) `Div` 2)
type instance Dim (Lo n  ) = n + ((n * (n - 1)) `Div` 2)

instance Terminal Domain Mor () where
    terminal = Mor terminal 

-- | Point of a domain 
type Point = Mor ()

{-
 -  Concrete presentation / construction
 -}

class (Domain x, KnownNat n) ⇒ Concrete (n ∷ Nat) x | x → n where
    toConcrete      ∷ Mor x (ℝ n)    
    fromConcrete    ∷ LA.R n → Point x

instance Concrete 0 () where
    toConcrete      = Mor id
    fromConcrete _  = Mor id

instance {-# OVERLAPPABLE #-} (Concrete n x, Concrete m y, KnownNat l, l ~ n + m) ⇒ Concrete l (x, y) where
    toConcrete      = iso . bimap (toConcrete @n @x) (toConcrete @m @y)
    fromConcrete p  = uncurry (×) $ bimap (fromConcrete @n @x) (fromConcrete @m @y) $ LA.split @n p

instance KnownNat n ⇒ Concrete n (ℝ n) where
    toConcrete      = id
    fromConcrete x  = Mor $ point x
   
getPoint ∷ ∀ (n ∷ Nat) x. Concrete n x ⇒ Point x → LA.R n
getPoint p = let Mor (J f) = toConcrete . p
                 (y, _)    = f undefined
              in y

real ∷ ∀ t n.  (Domain t, KnownNat n) ⇒ Double → Mor t (ℝ n) 
real x = Mor $ point $ LA.konst x

realp ∷ ∀ t n. (Domain t, KnownNat n) ⇒ Double → Mor t (ℝp n) 
realp x = Mor $ point $ LA.konst $ log x

getMatrix ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Point (M n m) → LA.L n m
getMatrix p = let Mor (J f) = p
                  (v, _) = f undefined
               in fromRtoL v   

{-
 -  Isomorphisms
 -}

-- | Canonical isomorphism.
--
-- Note: it is convenient to define instances asymmetrically. The desired
-- direction of the isomorphism may then be indicated distinguishing 'iso' vs. 'osi'. 
class (Domain x, Domain y, Dim x ~ Dim y) ⇒ x ≃ y where
    iso ∷ Mor x y
    osi ∷ Mor y x
    iso = Mor id
    osi = Mor id

instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (ℝ n, ℝ m)   ≃ ℝ  l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (ℝp n, ℝp m) ≃ ℝp l
instance (KnownNat n, KnownNat m, KnownNat l, l ~ n + m) ⇒ (I n, I m)   ≃ I  l

instance Domain x ⇒ ((), x) ≃ x
instance Domain x ⇒ (x, ()) ≃ x
instance (Domain x, Domain y, Domain z) ⇒ (x, (y, z)) ≃ ((x, y), z)

instance (Domain x, Domain y) ⇒ (x, y) ≃ (y, x) where
    iso = swap
    osi = swap

instance Δ 1 ≃ I 1 where
    iso = Mor $ linear (LA.konst (sqrt 2) * LA.eye)
    osi = Mor $ linear (LA.konst (recip $ sqrt 2) * LA.eye)

instance KnownNat n ⇒ M n 1 ≃ ℝ n
instance {-# OVERLAPPABLE #-} KnownNat n ⇒ M 1 n ≃ ℝ n

{-
 -  Embeddings
 -}

-- | Canonical subdomain embedding
class (Domain x, Domain y) ⇒ x ⊂ y where
    emb ∷ Mor x y

instance Domain x ⇒ x ⊂ x where
    emb = id

instance (x ⊂ y, x' ⊂ y') ⇒ (x,x') ⊂ (y,y') where
    emb = bimap emb emb

instance KnownNat n ⇒ ℝp n ⊂ ℝ n where
    emb = Mor $ fromPoints exp

instance KnownNat n ⇒ I n ⊂ ℝp n where
    emb = Mor $ fromPoints $ \x → x - log (1 + exp x) 

instance (KnownNat n, 1 <= n) ⇒ Σ n ⊂ M n n where
    emb = let n = intVal @n in Mor . law . mkFin' $ uncurry (ixΣ n) <$> lixM n n

instance (KnownNat n, 1 <= n) ⇒ Lo n ⊂ M n n where
    emb = let n = intVal @n 
              ι ∷ J (Dim (Lo n) + 1) (Dim (M n n))
              ι = law . mkFin' $ fromMaybe ((n*(n+1)) `div` 2) . uncurry (ixLo n) <$> lixM n n 
           in Mor $ ι . (id ⊙ 0)

instance (KnownNat n, KnownNat m, m ~ (n + 1)) ⇒ Δ n ⊂ ℝp m where
    emb = Mor $ fromPoints $ \x → let y = linear basisH ▶ x
                                      s = log (linear 1 ▶ exp y)
                                   in y - (expand ▶ s)

instance (KnownNat n, 1 <= n) ⇒ Σp n ⊂ Σ n where
    emb = mmT @n @n  . emb . chol    -- we factor Σp n ⊂ Σ n through the space of lower-triangular matrices


instance KnownNat n ⇒ Concrete n (ℝp n) where
    toConcrete      = emb
    fromConcrete x  = Mor $ point (log x)

instance KnownNat n ⇒ Concrete n (I n) where
    toConcrete      = emb @(ℝp n) . emb
    fromConcrete x  = Mor $ point (log $ x / (1-x)) 

instance (KnownNat n, KnownNat m, m ~ n + 1) ⇒ Concrete m (Δ n) where
    toConcrete      = emb @(ℝp m) . emb
    fromConcrete x  = Mor $ point (LA.tr (basisH @n) LA.#> log x)


{-
 -  Add
 -}

-- | Additive domains 
class Domain x ⇒ Add x where
    add ∷ Mor (x, x) x

instance KnownNat n ⇒ Add (ℝ n) where
    add = Mor $ fromPoints2' (+)

instance KnownNat n ⇒ Add (ℝp n) where
    add = Mor $ fromPoints2' $ \x y → log (exp x + exp y)

instance (KnownNat m, KnownNat n) ⇒ Add (M m n) where
    add = Mor $ fromPoints2' (+)

instance (KnownNat n, 1 <= n) ⇒ Add (Σ n) where
    add = Mor $ fromPoints2' (+)

instance (KnownNat n, 1 <= n) ⇒ Add (Lo n) where
    add = Mor $ fromPoints2' (+)

instance (KnownNat n, 1 <= n) ⇒ Add (Σp n) where
    add = Mor $ fromPoints2' $ \x y → let x0 = pr1' @J @n ▶ x
                                          x1 = pr2' @J @n ▶ x
                                          y0 = pr1' @J @n ▶ y
                                          y1 = pr2' @J @n ▶ y
                                          z0 = log (exp x0 + exp y0)
                                          z1 = x1 + y1
                                       in z0 ⊙ z1  

{-
 -  Mul
 -}

-- | Multiplicative domains
class Domain x ⇒ Mul x where
    mul ∷ Mor (x, x) x

instance KnownNat n ⇒ Mul (ℝ n) where
    mul = Mor $ fromPoints2' (*)

instance KnownNat n ⇒ Mul (ℝp n) where
    mul = Mor $ fromPoints2' (+)

instance KnownNat n ⇒ Mul (I n) where
    mul = Mor $ fromPoints2' $ \x y → x + y - log (1 + exp x + exp y)  

instance KnownNat n ⇒ Mul (M n n) where
    mul = mm

instance (KnownNat n,  1 <= n) ⇒ Mul (Lo n) where
    mul = tril . mm @n @n @n . bimap emb emb

{-
 -  Lerp
 -}

-- | Convex domains
class Domain x ⇒ Lerp x where
    lerp ∷ Mor (I 1, (x, x)) x

instance {-# OVERLAPPABLE #-} (ScaleP x, Add x) ⇒ Lerp x where
    lerp = fromPoints3 $ \c x x' → let k  = emb ▶ c
                                       k' = emb ▶ invol ▶ c
                                       y  = k  ◀ scalep $ x'
                                       y' = k' ◀ scalep $ x
                                    in y ◀ add $ y'

instance KnownNat n ⇒ Lerp (Δ  n) where
    lerp = fromPoints3 $ \c x x' → let k  = emb ▶ c
                                       k' = emb ▶ invol ▶ c
                                       y  = k  ◀ scalep $ emb ▶ x'
                                       y' = k' ◀ scalep $ emb ▶ x
                                    in simplexProjection ▶ (y ◀ add $ y')

instance KnownNat n ⇒ Lerp (I  n) where
    lerp = Mor $ fromPoints3' $ \c x x' → let e z = let w = exp z in w / (1 + w)
                                              d   = e (expand ▶ c)
                                              y   = e x
                                              y'  = e x'
                                              y'' = (1-d) * y + d * y'
                                           in log $ y'' / (1 - y'')

{-
 - ScaleP, Scale
 -}


-- | Conical domains
class Domain x ⇒ ScaleP x where
    scalep ∷ Mor (ℝp 1, x) x

-- | Projective domains
class Domain x ⇒ Scale x where
    scale ∷ Mor (ℝ 1, x) x

instance {-# OVERLAPPABLE #-} Scale x ⇒ ScaleP x where
    scalep = scale . bimap emb id

instance KnownNat n ⇒ ScaleP (ℝp n) where
    scalep = Mor $ fromPoints2' $ \c x → (expand ▶ c) + x
              
instance KnownNat n ⇒ Scale (ℝ n) where
    scale  = Mor $ fromPoints2' $ \c x → (expand ▶ c) * x

instance (KnownNat m, KnownNat n) ⇒ Scale (M m n) where
    scale  = Mor $ fromPoints2' $ \c x → (expand ▶ c) * x

instance (KnownNat n, 1 <= n) ⇒ Scale (Σ n) where
    scale  = Mor $ fromPoints2' $ \c x → (expand ▶ c) * x

instance (KnownNat n, 1 <= n) ⇒ Scale (Lo n) where
    scale  = Mor $ fromPoints2' $ \c x → (expand ▶ c) * x

instance (KnownNat n, 1 <= n) ⇒ ScaleP (Σp n) where
    scalep = Mor $ fromPoints2' $ \c x → let x0 = pr1' @J @n ▶ x
                                             x1 = pr2' @J @n ▶ x
                                             e  = exp c
                                             y0 = (expand ▶ c) + x0
                                             y1 = (expand ▶ e) * x1
                                          in y0 ⊙ y1  

{-
 -  Invol
 -}

-- | Involutive domains
class Domain x ⇒ Invol x where
    -- | by default, invol corresponds to negation in canonical coordinates
    invol ∷ Mor x x
    invol = Mor $ fromPoints negate

instance KnownNat n ⇒ Invol (ℝ  n) 
instance KnownNat n ⇒ Invol (ℝp n) 
instance KnownNat n ⇒ Invol (I  n) 
instance KnownNat n ⇒ Invol (Δ  n)

{- 
 -  Ab, AbM
 -}

-- | (additive) Abelian domains
class Add x ⇒ Ab x where
    neg ∷ Mor x x
    sub ∷ Mor (x, x) x
    sub = add . bimap id neg

-- | (multiplicative) Abelian domains
class Mul x ⇒ AbM x where
    rcp ∷ Mor x x
    quo ∷ Mor (x, x) x
    quo = mul . bimap id rcp

instance KnownNat n ⇒ Ab (ℝ n) where
    neg = Mor $ fromPoints negate
    sub = Mor $ fromPoints2' (-)

instance KnownNat n ⇒ AbM (ℝp n) where
    rcp = Mor $ fromPoints negate
    quo = Mor $ fromPoints2' (-)

instance (KnownNat m, KnownNat n) ⇒ Ab (M m n) where
    neg = Mor $ fromPoints negate
    sub = Mor $ fromPoints2' (-)

instance (KnownNat n, 1 <= n) ⇒ Ab (Σ n) where
    neg = Mor $ fromPoints negate
    sub = Mor $ fromPoints2' (-)

instance (KnownNat n, 1 <= n) ⇒ Ab (Lo n) where
    neg = Mor $ fromPoints negate
    sub = Mor $ fromPoints2' (-)

{-
 -  Dot
 -}

-- | Heavily overloaded dot operator for multiplicative pairings 
class (Domain x, Domain y, Domain z) ⇒ Dot x y z | x y → z where
    dot ∷ Mor (x, y) z

(∙) ∷ (Domain t, Dot x y z) ⇒ Mor t x → Mor t y → Mor t z -- Sb
(∙) = toPoints2 dot

instance (KnownNat m, KnownNat n, KnownNat l) ⇒ Dot (M m n) (M n l) (M m l) where
    dot = mm

instance (KnownNat m, KnownNat n) ⇒ Dot (M m n) (ℝ n) (ℝ m) where
    dot = iso . mm @m @n @1 . bimap id osi

instance (KnownNat n, x ⊂ M n n) ⇒ Dot x (ℝ n) (ℝ n) where
    dot = iso . mm @n @n @1 . bimap emb osi

instance (KnownNat m, KnownNat n) ⇒ Dot (ℝ m) (M m n) (ℝ n) where
    dot = iso . mm @1 @m @n . bimap osi id 

instance (KnownNat n, x ⊂ M n n) ⇒ Dot (ℝ n) x (ℝ n) where
    dot = iso . mm @1 @n @n . bimap osi emb

instance KnownNat n ⇒ Dot (ℝ n) (ℝ n) (ℝ 1) where
    dot = iso . mm @1 @n @1 . bimap osi osi

{-
 -  Based
 -}

-- | Based domains
class Domain x ⇒ Based x where
    -- | by default, the basepoint is zero in canonical coordinates
    basePoint ∷ Point x
    basePoint = Mor 0

instance KnownNat n ⇒ Based (ℝ  n)
instance KnownNat n ⇒ Based (ℝp n)
instance KnownNat n ⇒ Based (Δ  n)
instance KnownNat n ⇒ Based (I  n)
instance (KnownNat n, 1 <= n) ⇒ Based (Σ  n)
instance (KnownNat n, 1 <= n) ⇒ Based (Lo n)
instance (KnownNat n, 1 <= n) ⇒ Based (Σp n)

{-
 -  Square
 -}

-- | Square matrices
class Domain x ⇒ Square x where
    type Diag x
    toDiag      ∷ Mor x (Diag x)
    fromDiag    ∷ Mor (Diag x) x

instance (KnownNat n, 1 <= n) ⇒ Square (Lo n) where
    type Diag (Lo n) = ℝ n
    toDiag = Mor $ pr1' @_ @n
    fromDiag = Mor $ id ⊙ 0

instance (KnownNat n, 1 <= n) ⇒ Square (Σ n) where
    type Diag (Σ n) = ℝ n
    toDiag = Mor $ pr1' @_ @n
    fromDiag = Mor $ id ⊙ 0

instance (KnownNat n, 1 <= n) ⇒ Square (Σp n) where
    type Diag (Σp n) = ℝp n
    toDiag = Mor $ pr1' @_ @n
    fromDiag = Mor $ id ⊙ 0

{-
 -  Individual morphisms
 -}

-- | The simplex @Δ n@ is a retract of @ℝ (n+1)@, so that 
--
-- @
-- simplexProjection . emb = id
-- @
simplexProjection ∷ ∀ n. KnownNat n ⇒ Mor (ℝp (n + 1)) (Δ n) 
simplexProjection = Mor $ linear (LA.tr basisH)

-- | matrix transpose
tr ∷ ∀ m n. (KnownNat m, KnownNat n) ⇒ Mor (M m n) (M n m) 
tr = let n = intVal @n
         m = intVal @m
      in Mor . law $ mkFin' $ uncurry (flip (ixM n)) <$> lixM n m      


-- | produce a symmetric matrix using the lower triangular part
sym ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (M n n) (Σ n)
sym = let n = intVal @n
       in Mor . law $ mkFin' $ uncurry (ixM n) <$> lixΣ n

-- | extract the lower triangular part
tril ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (M n n) (Lo n)
tril = let n = intVal @n
        in Mor . law $ mkFin' $ uncurry (ixM n) <$> lixLo n   

-- | matrix multiply
mm ∷ ∀ m n l. (KnownNat m, KnownNat n, KnownNat l) ⇒ Mor (M m n, M n l) (M m l)
mm = let m = intVal @m
         n = intVal @n
         l = intVal @l
      in Mor $ J $ \x → let (af, bf) = LA.split @(m * n) x
                            a ∷ LA.L m n = fromRtoL af
                            b ∷ LA.L n l = fromRtoL bf
                            y ∷ LA.R (m * l) = fromLtoR $ a LA.<> b
                            g dy = let δ  ∷ LA.L m l= fromRtoL dy 
                                       d1 ∷ LA.R (m * n) = fromLtoR $ δ LA.<> LA.tr b
                                       d2 ∷ LA.R (n * l) = fromLtoR $ LA.tr a LA.<> δ
                                       dx = d1 LA.# d2
                                    in dx
                         in (y, g)

-- | produce a symmetric matrix, mapping a to a a^T
mmT ∷ ∀ m n. (KnownNat m, KnownNat n, 1 <= n) ⇒ Mor (M n m) (Σ n)
mmT = sym . mm @n @m @n . bimap id tr . (id × id)



-- | Lower-triangular Cholesky factor
chol ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (Σp n) (Lo n)
chol = Mor $ bimap' @J @n @((n * (n - 1)) `Div` 2) (fromPoints exp) id

-- | take nilpotent part (i.e. put zeroes on diagonal)
toNil ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (Lo n) (Lo n)
toNil = Mor $ 0 ⊙ pr2' @J @n

-- | decompose lower Cholesky factor into diagonal and nilpotent parts
decomposeChol ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (Σp n) (ℝp n, Lo n)
decomposeChol = toDiag × (toNil . chol)

-- | left inverse of 'decomposeChol'
composeChol ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (ℝp n, Lo n) (Σp n)
composeChol = Mor $ bimap' @J @n @(n + (n * (n - 1)) `Div` 2) id (pr2' @J @n)

-- | inverse of the lower Cholesky factor
cholInverse ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (Σp n) (Lo n)
cholInverse = chol . composeChol . f . decomposeChol
              where
                f ∷ Mor (ℝp n, Lo n) (ℝp n, Lo n)
                f = let n = intVal @n 
                     in fromPoints2 $ \d u → let di   = invol ▶ d
                                                 di'  = emb @(ℝp n) @(ℝ n) ▶ di
                                                 di'' = fromDiag @(Lo n) ▶ di'
                                                 v    = neg ▶ (di'' ◀ mul $ toNil ▶ u) -- -D^{-1} U_nil
                                                 go 1 = v
                                                 go k = v ◀ add $ v ◀ mul $ go (k-1)
                                                 ui   = go (n-1) ◀ mul $ di''            -- ( Σ_{0<k<n} (-D^{-1} U_nil)^k ) D^{-1}
                                              in di × ui                                 -- ( Σ_{k>=0}  (-D^{-1} U_nil)^k ) D^{-1}
                                                                                         -- = [ I + D^{-1} U_nil ]^{-1}  D^{-1}
                                                                                         -- = [ D + U_nil ]^{-1}

-- | determinant of the lower Cholesky factor
cholDet ∷ ∀ n. (KnownNat n, 1 <= n) ⇒ Mor (Σp n) (ℝp 1)
cholDet = Mor $ linear (LA.konst 1) . pr1' @_ @n

-- | product of positive reals
prodP ∷ KnownNat n ⇒ Mor (ℝp n) (ℝp 1)
prodP = Mor $ linear (LA.konst 1)

-- | logarithm
log' ∷ KnownNat n ⇒ Mor (ℝp n) (ℝ n)
log' = Mor id

-- | exponential
exp' ∷ KnownNat n ⇒ Mor (ℝ n) (ℝp n)
exp' = Mor id

-- | logit
logit ∷ KnownNat n ⇒ Mor (I n) (ℝ n)
logit = Mor id

-- | logistic 
logistic ∷ KnownNat n ⇒ Mor (ℝ n) (I n)
logistic = Mor id

-- | gamma function
gamma ∷ KnownNat n ⇒ Mor (ℝp n) (ℝp n)
gamma = Mor . J $ \x → let ex = exp x
                           y  = LA.dvmap GSL.lngamma ex
                           d  = ex * LA.dvmap GSL.psi ex
                        in (y, (d *))

-- | beta function
beta ∷ KnownNat n ⇒ Mor (I n, I n) (ℝp n)
beta = fromPoints2 $ \x y → let x' = emb . x
                                y' = emb . y
                                p  = (gamma ▶ x') ◀ mul $ (gamma ▶ y')
                                q  = gamma ▶ (x' ◀ add $ y')
                             in p ◀ quo $ q  

