{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Jets ( J(..)
               , point, linear, affine 
               ) where

import VI.Categories

import Prelude                  (uncurry, ($), const)
import Data.Maybe
import Data.Bool 
import Data.Functor
import Control.Applicative
import GHC.TypeNats
import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra as LA'
import qualified Data.List as L
import GHC.Classes
import GHC.Float 
import GHC.Real  
import GHC.Num   

import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM

-- | @J n m@ models sections of J¹(π₁ : R^n × R^m → R^n),
-- mapping a point of R^n to a point of R^m together with a
-- transpose Jacobian R^m → R^n. Note that the latter is a 
-- map on points, not a jet itself; thus 'J' interprets only
-- first-order differentiable programs.
--
-- Example:
--
-- @
--   test ∷ J 2 2
--   test = fromPoints2' $ \\x y → (exp $ x * y) ⊙ ( sin (x * pi) / exp y ) 
-- @  
data J (n ∷ Nat) (m ∷ Nat) where
     J ∷ (KnownNat n, KnownNat m) ⇒ (LA.R n → (LA.R m, LA.R m → LA.R n)) → J n m

instance Cat KnownNat J where
    id = J $ \x → (x, id)
    J φ . J ψ = J $ \x → let (y, dψ) = ψ x
                             (z, dφ) = φ y
                          in (z, dψ . dφ)
    witness (J _) a = a

instance Cart' J where
    pr1' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ J (n + m) n
    pr1' = J $ \x → (pr1 $ LA.split @n x, (LA.# 0))
    pr2' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ J (n + m) m
    pr2' = J $ \x → (pr2 $ LA.split @n x, (0 LA.#))
    J φ ⊙ J ψ = J $ \x → let (y, dφ) = φ x
                             (z, dψ) = ψ x
                          in (y LA.# z, uncurry (+) . bimap dφ dψ . LA.split)

lift1 ∷ ∀ c n m. (KnownNat n, KnownNat m, c (LA.R m)) ⇒ (∀ a. c a ⇒ (a → (a, a))) → J n m → J n m
lift1 f (J φ) = J $ \x → let (y, dφ) = φ x
                             (z, df) = f y 
                          in (z, dφ . (df *))     

instance (KnownNat n, KnownNat m) ⇒ Num (J n m) where
    J φ + J ψ    = J $ \x → let (y, dφ) = φ x
                                (z, dψ) = ψ x
                            in (y + z, (+) <$> dφ <*> dψ)  
    J φ * J ψ    = J $ \x → let (y, dφ) = φ x
                                (z, dψ) = ψ x
                             in (y * z, (+) <$> dφ . (z *) <*> dψ . (y *))
    fromInteger k  = J $ \_ → (fromInteger k, pure 0) 
    abs            = lift1 @Num $ \x → (abs x, signum x)
    signum         = lift1 @Num $ \x → (signum x, 0)
    negate         = lift1 @Num $ \x → (negate x, -1)

instance (KnownNat n, KnownNat m) ⇒ Fractional (J n m) where
    fromRational r = J $ \_ → (fromRational r, pure 0)
    recip          = lift1 @Fractional $ \x → (recip x, negate . recip $ x * x)

instance (KnownNat n, KnownNat m) ⇒ Floating (J n m) where
    pi             = J $ \_ → (pi, pure 0)
    exp            = lift1 @Floating $ \x → let y = exp x in (y, y) 
    log            = lift1 @Floating $ \x → (log x, recip x)
    sin            = lift1 @Floating $ \x → (sin x, cos x)
    cos            = lift1 @Floating $ \x → (cos x, negate $ sin x)
    tan            = lift1 @Floating $ \x → let y = recip $ cos x in (tan x, y * y)
    asin           = lift1 @Floating $ \x → (asin x, recip $ cos x)
    acos           = lift1 @Floating $ \x → (acos x, negate . recip $ sin x)
    atan           = lift1 @Floating $ \x → let y = cos x in (atan x, y * y)
    sinh           = lift1 @Floating $ \x → (sinh x, cosh x)  
    cosh           = lift1 @Floating $ \x → (cosh x, sinh x)  
    tanh           = lift1 @Floating $ \x → let y = recip $ cosh x in (tanh x, y * y)
    asinh          = lift1 @Floating $ \x → (asinh x, recip $ cosh x)
    acosh          = lift1 @Floating $ \x → (asinh x, recip $ sinh x)
    atanh          = lift1 @Floating $ \x → let y = cosh x in (atanh x, y * y)
    sqrt           = lift1 @Floating $ \x → let y = sqrt x in (y, recip $ 2 * y)

instance Law J where
    law ∷ ∀ n m. Fin' n m → J n m
    law (Fin' j) = let m = intVal @m
                       n = intVal @n   
                    in J $ \x → let x' = LA.extract x
                                    y' = G.map (x' LA'.!) j
                                    Just y = LA.create y'
                                    g ∷ LA.R m → LA.R n
                                    g dy = let u = LA.extract dy 
                                               v = G.generate n $ \i → G.sum (G.zipWith (\j0 u0 → bool 0 u0 (j0==i)) j u)
                                               Just dx = LA.create v
                                            in dx 
                                 in (y, g)

point ∷ (KnownNat n, KnownNat m) ⇒ LA.R n → J m n
point x = J $ \_ → (x, pure 0)

linear ∷ (KnownNat n, KnownNat m) ⇒ LA.L m n → J n m
linear a = J $ \x → (a LA.#> x, (LA.tr a LA.#>))

-- | This is a basic example of pointed style:
--
-- @
--     affine b a = fromPoints $ \x → point b + linear a ▶ x 
-- @
affine ∷ (KnownNat n, KnownNat m) ⇒ LA.R m → LA.L m n → J n m
affine b a = fromPoints $ \x → point b + linear a ▶ x

