{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Jets ( Jet(..)
               , point, linear, affine 
               ) where

import VI.Categories

import Prelude                  (uncurry, ($), const)
import Data.Maybe
import Data.Bool 
import Data.Functor
import Control.Applicative
import GHC.TypeLits
import GHC.TypeLits.Extra
import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra as LA'
import qualified Data.List as L
import GHC.Classes
import GHC.Float 
import GHC.Real  
import GHC.Num   

import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM

-- | 1-jet of a map R^n -> R^m, as value & transpose Jacobian
--
-- Note the associated instances.
--
-- Example:
--
-- @
--   test ∷ Jet 2 2
--   test = fromPoints2' $ \\x y → (exp $ x * y) ⊙ ( sin (x * pi) / exp y ) 
-- @  
data Jet (n ∷ Nat) (m ∷ Nat) where
    Jet ∷ (KnownNat n, KnownNat m) ⇒ (LA.R n → (LA.R m, LA.R m → LA.R n)) → Jet n m

instance Cat KnownNat Jet where
    id = Jet $ \x → (x, id)
    Jet φ . Jet ψ = Jet $ \x → let (y, dψ) = ψ x
                                   (z, dφ) = φ y
                                in (z, dψ . dφ)

instance Cart' Jet where
    pr1' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Jet (n + m) n
    pr1' = Jet $ \x → (pr1 $ LA.split @n x, (LA.# 0))
    pr2' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Jet (n + m) m
    pr2' = Jet $ \x → (pr2 $ LA.split @n x, (0 LA.#))
    Jet φ ⊙ Jet ψ = Jet $ \x → let (y, dφ) = φ x
                                   (z, dψ) = ψ x
                                in (y LA.# z, uncurry (+) . bimap dφ dψ . LA.split)

lift1 ∷ ∀ c n m. (KnownNat n, KnownNat m, c (LA.R m)) ⇒ (∀ a. c a ⇒ (a → (a, a))) → Jet n m → Jet n m
lift1 f (Jet φ) = Jet $ \x → let (y, dφ) = φ x
                                 (z, df) = f y 
                              in (z, dφ . (df *))     

instance (KnownNat n, KnownNat m) ⇒ Num (Jet n m) where
    Jet φ + Jet ψ  = Jet $ \x → let (y, dφ) = φ x
                                    (z, dψ) = ψ x
                                 in (y + z, (+) <$> dφ <*> dψ)  
    Jet φ * Jet ψ  = Jet $ \x → let (y, dφ) = φ x
                                    (z, dψ) = ψ x
                                 in (y * z, (+) <$> dφ . (z *) <*> dψ . (y *))
    fromInteger k  = Jet $ \_ → (fromInteger k, pure 0) 
    abs            = lift1 @Num $ \x → (abs x, signum x)
    signum         = lift1 @Num $ \x → (signum x, 0)
    negate         = lift1 @Num $ \x → (negate x, -1)

instance (KnownNat n, KnownNat m) ⇒ Fractional (Jet n m) where
    fromRational r = Jet $ \_ → (fromRational r, pure 0)
    recip          = lift1 @Fractional $ \x → (recip x, negate $ x * x)

instance (KnownNat n, KnownNat m) ⇒ Floating (Jet n m) where
    pi             = Jet $ \_ → (pi, pure 0)
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

instance Law Jet where
    law ∷ ∀ n m. Fin' n m → Jet n m
    law (Fin' j) = let m = intVal @m
                       n = intVal @n   
                    in Jet $ \x → let x' = LA.extract x
                                      y' = G.map (x' LA'.!) j
                                      Just y = LA.create y'
                                      g ∷ LA.R m → LA.R n
                                      g dy = let u = LA.extract dy 
                                                 v = G.generate n $ \i → G.sum (G.zipWith (\j0 u0 → bool 0 u0 (j0==i)) j u)
                                                 Just dx = LA.create v
                                              in dx 
                                   in (y, g)

point ∷ (KnownNat n, KnownNat m) ⇒ LA.R n → Jet m n
point x = Jet $ \_ → (x, pure 0)

linear ∷ (KnownNat n, KnownNat m) ⇒ LA.L m n → Jet n m
linear a = Jet $ \x → (a LA.#> x, (LA.tr a LA.#>))

-- | This is a basic example of pointed style:
--
-- @
--     affine b a = fromPoints $ \x → point b + linear a ▶ x 
-- @
affine ∷ (KnownNat n, KnownNat m) ⇒ LA.R m → LA.L m n → Jet n m
affine b a = fromPoints $ \x → point b + linear a ▶ x

