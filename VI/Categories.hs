{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, StandaloneKindSignatures, LiberalTypeSynonyms, FunctionalDependencies, RankNTypes, ScopedTypeVariables, InstanceSigs #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Categories ( -- * Categories
                       Cat(..), Unconstrained, Terminal(..)
                       -- * Cartesian categories
                     , Cart(..), bimap, assocR, assocL, swap
                     , Cart'(..), bimap'
                       -- * Pointed/point-free conversion
                     , fromPoints, toPoints, fromPoints2, toPoints2, fromPoints2', toPoints2', fromPoints3, fromPoints3'
                     , (▶), (◀)
                       -- * Lawvere theories
                     , Fin'(..), mkFin', Law(..), expand
                       -- * Auxiliary
                     , intVal
                     ) where

import Prelude (otherwise, error)

import Data.Kind
import Data.Functor
import Data.Proxy
import Control.Applicative
import GHC.Types
import GHC.Classes
import GHC.Num
import GHC.Real
import GHC.TypeNats
import Data.Function (($))
import qualified Data.Function as F
import qualified Data.Tuple as T
import qualified Data.Vector.Storable as V
import qualified Data.List as L


class Unconstrained x
instance Unconstrained x

-- | Category with constrained objects
class Cat (ob ∷ k → Constraint) (c ∷ k → k → Type) | c → ob where
    id ∷ ob x ⇒ c x x
    (.) ∷ c y z → c x y → c x z
    -- | Use a morphism @x → y@ in @c@ as a witness of @(ob x, ob y)@
    witness ∷ c x y → ((ob x, ob y) ⇒ a) → a

instance Cat Unconstrained (->) where
    id = F.id
    (.) = (F..)
    witness _ a = a

-- | Cartesian structure (over 'Type', with its free product)
class Cat (ob ∷ Type → Constraint) c ⇒ Cart ob c where
    pr1 ∷ (ob x, ob y) ⇒ c (x,y) x
    pr2 ∷ (ob x, ob y) ⇒ c (x,y) y
    (×) ∷ c x y → c x y' → c x (y,y')                 -- ^K \/

instance Cart Unconstrained (->) where
    pr1 = T.fst
    pr2 = T.snd
    f × g = (,) <$> f <*> g

assocR ∷ (Cart ob c, ob x, ob y, ob z, ob (x,y), ob (y,z)) ⇒ c ((x,y),z) (x,(y,z))
assocR = (pr1 . pr1) × ((pr2 . pr1) × pr2)

assocL ∷ (Cart ob c, ob x, ob y, ob z, ob (x,y), ob (y,z)) ⇒ c (x,(y,z)) ((x,y),z)
assocL = (pr1 × (pr1 . pr2) × (pr2 . pr2))

swap  ∷ (Cart ob c, ob x, ob y) ⇒ c (x,y) (y,x)
swap  = pr2 × pr1

bimap ∷ Cart ob c ⇒ c x y → c x' y' → c (x,x') (y,y')
bimap f g = witness f $ witness g $ (f . pr1) × (g . pr2)

-- | Cartesian structure (for a category on 'Nat's, with '+' as product)
class Cat KnownNat (c ∷ Nat → Nat → Type) ⇒ Cart' c where
    pr1' ∷ (KnownNat n, KnownNat m) ⇒ c (n + m) n
    pr2' ∷ (KnownNat n, KnownNat m) ⇒ c (n + m) m
    (⊙)  ∷ c n m → c n m' → c n (m + m')                -- ^K 0.

bimap' ∷ ∀ c x x' y y'. Cart' c ⇒ c x y → c x' y' → c (x + x') (y + y')
bimap' f g = witness f $ witness g $ (f . pr1') ⊙ (g . pr2')

fromPoints ∷ (Cat ob c, ob x, ob y) 
           ⇒ (∀ t. ob t ⇒ c t x → c t y) → c x y
fromPoints f = f id

fromPoints2 ∷ (Cart ob c, ob x, ob x', ob (x,x'), ob y) 
            ⇒ (∀ t. ob t ⇒ c t x → c t x' → c t y) → c (x,x') y
fromPoints2 f = f pr1 pr2

fromPoints3 ∷ (Cart ob c, ob x, ob x', ob x'', ob (x',x''), ob (x,(x',x'')), ob y)
            ⇒ (∀ t. ob t ⇒ c t x → c t x' → c t x'' → c t y) → c (x,(x',x'')) y
fromPoints3 f = f pr1 (pr1 . pr2) (pr2 . pr2)

fromPoints2' ∷ (Cart' c, KnownNat n, KnownNat n', KnownNat (n + n'), KnownNat m) 
             ⇒ (∀ k. KnownNat k ⇒ c k n → c k n' → c k m) → c (n + n') m
fromPoints2' f = f pr1' pr2'

fromPoints3' ∷ ∀ c n n' n'' m. (Cart' c, KnownNat n, KnownNat n', KnownNat n'', KnownNat (n + n' + n''), KnownNat m)
            ⇒ (∀ k. KnownNat k ⇒ c k n → c k n' → c k n'' → c k m) → c (n + n' + n'') m
fromPoints3' f = f (pr1' @c @n @(n' + n'')) (pr1' @c @n' @n'' . pr2') (pr2' @c @n @n'' . pr2')

toPoints ∷ Cat ob c ⇒ c x y → (∀ t. c t x → c t y)
toPoints f = \x → f . x

-- | infix alias for 'toPoints'
--
-- usage: @ f ▶ x @
(▶) ∷ Cat ob c ⇒ c x y → (∀ t. c t x → c t y)
(▶) = toPoints

infixr 0 ▶

toPoints2 ∷ Cart ob c ⇒ c (x,x') y → (∀ t. ob t ⇒ c t x → c t x' → c t y)
toPoints2 f = \x x' → f . (x × x')

-- | infix alias for 'toPoints2'
--
-- usage: @ x ◀ f $ y @
(◀) ∷ (Cart ob c, ob t) ⇒ c t x → c (x,x') y → c t x' → c t y 
x ◀ f = toPoints2 f x

infixl 1 ◀

toPoints2' ∷ Cart' c ⇒ c (n + n') m → (∀ k. c k n → c k n' → c k m)
toPoints2' f = \x x' → f . (x ⊙ x')

-- | Opposite category of the skeletal category of finite sets 
--
-- The vector @j@ in @(Fin' j ∷ Fin' n m)@ should consist of @m@ integers in the range @[0..n-1]@. This is not enforced statically.
data Fin' (n ∷ Nat) (m ∷ Nat) where
    Fin' ∷ (KnownNat n, KnownNat m) ⇒ V.Vector Int → Fin' n m

intVal ∷ ∀ n. KnownNat n ⇒ Int
intVal = fromIntegral $ natVal (Proxy ∷ Proxy n)

mkFin' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ [Int] → Fin' n m
mkFin' js = let m = intVal @m
                n = intVal @n
                v | L.length js == m && L.all (\j → j >= 0 && j < n) js  
                                 = V.fromList js
                  | otherwise    = error "not a valid map of finite sets"
             in Fin' v   

instance Cat KnownNat Fin' where
    id ∷ ∀ n. KnownNat n ⇒ Fin' n n
    id = Fin' $ V.generate (intVal @n) id
    Fin' j . Fin' k = Fin' $ V.map (k V.!) j
    witness (Fin' _) a = a

instance Cart' Fin' where
    pr1' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Fin' (n + m) n
    pr1' = let n = intVal @n in Fin' $ V.generate n id
    pr2' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Fin' (n + m) m
    pr2' = let n = intVal @n
               m = intVal @m
            in Fin' $ V.generate n $ (m +) . id
    (⊙) ∷ Fin' n m → Fin' n m' → Fin' n (m + m')
    Fin' j ⊙ Fin' k = Fin' $ j V.++ k

-- | Lawvere theory
class Cart' c ⇒ Law c where
    law ∷ Fin' n m → c n m

-- | the @n@-diagonal, using 'law'
expand ∷ ∀ n c. (KnownNat n, Law c) ⇒ c 1 n
expand = let n = intVal @n in law $ Fin' $ V.replicate n 0


class Cat ob c ⇒ Terminal c ob x where
    terminal ∷ ob y ⇒ c y x

