{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, StandaloneKindSignatures, LiberalTypeSynonyms, FunctionalDependencies, RankNTypes, ScopedTypeVariables, InstanceSigs, QuantifiedConstraints #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Categories ( -- * Categories
-- | 
-- We model a category in terms of an underlying kind @k@,
-- the type of morphisms @c ∷ k → k → 'Type'@,
-- and a predicate @ob ∷ k → 'Constraint'@ selecting the actual objects.
-- An empty constraint is provided by 'Unconstrained', so that we have
-- e.g. @'Cat' 'Unconstrained' (->)@.
                       Cat(..), Gpd(..), Unconstrained, Terminal(..)
-- * Cartesian categories
-- |
-- For simplicity, we only model Cartesian structure in two situations:
--
--  * for categories with underlying kind 'Type', where the product is represented by the plain tuple type,
--  * for categories with 'KnownNat's as objects, where the product is represented by type-level addition.
--
--  These correspond to the classes 'Cart' and 'Cart''. 
                     , Cart(..), bimap, assocR, assocL, swap
                     , Cart'(..), bimap'
                       -- * Pointed/point-free conversion
-- | 
-- Morphisms in a Cartesian category are conveniently expressed in terms of generalised points:
--
--   * conversion between point-free and pointful representations is facilitated by @fromPoints*@ and @toPoints*@;
--   * a morphism @f ∷ c x y@ can be applied to a generalised point @ξ@ of @x@ using @f '▶' x@;
--   * a morphism @g ∷ c (x,x') y@ can be applied as a binary operation to generalised points @ξ@ of @x@ and @η@ of @y@ using @x '◀' g '$' y@.
--
--   See 'VI.Jets.affine' for an example of this style.
                     , fromPoints, toPoints, fromPoints2, toPoints2, fromPoints2', toPoints2', fromPoints3, fromPoints3'
                     , (▶), (◀)
                       -- * Lawvere theories
-- |
-- We model Lawvere theories as instances @c@ of 'Cart'' together with a lift of every
-- map \( [m] \to [n] \) of finite sets to a morphism in @c n m@. Here \([n]\) stands
-- for the set \( \{0,\dots,n-1\} \). These sets form a skeleton of the category of
-- finite sets, and the opposite category of this skeleton is modeled by 'Fin''.
-- The main example for our purposes is 'VI.Jets.J'.
                     , Fin'(..), mkFin', Law(..), expand
                       -- * Braids

-- |
-- We express canonical isomorphisms in any Cartesian category in terms of the data type
-- 'Braid'. One may think of @'Braid' ob@ as modeling the internal language of the free Cartesian category
-- with objects determined by the predicate @ob ∷ Type → Constraint@. The terms of @'Braid' ob@ can be interpreted
-- in any category @c@ satisfying @'Cart' ob c@ using 'braid'.
                     , Braid(..), braid
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

-- | Groupoid
class Cat ob c ⇒ Gpd ob c where
    inv ∷ c x y → c y x

instance Cat Unconstrained (->) where
    id = F.id
    (.) = (F..)
    witness _ a = a

class Cat ob c ⇒ Terminal ob c x where
    terminal ∷ ob y ⇒ c y x

instance Terminal Unconstrained (->) () where
    terminal _ = ()

-- | Cartesian structure over 'Type', with its free product.
class (Cat (ob ∷ Type → Constraint) c, Terminal ob c (), ∀ x y. (ob x, ob y) ⇒ ob (x, y)) ⇒ Cart ob c where
    pr1 ∷ (ob x, ob y) ⇒ c (x,y) x
    pr2 ∷ (ob x, ob y) ⇒ c (x,y) y
    (×) ∷ c x y → c x y' → c x (y,y')                 -- digraph: ^K \/

instance Cart Unconstrained (->) where
    pr1 = T.fst
    pr2 = T.snd
    f × g = (,) <$> f <*> g

assocR ∷ (Cart ob c, ob x, ob y, ob z) ⇒ c ((x,y),z) (x,(y,z))
assocR = (pr1 . pr1) × ((pr2 . pr1) × pr2)

assocL ∷ (Cart ob c, ob x, ob y, ob z) ⇒ c (x,(y,z)) ((x,y),z)
assocL = pr1 × (pr1 . pr2) × (pr2 . pr2)

swap  ∷ (Cart ob c, ob x, ob y) ⇒ c (x,y) (y,x)
swap  = pr2 × pr1

bimap ∷ Cart ob c ⇒ c x y → c x' y' → c (x,x') (y,y')
bimap f g = witness f $ witness g $ (f . pr1) × (g . pr2)

-- | Cartesian structure (for a category on 'Nat's, with '+' as product)
class (Cat KnownNat (c ∷ Nat → Nat → Type), Terminal KnownNat c 0) ⇒ Cart' c where
    pr1' ∷ (KnownNat n, KnownNat m) ⇒ c (n + m) n
    pr2' ∷ (KnownNat n, KnownNat m) ⇒ c (n + m) m
    (⊙)  ∷ c n m → c n m' → c n (m + m')                -- digraph: ^K 0.

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

instance Terminal KnownNat Fin' 0 where
    terminal = Fin' V.empty

instance Cart' Fin' where
    pr1' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Fin' (n + m) n
    pr1' = let n = intVal @n in Fin' $ V.generate n id
    pr2' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ Fin' (n + m) m
    pr2' = let n = intVal @n
               m = intVal @m
            in Fin' $ V.generate n (m +) 
    (⊙) ∷ Fin' n m → Fin' n m' → Fin' n (m + m')
    Fin' j ⊙ Fin' k = Fin' $ j V.++ k

-- | Lawvere theory
class Cart' c ⇒ Law c where
    law ∷ Fin' n m → c n m

-- | the @n@-diagonal, using 'law'
expand ∷ ∀ n c. (KnownNat n, Law c) ⇒ c 1 n
expand = let n = intVal @n in law $ Fin' $ V.replicate n 0

-- | A redundant encoding of canonical isomorphisms induced by a 'Cart'esian structure over 'Type'
data Braid ob x y where
    BI ∷ ob x ⇒ Braid ob x x
    BC ∷ Braid ob y z → Braid ob x y → Braid ob x z
    Swap ∷ (ob x, ob y) ⇒ Braid ob (x, y) (y, x)
    AssocL ∷ (ob x, ob y, ob z) ⇒ Braid ob (x, (y, z)) ((x, y), z)
    AssocR ∷ (ob x, ob y, ob z) ⇒ Braid ob ((x, y), z) (x, (y, z))
    TermL  ∷ ob x ⇒ Braid ob ((), x) x
    TermL' ∷ ob x ⇒ Braid ob x ((), x)
    TermR  ∷ ob x ⇒ Braid ob (x, ()) x
    TermR' ∷ ob x ⇒ Braid ob x (x, ())
    BraidL ∷ ob x ⇒ Braid ob y z → Braid ob (y,x) (z,x) 
    BraidR ∷ ob x ⇒ Braid ob y z → Braid ob (x,y) (x,z) 

instance (ob (), ∀ x y. (ob x, ob y) ⇒ ob (x, y)) ⇒ Cat ob (Braid ob) where
    id = BI
    (.) = BC
    witness BI a = a
    witness (BC φ ψ) a = witness φ $ witness ψ a
    witness Swap a = a
    witness AssocL a = a
    witness AssocR a = a
    witness TermL a = a
    witness TermL' a = a
    witness TermR a = a
    witness TermR' a = a
    witness (BraidL φ) a = witness φ a
    witness (BraidR φ) a = witness φ a

instance (ob (), ∀ x y. (ob x, ob y) ⇒ ob (x, y)) ⇒ Gpd ob (Braid ob) where
    inv BI = BI
    inv (BC φ ψ) = BC (inv ψ) (inv φ)
    inv Swap = Swap
    inv AssocL = AssocR
    inv AssocR = AssocL
    inv TermL = TermL'
    inv TermL' = TermL
    inv TermR = TermR'
    inv TermR' = TermR
    inv (BraidL φ) = BraidL (inv φ)
    inv (BraidR φ) = BraidR (inv φ)

braid ∷ Cart ob c ⇒ Braid ob x y → c x y
braid BI = id
braid (BC φ ψ) = braid φ . braid ψ
braid Swap = swap
braid AssocL = assocL
braid AssocR = assocR
braid (BraidL φ) = bimap (braid φ) id
braid (BraidR φ) = bimap id (braid φ) 

