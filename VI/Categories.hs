{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, StandaloneKindSignatures, LiberalTypeSynonyms, FunctionalDependencies, RankNTypes #-}

module VI.Categories ( -- * Categories
                       Cat(..), Unconstrained
                       -- * Cartesian categories
                     , Cart(..), bimap
                     , Cart'(..), bimap'
                       -- * Pointed/point-free conversion
                     , fromOp1, toOp1, fromOp2, toOp2, fromOp2', toOp2'
                     ) where

import Data.Kind
import Data.Tuple
import Data.Functor
import Control.Applicative
import GHC.TypeLits
import qualified Data.Function as F

class Unconstrained x
instance Unconstrained x

-- | Category with constrained objects
class Cat (ob ∷ k → Constraint) (c ∷ k → k → Type) | c → ob where
    id ∷ ob x ⇒ c x x
    (.) ∷ c y z → c x y → c x z

instance Cat Unconstrained (->) where
    id = F.id
    (.) = (F..)

-- | Cartesian structure (with free product)
class Cat ob c ⇒ Cart ob c where
    pr1 ∷ (ob x, ob y, ob (x,y)) ⇒ c (x,y) x
    pr2 ∷ (ob x, ob y, ob (x,y)) ⇒ c (x,y) y
    (×) ∷ c x y → c x y' → c x (y,y')

instance Cart Unconstrained (->) where
    pr1 = fst
    pr2 = snd
    f × g = (,) <$> f <*> g

bimap ∷ (Cart ob c, ob x, ob x', ob (x,x')) ⇒ c x y → c x' y' → c (x,x') (y,y')
bimap f g = (f . pr1) × (g . pr2)

-- | Cartesian structure (for a category on 'Nat's, with '+' as product)
class Cat KnownNat (c ∷ Nat → Nat → Type) ⇒ Cart' c where
    pr1' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ c (n + m) n
    pr2' ∷ ∀ n m. (KnownNat n, KnownNat m) ⇒ c (n + m) m
    (⊙) ∷ c n m → c n m' → c n (m + m')

bimap' ∷ (Cart' c, KnownNat x, KnownNat x', KnownNat (x + x')) ⇒ c x y → c x' y' → c (x + x') (y + y')
bimap' f g = (f . pr1') ⊙ (g . pr2')

fromOp1 ∷ (Cat ob c, ob x, ob y) ⇒ (∀ t. ob t ⇒ c t x → c t y) → c x y
fromOp1 f = f id

fromOp2 ∷ (Cart ob c, ob x, ob x', ob (x,x'), ob y) ⇒ (∀ t. ob t ⇒ c t x → c t x' → c t y) → c (x,x') y
fromOp2 f = f pr1 pr2

fromOp2' ∷ (Cart' c, KnownNat n, KnownNat n', KnownNat (n + n'), KnownNat m) ⇒ (∀ k. KnownNat k ⇒ c k n → c k n' → c k m) → c (n + n') m
fromOp2' f = f pr1' pr2'

toOp1 ∷ Cat ob c ⇒ c x y → (∀ t. c t x → c t y)
toOp1 f = \x → f . x

toOp2 ∷ Cart ob c ⇒ c (x,x') y → (∀ t. c t x → c t x' → c t y)
toOp2 f = \x x' → f . (x × x')

toOp2' ∷ Cart' c ⇒ c (n + n') m → (∀ k. c k n → c k n' → c k m)
toOp2' f = \x x' → f . (x ⊙ x')
