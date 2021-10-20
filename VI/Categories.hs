{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, StandaloneKindSignatures, LiberalTypeSynonyms, FunctionalDependencies #-}

module VI.Categories ( Cat(..), Unconstrained
                     , Cart(..), bimap
                     ) where

import Data.Kind
import Data.Tuple
import Data.Functor
import Control.Applicative
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

-- | Cartesian structure
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
