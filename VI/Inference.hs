{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections #-}

module VI.Inference ( -- * SGD on divergence
                      sgdStep
                    ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Disintegrations

import GHC.Types
import GHC.Num
import Control.Monad
import Data.Function    (const)
import Data.Functor

import qualified Numeric.LinearAlgebra.Static as LA

-- | Elementary SGD step
sgdStep  ∷ (Monad m, Domain x, Dim x ~ n) 
         ⇒ Double           -- ^ rate
         → m (Mor x (ℝ 1))  -- ^ loss sampler
         → (LA.R n → m (LA.R n))
sgdStep rate loss p = let go (Mor (J φ)) = p - LA.konst rate * pr2 (φ p) 1
                       in go <$> loss
           


