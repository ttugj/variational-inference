{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns #-}

module VI.Inference ( -- * SGD on divergence
                      sgdStep
                    ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Disintegrations

import GHC.Types
import GHC.Num
import GHC.Real
import Control.Monad
import Data.Function    (const)
import Data.Functor



import qualified Numeric.LinearAlgebra.Static as LA

-- | Elementary SGD step, acting on the associated Euclidean space and reporting sampled loss. 
sgdStep  ∷ (Monad m, Domain x, Dim x ~ n) 
         ⇒ Double           -- ^ rate
         → m (Mor x (ℝ 1))  -- ^ loss sampler
         → LA.R n → m (LA.R n, Double)
sgdStep rate loss p = let go (Mor (J φ)) = let (γ, dγ) = φ p
                                               (g, _)  = LA.headTail γ
                                            in (p - LA.konst rate * dγ 1, g)
                       in go <$> loss
           

-- | As in 'sgdStep', but preforms a given number of steps and reports average loss.
sgdSteps ∷ (Monad m, Domain x, Dim x ~ n) 
         ⇒ Int -- ^ number of steps
         → Double 
         → m (Mor x (ℝ 1)) 
         → LA.R n → m (LA.R n, Double)
sgdSteps k rate loss p = bimap id (/ fromIntegral k) <$> go k p 0 where
                            go 0 !q !a = return (q, a)
                            go l !q !a = sgdStep rate loss q >>= \(q', a') → go (l-1) q' (a+a')




