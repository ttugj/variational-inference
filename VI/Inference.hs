{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns #-}

module VI.Inference ( -- * SGD on divergence
                      sgdStep, sgdSteps, sgdMonitor
                    ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Disintegrations

import GHC.Types
import GHC.Classes
import GHC.Num
import GHC.Real
import GHC.Show
import Control.Monad
import Control.Monad.IO.Class
import Data.Function    (const, ($))
import Data.Functor
import Data.Maybe
import System.IO

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Data.List as L

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
         ⇒ Int              -- ^ number of steps
         → Double           -- ^ rate 
         → m (Mor x (ℝ 1))  -- ^ loss sampler
         → LA.R n → m (LA.R n, Double)
sgdSteps steps rate loss p = bimap id (/ fromIntegral steps) <$> go steps p 0 where
                                    go 0 !q !a = return (q, a)
                                    go l !q !a = sgdStep rate loss q >>= \(q', a') → go (l-1) q' (a+a')

-- | Debugging
sgdMonitor ∷ ∀ x. Domain x
           ⇒ Int    -- ^ number of steps per epoch
           → Double -- ^ rate
           → (∀ m. SampleM m ⇒ m (Mor x (ℝ 1))) -- ^ loss sampler
           → Maybe (Mor Pt x)                   -- ^ initial point
           → IO ()
sgdMonitor steps rate loss init
           = executeSampleIO $ go p0 0 where
               p0 = case init of
                      Just (Mor (J φ)) → pr1 (φ 0)
                      Nothing → 0
               go ∷ ∀ m. (SampleM m, MonadIO m) ⇒ LA.R (Dim x) → Int → m ()
               go p i = do
                           (p', g) ← sgdSteps steps rate loss p
                           liftIO . putStrLn . L.unwords $ [ "epoch", show i, "loss", show g, "point", show p' ]
                           go p' (i+1)

sgdDemo ∷ IO ()
sgdDemo = putStrLn "* target: 3.14, 1.00" >> sgdMonitor steps rate loss Nothing
            where
                    steps = 1000
                    rate  = 0.001
                    loss  ∷ ∀ m. SampleM m ⇒ m (Mor ((ℝ 1, ℝp 1), Pt) (ℝ 1))
                    loss  = divergenceSample variationalFamily posterior
                    variationalFamily ∷ Couple Density Sampler (ℝ 1, ℝp 1) (ℝ 1)
                    variationalFamily = gaussian 
                    posterior ∷ Density Pt (ℝ 1)
                    posterior = let Couple μ _ = variationalFamily 
                                 in pull (real 3.14 × realp 2.72) μ 

