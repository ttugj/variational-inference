{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns, RecordWildCards #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Inference ( -- * SGD on divergence
                      -- ** Optimiser abstractions
                      Loss, Optimiser, Loss', Optimiser', OptimiserState(..)
                    , chunked
                    , Plan(..), defaultPlan
                    , optimise, optimise', optimiseIO, optimiseIO'
                      -- ** Concrete optimisers
                    , plainSGD
                    , AdamState, AdamParams(..), defaultAdamParams, adamSGD
                      -- * Inference models
                      -- ** Bayes
                    , BayesSetup(..), bayesLoss
                    ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Disintegrations

import GHC.Types
import GHC.Classes
import GHC.Num
import GHC.Real
import GHC.Float
import GHC.Show
import Control.Monad
import Control.Monad.IO.Class
import Data.Tuple       (uncurry)
import Data.Function    (const, ($))
import Data.Functor
import Data.Maybe
import System.IO

import qualified Numeric.LinearAlgebra.Static as LA
import qualified Data.List as L

type Loss      m   x = m (Mor x (ℝ 1))
type Optimiser m s x = Loss m x → s → LA.R (Dim x) → m (s, LA.R (Dim x), Double) 

type Loss'        x = ∀ m. SampleM m ⇒ Loss      m   x
type Optimiser' s x = ∀ m. Functor m ⇒ Optimiser m s x

class Domain x ⇒ OptimiserState s x where
    initState ∷ s    

instance Domain x ⇒ OptimiserState () x where
    initState = ()

-- | Perform optimisation steps in chunks, reporting averaged loss.
chunked ∷ Monad m ⇒ Int → Optimiser m s x → Optimiser m s x 
chunked steps opt loss s0 p0 
        = go s0 p0 0 steps where
            go !s !p !adam 0 = return (s, p, adam / fromIntegral steps)
            go !s !p !adam k = do
                                (s',p',g) ← opt loss s p
                                go s' p' (adam+g) (k-1)

-- | Optimisation plan
data Plan = Plan { planThreshold ∷ Double    -- ^ loss threshold
                 , planMaxSteps  ∷ Int       -- ^ max optimisation steps
                 , planChunkSize ∷ Int       -- ^ chunk size for averaging loss and callbacks
                 }

defaultPlan ∷ Plan
defaultPlan = Plan 1.0 100000 1000

-- | Optimise according to plan, terminating once 
-- loss falls below threshold or max number of steps
-- exceeded. 
optimise ∷ ∀ m s x. (SampleM m, OptimiserState s x)
         ⇒ (Point x → Double → m ())   -- ^ callback
         → Plan                        -- ^ optimisation plan
         → Optimiser' s x              -- ^ optimiser
         → Loss' x                     -- ^ loss
         → Maybe (Point x)             -- ^ initial point
         → m (Point x, Double)
optimise cb Plan{..} opt loss init
         = go s0 p0 0 where 
                    s0 = initState @s @x
                    p0 = case init of
                           Just (Mor (J φ)) → pr1 (φ 0)
                           Nothing → 0
                    go s p i = do
                                   (s', p', g) ← chunked planChunkSize opt loss s p
                                   let π = Mor (point p) 
                                   cb π g
                                   if i * planChunkSize < planMaxSteps && g > planThreshold then go s' p' (i+1)
                                                                                            else return (π, g)

-- | 'optimise' without callback
optimise' ∷ (SampleM m, OptimiserState s x)                                 
          ⇒ Plan                         -- ^ optimisation plan
          → Optimiser' s x               -- ^ optimiser
          → Loss' x                      -- ^ loss
          → Maybe (Point x)             -- ^ initial point
          → m (Point x, Double)
optimise' = optimise $ \_ _ → return ()

-- | 'optimise' in 'IO'
optimiseIO ∷ ∀ s x. OptimiserState s x
           ⇒ (∀ m. MonadIO m ⇒ Point x → Double → m ())  -- ^ callback
           → Plan                                         -- ^ optimisation plan
           → Optimiser' s x                               -- ^ optimiser
           → Loss' x                                      -- ^ loss
           → Maybe (Point x)                             -- ^ initial point
           → IO (Point x, Double)
optimiseIO cb plan opt loss init 
           = executeSampleIO α where
                α ∷ ∀ m. (SampleM m, MonadIO m) ⇒ m (Point x, Double)
                α = optimise cb plan opt loss init

-- | 'optimiseIO' without callback
optimiseIO' ∷ ∀ s x. OptimiserState s x
            ⇒ Plan                                        -- ^ optimisation plan
            → Optimiser' s x                              -- ^ optimiser
            → Loss' x                                     -- ^ loss
            → Maybe (Point x)                             -- ^ initial point
            → IO (Point x, Double)
optimiseIO' = optimiseIO $ \_ _ → return () 

-- | Plain constant-rate SGD optimiser
plainSGD ∷ Double → Optimiser' () x
plainSGD rate loss _ p = let go (Mor (J φ)) = let (γ, dγ) = φ p
                                                  (g, _)  = LA.headTail γ
                                               in ((), p - LA.konst rate * dγ 1, g)
                          in go <$> loss

data AdamState x = AdamState { adamGrad1 ∷ !(LA.R (Dim x))
                             , adamGrad2 ∷ !(LA.R (Dim x))
                             , adamWt1   ∷ !Double
                             , adamWt2   ∷ !Double
                             }

updateAdamState ∷ Domain x ⇒ AdamParams → LA.R (Dim x) → AdamState x → AdamState x
updateAdamState AdamParams{..} !δ AdamState{..}
                = AdamState { adamGrad1 = LA.konst β1 * adamGrad1 + LA.konst β1' * δ
                            , adamGrad2 = LA.konst β2 * adamGrad2 + LA.konst β2' * δ * δ
                            , adamWt1   = β1 * adamWt1 + β1'
                            , adamWt2   = β2 * adamWt2 + β2'
                            }
                  where
                          β1   = adamβ1
                          β2   = adamβ2
                          β1'  = 1 - β1
                          β2'  = 1 - β2

getAdamMeans ∷ Domain x ⇒ AdamState x → (LA.R (Dim x), LA.R (Dim x))
getAdamMeans AdamState{..} = (μ1, μ2) where 
                                   μ1 = adamGrad1 / LA.konst adamWt1
                                   μ2 = adamGrad2 / LA.konst adamWt2

instance Domain x ⇒ OptimiserState (AdamState x) x where
    initState = AdamState 0 0 0 0

data AdamParams = AdamParams { adamRate ∷ Double
                             , adamβ1   ∷ Double
                             , adamβ2   ∷ Double
                             , adamε    ∷ Double
                             } 

-- | Default ADAM parameters
defaultAdamParams ∷ AdamParams
defaultAdamParams = AdamParams 0.001 0.9 0.999 1.0e-7

-- | Plain ADAM optimiser
adamSGD ∷ AdamParams → Optimiser' (AdamState x) x 
adamSGD  params@AdamParams{..} loss state p
        = let go (Mor (J φ)) = let (γ, dγ)  = φ p
                                   !δ       = dγ 1
                                   !state'  = updateAdamState params δ state
                                   (μ1,μ2)  = getAdamMeans state'
                                   (g, _)   = LA.headTail γ
                                   rate     = LA.konst adamRate / (LA.konst adamε + sqrt μ2)
                                   !p'      = p - rate * μ1 
                                in (state', p', g)
           in go <$> loss

data BayesSetup lat obs hyp fam = BayesSetup { bayesPrior ∷ Density () hyp
                                             , bayesModel ∷ Density hyp (lat, obs)
                                             , bayesObs   ∷ Point obs
                                             , bayesFam   ∷ Couple Density Sampler fam (hyp, lat)
                                             }

-- | Generic Bayesian loss for a model whose joint domain
-- is a product of hypothesis space, latent space and observed space
bayesLoss ∷ ∀ hyp lat obs fam. (Domain hyp, Domain lat, Domain obs, Domain fam)
            ⇒ BayesSetup lat obs hyp fam → Loss' fam
bayesLoss BayesSetup{..} = let joint ∷ Density () (obs, (hyp, lat)) 
                               joint = pushB @Domain @Mor (Swap . AssocL) $ mix' @Domain @Mor bayesPrior bayesModel
                               post  ∷ Density () (hyp, lat)
                               post  = pull (id × bayesObs) $ pseudoConditional joint   
                               loss  ∷ Loss' fam 
                               loss  = (. osi) <$> divergenceSample bayesFam post
                            in loss 

