{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns, RecordWildCards #-}

module VI.Inference ( -- * SGD on divergence
                      -- ** Optimiser abstraction
                      Loss, Optimiser, Loss', Optimiser', OptimiserState(..)
                    , chunked
                      -- ** Concrete optimisers
                    , plainSGD
                    , AdamState, AdamParams(..), adamParams, adamSGD
                      -- ** Debugging
                    , monitor, demo
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

-- | Run chunked steps of an optimiser, displaying loss and location.
monitor ∷ ∀ s x. OptimiserState s x
        ⇒ Optimiser' s x      -- ^ optimiser
        → Loss' x             -- ^ loss
        → Maybe (Mor Pt x)    -- ^ initial point
        → Int                 -- ^ chunk size
        → IO ()                             
monitor opt loss init chunk 
        = executeSampleIO $ go s0 p0 0 where
            s0 = initState @s @x
            p0 = case init of
                   Just (Mor (J φ)) → pr1 (φ 0)
                   Nothing → 0
            go ∷ ∀ m. (SampleM m, MonadIO m) ⇒ s → LA.R (Dim x) → Int → m ()
            go s p i = do
                   (s', p', g) ← chunked chunk opt loss s p
                   liftIO . putStrLn . L.unwords $ [ "epoch", show i, "loss", show g, "point", show p' ]
                   go s' p' (i+1)

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
adamParams ∷ AdamParams
adamParams = AdamParams 0.001 0.9 0.999 1.0e-7

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

demo ∷ IO ()
demo = putStrLn "* target: 3.14, 1.00" >> monitor (adamSGD adamParams) loss Nothing 1000
            where
                    loss  ∷ ∀ m. SampleM m ⇒ m (Mor ((ℝ 1, ℝp 1), Pt) (ℝ 1))
                    loss  = divergenceSample variationalFamily posterior
                    variationalFamily ∷ Couple Density Sampler (ℝ 1, ℝp 1) (ℝ 1)
                    variationalFamily = gaussian 
                    posterior ∷ Density Pt (ℝ 1)
                    posterior = let Couple μ _ = variationalFamily 
                                 in pull (real 3.14 × realp 2.72) μ 

