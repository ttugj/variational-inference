{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns #-}

module VI.Inference ( -- * SGD on divergence
                      Loss, Optimiser, OptimiserState(..)
                    , chunked, monitor
                    , plainSGD
                    , demo
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

type Loss      m   x = m (Mor x (ℝ 1))
type Optimiser m s x = Loss m x → s → LA.R (Dim x) → m (s, LA.R (Dim x), Double) 

class Domain x ⇒ OptimiserState s x where
    initState ∷ s    

instance Domain x ⇒ OptimiserState () x where
    initState = ()

-- | Perform optimisation steps in chunks, reporting averaged loss.
chunked ∷ Monad m ⇒ Int → Optimiser m s x → Optimiser m s x 
chunked steps opt loss s0 p0 
        = go s0 p0 0 steps where
            go !s !p !acc 0 = return (s, p, acc / fromIntegral steps)
            go !s !p !acc k = do
                                (s',p',g) ← opt loss s p
                                go s' p' (acc+g) (k-1)

-- | Run chunked steps of an optimiser, displaying loss and location.
monitor ∷ ∀ s x. OptimiserState s x
        ⇒ (∀ m. Functor m ⇒ Optimiser m s x)
        → (∀ m. SampleM m ⇒ Loss m x) 
        → Maybe (Mor Pt x)
        → Int
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

-- | A plain constant-rate SGD optimiser
plainSGD ∷ Functor m 
         ⇒ Double  -- ^ rate
         → Optimiser m () x
plainSGD rate loss _ p = let go (Mor (J φ)) = let (γ, dγ) = φ p
                                                  (g, _)  = LA.headTail γ
                                               in ((), p - LA.konst rate * dγ 1, g)
                          in go <$> loss

demo ∷ IO ()
demo = putStrLn "* target: 3.14, 1.00" >> monitor (plainSGD 0.001) loss Nothing 1000
            where
                    loss  ∷ ∀ m. SampleM m ⇒ m (Mor ((ℝ 1, ℝp 1), Pt) (ℝ 1))
                    loss  = divergenceSample variationalFamily posterior
                    variationalFamily ∷ Couple Density Sampler (ℝ 1, ℝp 1) (ℝ 1)
                    variationalFamily = gaussian 
                    posterior ∷ Density Pt (ℝ 1)
                    posterior = let Couple μ _ = variationalFamily 
                                 in pull (real 3.14 × realp 2.72) μ 

