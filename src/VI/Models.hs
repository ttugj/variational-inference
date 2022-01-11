{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns, RecordWildCards, PartialTypeSignatures #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Models ( -- * Models
        -- 
        -- | This module will contain a collection of loosely related models,
        -- mostly to serve as examples.   
                   linearRegressionModel, linearRegressionExec
                 ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Disintegrations
import VI.Inference
import VI.Util              (fromLtoR)

import Data.Semigroup
import Data.Maybe    
import GHC.TypeNats
import GHC.Classes
import GHC.Num  
import GHC.Float
import GHC.Show
import Data.Function (($))
import Control.Monad
import Control.Monad.IO.Class
import System.IO

import qualified Numeric.LinearAlgebra.Static as LA

-- | A simple Bayesian linear regression model.
--
-- Specification:
--
-- * data: \((x_i, y_i)_{1 \le i \le n}\) with \(x_i \in \mathbb{R}^d\), \(y_i\in\mathbb{R}\)
-- * parameters: \(w \in \mathbb{R}^d\), \(\sigma\in\mathbb{R}_{>0}\)
-- * model: \( y_i = w^* x_i + \epsilon_i\), with iid \(\epsilon_i \sim \mathcal{N}(w x_i, \sigma^2)\)
-- * prior: \( w \sim \mathcal{N}(0, c^2 I)\), \( \sigma^{-2} \sim \mathrm{Gamma}(a,b)\)
linearRegressionModel ∷ ∀ d n hyp fam cov. ( KnownNat d, KnownNat n
                                           , hyp ~ (ℝ d, ℝp 1)
                                           , cov ~ Σp (Dim hyp)  
                                           , fam ~ (hyp, cov)
                                           )
                      ⇒ Point ((ℝp 1, ℝp 1), ℝp 1) -- ^ hyperparameters @((a,b),c)@
                      → Point (M n d, ℝ n)         -- ^ data 
                      → BayesSetup () (ℝ n) hyp fam
linearRegressionModel hyper xy 
                      = let bayesPrior = prior 
                            bayesModel = pushOsi model 
                            bayesObs   = pr2 . xy
                            bayesFam   = pushOsi genericGaussian
                         in BayesSetup{..}
                            where
                                x ∷ ∀ t. Domain t ⇒ Mor t (M n d)
                                x = pr1 . xy . terminal
                                model ∷ Density hyp (ℝ n)
                                model = let f ∷ Mor hyp (ℝ n, ℝp n)
                                            f = bimap (fromPoints $ \y → x ∙ y) (Mor expand)
                                            μ = gaussianD @n @(ℝp n) 
                                         in pull @Domain @Mor f μ 
                                prior ∷ Density () hyp 
                                prior = let μ ∷ Density () (ℝ d)
                                            μ = pull (basePoint × (Mor expand . pr2 . hyper)) $ gaussianD @d @(ℝp d)
                                            ν ∷ Density () (ℝp 1)
                                            ν = pull (pr1 . hyper) $ reparam (inv stdToPrecision) gammaD
                                         in μ ◎ ν   

-- | Fit a 'linearRegressionModel' using 'adamSGD' with default settings,
-- and return mean and covariance of regression weights.
linearRegressionExec ∷ ∀ d n. (KnownNat d, KnownNat n)
                     ⇒ Double
                     → Double
                     → Double
                     → LA.L n d
                     → LA.R n
                     → IO (LA.R d, LA.Sym d)
linearRegressionExec a b c x y
                     = do
                         let model = linearRegressionModel @d @n ((realp a × realp b) × realp c) ((Mor . point . fromLtoR $ x) × fromConcrete y)
                             loss  ∷ Loss' _
                             loss  = bayesLoss model 
                             opt   ∷ Optimiser' _ _
                             opt   = adamSGD defaultAdamParams 
                             cb _ h = liftIO $ putStrLn $ "loss: " <> show h
                         (p,_) ← optimiseIO cb defaultPlan opt loss Nothing 
                         let 
                             wts  = pr1 . pr1 . p
                             cov  = pr2 . p
                         return (getPoint wts, LA.sym . blk . getMatrix $ emb @(Σ (d + 1)) . emb . cov)

                        where

                            blk ∷ LA.Sq (d + 1) → LA.Sq d
                            blk m = let (m', _) = LA.splitRows @d @(d + 1) @(d + 1) m
                                        (m'',_) = LA.splitCols @d @d       @(d + 1) m'
                                     in m''


