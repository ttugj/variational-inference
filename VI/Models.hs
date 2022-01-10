{-# LANGUAGE UnicodeSyntax, PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, ConstraintKinds, TypeApplications, AllowAmbiguousTypes, NoImplicitPrelude, UndecidableInstances, NoStarIsType, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, LiberalTypeSynonyms, ScopedTypeVariables, InstanceSigs, DefaultSignatures, RankNTypes, TupleSections, BangPatterns, RecordWildCards #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module VI.Models ( -- * Models
        -- 
        -- | This module will contain a collection of loosely related models,
        -- mostly to serve as examples.   
                   linearRegression
                 ) where

import VI.Categories
import VI.Jets
import VI.Domains
import VI.Disintegrations
import VI.Inference

import GHC.TypeNats
import GHC.Classes
import GHC.Num  
import Data.Function (($))

-- | A simple Bayesian linear regression model.
--
-- Specification:
--
-- * data: \((x_i, y_i)_{1 \le i \le n}\) with \(x_i \in \mathbb{R}^d\), \(y_i\in\mathbb{R}\)
-- * parameters: \(w \in \mathbb{R}^d\), \(\sigma\in\mathbb{R}_{>0}\)
-- * model: \( y_i = w^* x_i + \epsilon_i\), with iid \(\epsilon_i \sim \mathcal{N}(w x_i, \sigma^2)\)
-- * prior: \( w \sim \mathcal{N}(0, c^2 I)\), \( \sigma^{-2} \sim \mathrm{Gamma}(a,b)\)
linearRegression ∷ ∀ d n hyp fam cov. ( KnownNat d, KnownNat n
                                      , hyp ~ (ℝ d, ℝp 1)
                                      , cov ~ Σp (Dim hyp)  
                                      , fam ~ (hyp, cov)
                                      )
                 ⇒ Point ((ℝp 1, ℝp 1), ℝp 1) -- ^ hyperparameters @((a,b),c)@
                 → Point (M n d, ℝ n)         -- ^ data 
                 → BayesSetup () (ℝ n) hyp fam
linearRegression hyper xy = let bayesPrior = prior 
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
 
 
