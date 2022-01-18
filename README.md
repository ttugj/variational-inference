# Synopsis 

This library implements an approach to variational inference loosely
following [ADVI](https://arxiv.org/abs/1603.00788) by Kucukelbir _et al._
It is a work in progress, aimed at testing a particular design.

# Background

## Variational inference

Consider the typical computational problem of probabilistic inference:
given a probability distribution μ over some domain, known only via its density
(with respect to some reference measure) up to a (computationally untractable)
normalisation constant, compute statistics such as the expected value of a
given function over the domain.

The distribution may arise from the joint distribution of some probabilistic
model conditioned on observed data, as in Bayesian inference, but other
scenarios are possible as well. One approach to the problem is to sample _directly_
from μ using MCMC methods (expected values are then estimated by averaging over
samples). Another is to _approximate_ μ by a more easily controlled probability distribution,
described by easily interpretable parameters and straightforward to sample from.

In the latter case, one fixes a _variational family_ consisting of distributions ν(θ) parameterised
by some finite-dimensional parameter domain Θ. Mapping θ ∈ Θ to the Kullback-Leibler divergence
between ν(θ) and μ defines a loss function _L_(θ) = _D_(ν(θ)|μ) on Θ,
and ν(argmin _L_) is the resulting variational approximation. Thus the problem is reduced to 
minimising loss, a pure optimisation task.

## ADVI

Variational inference becomes difficult for larger, hierarchical models: given several levels
of priors, composing distributions with constrained parameters (as in the usual parameterisations
of Beta or Gamma), both constructing a variational family that can reasonably well approximate
the target distribution, as well as minimising loss over the variational parameter space, are non-trivial 
to perform and debug. The approach of ADVI is, in a simplified form, to:

1. reparameterise to remove constraints (e.g. apply _log_ to positive parameters, _logit_ to parameters in [0,1], etc.);
2. use a single multivariate normal variational family over the entire unconstrained parameter space (full covariance, or mean field);
3. use the reparameterisation trick and leverage automatic differentiation to sample estimates of loss gradient (parameterising
variational distributions by mean and a Cholesky factor of covariance).

# Design




