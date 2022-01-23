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
described by immediately interpretable parameters and straightforward to sample from.

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
to perform and debug. The ADVI recipe is, in a simplified form, to:

1. reparameterise to remove constraints (e.g. apply _log_ to positive parameters, _logit_ to parameters in [0,1], etc.);
2. use a single multivariate normal variational family over the entire unconstrained parameter space (full covariance, or mean field);
3. use the reparameterisation trick and leverage automatic differentiation to sample estimates of loss gradient (parameterising
variational distributions by mean and a Cholesky factor of covariance).

# Design

## Mathematical model

Given a sufficiently rich category of spaces __C__, it is most convenient to formalise probability theory
in terms of a monad _P_ : __C__ → __C__, with _PX_ interpreted as the space of probability distributions on _X_.
This is too much to hope for in our context.

First, since we need automatic differentiation, we'll work over a
much more restricted category of _domains_ (in a first approximation equivalent to the category of Cartesian
spaces and smooth maps). We thus lose representability, weakening _P_ to a profunctor _p_:__C__° × __C__ → __Set__,
with _p_(_X_,_Y_) interpreted as the set of families of probability distributions over _Y_ parameterised by _X_.
In fact, our category will be Cartesian, and the profunctor _p_ would then be an _arrow_ (in the usual Haskell sense),
a shadow of _P_ being a monad.

However, since marginals are in general intractable, we do not even have functoriality in the second argument of _p_!
Likewise, there are no composition maps _p_(_X_,_Y_) × _p_(_Y_,_Z_) → _p_(_X_,_Z_). Instead, _p_(_X_,-) is functorial only
with respect to canonical isomorphisms induced by the Cartesian structure (generated by symmetry and associativity of the
product), while composition is replaced by general mixture maps 
_p_(_X_,_Y_) × _p_(_X_ × _Y_, _Z_) → _p_(_X_, _Y_ × _Z_). The latter allow us to construct _joint_ distributions over all intermediate
variables instead of a marginal distribution over some final subset thereof.

These properties give rise to what we'll call a _quasiarrow_. First, let __C__ be a Cartesian category,
and CartIso(__C__) → __C__ be the groupoid of isomorphisms in the free Cartesian category on Ob(__C__),
together with a Cartesian embedding, identity on Ob(__C__) ⊂ Ob(CartIso(__C__)).
Then a _quasiarrow_ on __C__ is a map _p_ : __C__° × __C__ → __Set__ together with:

1. pullback maps __C__(_X'_,_X_) × _p_(_X_,_Y_) → _p_(_X'_,_Y_) extending _p_(-,_Y_) to a presheaf on __C__,
2. mixture maps _p_(_X_,_Y_) × _p_(_X_ × _Y_, _Z_) → _p_(_X_, _Y_ × _Z_),
3. pushforward maps CartIso(__C__)(_Y_,_Y'_) × _p_(_X_,_Y_) → _p_(_X_,_Y_') extending the restriction of _p_(_X_,-) to
a set-valued functor on CartIso(__C__);

satisfying natural compatibility conditions: pullbacks commute with pushforwards, mixtures are compatible with both pullbacks
and pushforwards, and furthermore associative in the sense that the two composites
mix ∘ (mix × id), mix ∘ (id × mix): _p_(_X_,_Y_) × _p_(_X_×_Y_,_Z_) × _p_(_X_×_Y_×_Z_,_W_) → _p_(_X_,_Y_×_Z_×_W_)
coincide (where we implicitly use functoriality of _p_(_X_,-) with respect to CartIso(__C__) to disambiguate iterated products).

## Implementation 

### `VI.Categories`
### `VI.Jets`
### `VI.Domains`
### `VI.Quasiarrows`
### `VI.Inference`

