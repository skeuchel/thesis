%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt
%include macros.fmt

%if False

> {-# OPTIONS -XRankNTypes -XDeriveFunctor -XFlexibleContexts #-}

> module Effects where

> import Control.Monad.State

> type MAlgebra f a = forall r . (r -> a) -> f r -> a

%endif



%===============================================================================
\section{Modular Monadic Semantics}
\input{src/ModEffects/Figures/FeatureEffects}

% This section presents \Name's solution for modular effects and modular
% effectful reasoning. That solution employs
% \emph{monads}~\cite{moggi89computational,moggi91notions,wadler92essence},
% \emph{monad transformers}~\cite{m} and \emph{algebraic laws}~\cite{m}.  We
% provide the first formalization of a monad transformer library with algebraic
% laws. Some of the algebraic laws, such as the laws for exceptions, were
% previously undocumented in the literature.

% The monad library allows \name to deal with the problem of
% expressing side-effects in semantics in a modular way. It also gives us
% the basic mechanisms which will allow modular reasoning about such
% definitions.\BO{add forward references here?}

Features can utilize the monad library included with \name to
construct algebras for semantic functions which are compatible with a
range of effects. These modular monadic algebras have the form:

< evalRef  :: MonadState Store m => MAlgebra RefF (m a)
< evalErr  :: MonadError () m => MAlgebra ErrF (m a)

\noindent These algebras use monad subclasses such as |MonadState| and
|MonadError| to \emph{constrain} the monad required by the feature,
% Unlike the approach in Section~\ref{m},
allowing the monad to have more effects than those used in the feature.
These two algebras can be combined to create a new evaluation algebra
with type:

< (MonadState m s, MonadError m x) => Mendler (RefF :+: ErrF) (m a)

The combination imposes both type class constraints while
the monad type remains extensible with new effects. The complete set of
effects used by the evaluation functions for the five language
features used in our case study of Section~\ref{sec:CaseStudy} are given in Figure~\ref{fig:FeatureEffects}.


%if False

> data Type = TRef Type | TUnit deriving Eq

> isTRef :: Type -> Maybe Type
> isTRef = undefined

> data Value = Loc Int | Stuck | Unit

> isLoc :: Value -> Maybe Int
> isLoc (Loc n) = Just n

> myLookup :: Int -> [a] -> Maybe a
> myLookup = undefined

> replace :: Int -> a -> [a] -> [a]
> replace = undefined

> fail1 :: Monad m => m a
> fail1 = fail ""

%endif

%-------------------------------------------------------------------------------
\subsection{Example: References}
\input{src/ModEffects/Figures/References_Figure}
\steven{This section needs to explicate that values and computations are two
  distinct sorts unlike SOS where values are a subset of expressions. The typing
  relation is a relation on values only.}
Figure~\ref{fig:references} illustrates this approach with definitions for the
functor for expressions and the evaluation and typing algebras for the
reference feature. Other features have similar definitions.

For the sake of presentation the definitions are slightly simplified from the
actual ones in Coq. For instance, we have omitted issues related to the
extensibility of the syntax for values (|Value|) and types (|Type|).  |Value|
and |Type| are treated as abstract datatypes with a number of smart constructor
functions (c.f. Section \ref{ssec:mod:smartconstructors}): |loc|, |stuck|,
|unit|, |tRef| and |tUnit| denote respectively reference locations, stuck
values, unit values, reference types and unit types. There are also matching
functions |isLoc| and |isTRef| for checking whether a term is a location value
or a reference type, respectively.

The type |RefF| is the functor for references. It has constructors for creating
references (|Ref|), dereferencing (|DeRef|) and assigning (|Assign|)
references. The evaluation algebra |evalRef| uses the state monad for its
reference environment, which is captured in the type class constraint
|MonadState Store m|.  The typing algebra (|typeofRef|) is also monadic, using
the failure monad to denote ill-typing.

% The definition of the algebra is quite straightforward.  itself is standard
% and looks almost like the monolithic version defined over a non-extensible
% expression type.  One small difference is the use of |rec| instead of a
% recursive call. A more significant difference is the use of the observation
% function |isLoc| to simulate a case analysis on values computed in the
% recursive call.

% As discussed in Section~\ref{m} it is the use of these observation functions
% that makes the approach trully modular.\BO{reference?}  In a monolithic
% version a conventional case analysis would have been used instead.

% Similarly to the evaluation algebra, an observation function |isTRef| is used.

%-------------------------------------------------------------------------------
\subsection{Effect-Dependent Theorems}\label{ssec:mod:effectdependenttheorems}
\input{src/ModEffects/Figures/EffectTheorems}

Monadic semantic function algebras are compatible with new effects and algebraic
laws facilitate writing extensible proofs over these monadic algebras. Effects
introduce further challenges to proof reuse, however: each combination of
effects induces its own type soundness statement. Consider the theorem
\LSoundS~in Figure \ref{thm:LSoundS} for a language with references
which features a store $\sigma$ and a store typing $\Sigma$ that are related
through the store typing judgement $\Sigma \vdash \sigma$. The initial store
$\sigma$ is well-formed w.r.t. the initial store typing $\Sigma$, the final
store typing $\Sigma'$ is an extension of the initial one, and the final store
$\sigma'$ is well-formed w.r.t. $\Sigma'$. The |put| operation is used to
constrain the initial and final store of the monadic computation.

Contrast this with the theorem \LSoundE~for a language with errors,
which must account for the computation possibly ending in an exception being
thrown which is modeled by a disjunction in the conclusion.


Clearly, the available effects are essential for the formulation of the
theorem. A larger language which involves both exceptions and state requires yet
another theorem \LSoundES~where the impact of both effects cross-cut one
another\footnote{A similar proliferation of soundness theorems can be found in
  TAPL~\cite{pierce}.}:

% \BO{Wondering whether some additional notes on $\Sigma$ related portions is
% useful.}

Modular formulations of \LSoundS~and \LSoundE~are useless for proving a modular
variant of \LSoundES~because their induction hypotheses have the wrong form. The
hypothesis for \LSoundE~requires the result to be of the form |return v|,
disallowing |put mu >> return v| (the form required by \LSoundS).  Similarly,
the hypothesis for \LSoundS~does not account for exceptions occurring in
subterms. In general, without anticipating additional effects, type soundness
theorems with fixed sets of effects cannot be reused modularly.

\begin{comment}
These type classes and operations enable us to write evaluation
algebras against constrained polymorphic monads:

< evalState  :: MonadState m s => F (m a)  -> m a
< evalExcep  :: MonadError m x => F (m a)  -> m a

These two types are compatible. Combining them, yields the conjunction of the
two type class constraints:

< (MonadState m s, MonadError m x) => (F :+: G) (m a) -> m a

This type is further extensible with new effects.

\BO{Finish section here.}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Basic Definition}
In Haskell, monads are described by a type class:

\begin{spec}
class Monad m where
    return  :: a -> m a
    (>>=)   :: m a -> (a -> m b) -> m b
\end{spec}

The type |m a| describes computations of type |m|
which produce values of type |a| when executed.
The function | return | lifts a value of type |a| into a
(pure) computation that simply produces the value. The \emph{bind} function
| >>= | composes a computation |m a|, which produces values of type |a|,
with a function that accepts a value of type |a| and returns
a computation of type |b|. The convenient function |>>| defines a special case of bind
that discards the intermediate value:

< (>>) :: Monad m => m a -> m b -> m b
< ma >> mb = ma >>= \_ -> mb

The Haskell |do| notation is syntactic sugar for the \textit{bind}
operator: |do { x <- f; g }| means |f >>= \x->g|.



Two particular monads are the state monad |State s| and the exception monad
|Exc x|.  The former which provides two operations |get :: State s s| and |put
:: s -> State s ()| for reading and writing a state. The latter provides |throw
:: x -> Exc x a| for throwing an exception and |catch :: Exc x a -> (x -> Exc x
a) -> Exc x a|. These enable us to write evaluation algebras of type:

< evalState  :: F (State s a)  -> State s a
< evalExcep  :: F (Exc x a)    -> Exc x a

The two types are now much more similar in structure, but still not compatible
because neither supports the effects of the other.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Abstractions}

In order to allow extensible effects we need abstract over the particular monad
implementation used. Any implementation is valid as long as it supports the
required operations. These requirements are captured in type classes such as
|MonadState| and |MonadError|, also called \emph{monad subclasses}. Note that
classes such as |MonadState s m| use \emph{functional
dependencies}~\cite{jones00type}. The annotation | m -> s| states that there is
a functional dependency between the type |m| and |s| (the type |m| determines
the type |s|). This additional information is used by the compiler to improve
type-inference.

These type classes enable us to write evaluation algebras against constrained
polymorphic monads:

< evalState  :: MonadState m s => F (m a)  -> m a
< evalExcep  :: MonadError m x => F (m a)  -> m a

These two types are compatible. Combining them, yields the conjunction of the
two type class constraints:

< (MonadState m s, MonadError m x) => (F :+: G) (m a) -> m a

This type is further extensible with new effects.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Modular Monad Definitions}

In order to instantiate a closed language with multiple effects, we must supply
a monad definition that implements all the required effects. We could write a
new definition from scratch, but it is much more convenient to reuse existing
implementations for individual effects. This is where \emph{monad transformers}
come in.

A monad transformer~\cite{liang95monad} is a higher-order monad that is
parameterized by another monad. It layers two kinds of monads on top of each
other to compose their functionality A monad transformer is defined by the
following type class:

%format MyMonadTrans  = MonadTrans
%format mylift        = lift
%format MyStateT      = StateT
%format runMyStateT   = runStateT

< class MonadTrans t where
<     lift :: Monad m => m a -> t m a

%if False
\begin{figure}

< newtype StateT s m a = StateT {
<   runStateT :: s -> m (a,s)
< }
<
< instance MonadTrans (StateT s) where
<    lift p = StateT $ \s -> do {a <- p; return (a, s)}
<
< instance Monad m => Monad (StateT s m) where
<    return a = StateT $ \s -> return (a, s)
<    p >>= k  = StateT $ \s -> do
<        (a, s') <- runStateT p s
<        runStateT (k a) s'
<
< class Monad m => MonadState s m | m -> s where
<     get :: m s
<     put :: s -> m ()
<
< instance (Monad m) =>
<  MonadState s (StateT s m) where
<    get   = StateT $ \s -> return (s, s)
<    put s = StateT $ \_ -> return ((), s)

\caption{State monad transformer machinery.}\label{fig:statet}

\label{fig:error}

\end{figure}
%endif

\noindent The | lift | operation  takes a monadic computation | m a |,
and lifts it into the transformed monad | t m | For each particular type
of effect (such as state or exceptions) there is an associated monad transformer
type and type class.

%-------------------------------------------------------------------------------
\subsection{Monads and Modular Reasoning}

While constrained polymorphic monads are quite convenient for modularizing side
effects in function algebras, they are problematic for reasoning. The
constrained polymorphism abstracts the behavior of the effectful operations
into an interface. When looking at a feature in isolation, we do not know what
implementation is used for its side effects. This is only known for fully
composed languages, and the implementation used may be different for different
languages. That leaves very little room for modular reasoning.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Monad Laws}
Fortunately, this problem is partly mitigated by the \emph{laws}. These laws
are an integral part of the definition of the monadic type classes and
constrain the possible implementations to sensible ones. Hence, without
knowing the particular implementation of a type classes used, we can still rely
on its laws for reasoning purposes.

For example, |Monad| instances must satisfy the following laws:
\begin{IEEEeqnarray*}{rCl"s}
| return x >>= f|  & ~~|==|~~ & |f x|                      & \textsc{(Return-Bind)} \\
| p >>= return |   & |==| & |p|                        & \textsc{(Bind-Return)} \\
| (p >>= f) >>= g |& |==| & |p >>= \x -> (f x >>= g)|  & \textsc{(Bind-Bind)}
\end{IEEEeqnarray*}
and |MonadState| instances must satisfy 5 more laws:
\begin{IEEEeqnarray*}{rCl"s}
| get >> m |  & ~~|==|~~ & |m|                      & \textsc{(Get-Query)} \\
| put s >> get |  & ~~|==|~~ & |put s >> return s|                      & \textsc{(Put-Get)} \\
| get >>= put |  & ~~|==|~~ & |return ()|                      & \textsc{(Get-Put)} \\
| get >>= \s -> get >>= f s | & |==| & |get >>= \s -> f s s |      & \textsc{(Get-Get)} \\
| put s1 >> put s2 | & |==| & |put s2| & \textsc{(Put-Put)}
\end{IEEEeqnarray*}
The Haskell language is not equipped to express, enforce and exploit type class
laws, but Coq does. Hence, we have provided our monadic type classes in Coq with a full
complement of laws, about 30 in total.

These laws play a crucial role in all the proofs over constrained polymorphic
monadic algebras.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Effect-Dependent Theorems}

Even though we now have reusable function algebras thanks to monads, and we can
write proofs about these algebras thanks to laws, the proofs themselves are not
necessarily reusable. In fact, the proofs for a property like type soundness
are inherently not reusable. The problem is that each combination of effects
requires its own type soundness statement~\cite{pierce}. Consider the theorem for exceptions:

\begin{gather*}\forall e, t. |typeof e| = |return t|
    \rightarrow \\ (\exists v. |eval e| = |return v| \wedge \vdash v : t) \vee (\exists x. |eval e| = |throw x|)
\end{gather*}

and that for state:

%format Sigma = "\Varid{\Sigma}"
%format sigma = "\Varid{\sigma}"
%format sigma' = "\Varid{\sigma'}"
\tom{Ben, have a look at the use of local here.}
\begin{gather*}
\forall e, t, \Sigma, \sigma.
    \left\{\begin{array}{c}
    | local (const Sigma) (typeof e) = return t | \\
    \Sigma \vdash \sigma
    \end{array}\right\} \\
 \rightarrow \\
  \exists v, \Sigma', \sigma'.
   \left\{\begin{array}{c}
   |put sigma >> eval e| = |put sigma' >> return v| \\
   \Sigma' \supseteq \Sigma \\
   \Sigma' \vdash v : t \\
   \Sigma' \vdash \sigma'
   \end{array}\right\}
\end{gather*}

Clearly, the available effects are essential for the formulation of the
theorem. If we build a larger language that involves both effects, then
we need to write a new theorem where the elements of both are cross-cutting one
another.

\tom{Show the combined theorem here.}

Neither of the two above theorems is useful for proving the new theorem. The former
does not mention the state and the latter does not allow for failure.

\tom{some sentence(s) to explain this is a general issue and a big challenge}

In general,
without anticipating or restricting the possible effects, there is no strongest
possible type soundness property.

In summary, it seems that we monads give us modularly reusable functions but
not proofs.
\end{comment}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
