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




Definition RefF_evalM (R : Set) (rec : R -> evalMR V ME)
     (e : RefF R) : evalMR V ME :=
       match e with
         | Ref e =>
           do v <- (rec e);
             do env <- get;
               put (insert _ v env) >> return_ (loc' (length env))
         | DeRef e =>
           do v <- (rec e);
             match isLoc (proj1_sig v) with
               | Some n => do env <- get;
                 return_ match (@lookup Value env n) with
                           | Some mv => mv
                           | _ => stuck' 457
                         end
               | None => return_ (stuck' 456)
             end
         | Assign e1 e2 =>
           do v <- (rec e1);
             match isLoc (proj1_sig v) with
               | Some n =>
                 do v2 <- rec e2;
                   do env <- get;
                     put (replace_el n v2 env) >> return_ unit'
               | None => return_ (stuck' 3)
             end
       end.



%endif

%===============================================================================

\input{src/ModularEffects/3MT_Overview_Figure}


\section{The \name Monad Library}

\name includes a monad library to support effectful semantic
functions using \emph{monads} and \emph{monad transformers}, and
provides \emph{algebraic laws} for reasoning.
Monads provide a uniform representation for encapsulating
computational effects such as mutable state, exception handling, and
non-determinism. Monad transformers allow monads supporting the desired set of
effects to be built. Algebraic laws are the key to \emph{modular} reasoning about
monadic definitions.

\name implements the necessary definitions of \emph{monads} and
\emph{monad transformers} as a Coq library inspired by the Haskell
\emph{monad transformer library} (MTL)~\cite{liang95monad}. Our
library refines the MTL in two key ways in order to support modular
reasoning using algebraic laws. While algebraic laws can only be
documented informally in Haskell, our library fully integrates them
into type class definitions using Coq's expressive type
system. Additionally, \name systematically includes laws for all
monad subclasses, several of which have not been covered in the
functional programming literature before.

% TOM: This is not very important:
%
% Although the port of the MTL definitions was mostly straightforward
% a notable difference is that the port does not use functional dependencies~\cite{jones00type}.
% The reason is simply that Coq's implementation of type classes does
% not support functional dependencies. However the use of functional
% dependencies is mostly for convenience: in Haskell it allows the compiler to
% improve type-inference. Since in Coq there is a lot less type-inference and
% type annotations are most often required anyway, the lack of functional dependencies
% is not a significant drawback.


\paragraph{Library overview}
Figure~\ref{fig:reference} summarizes the library's key classes, definitions
and laws. The type class |Monad| describes the basic interface of monads.  The
type |m a| denotes computations of type |m| which produce values of type |a|
when executed.  The function | return | lifts a value of type |a| into a (pure)
computation that simply produces the value. The \emph{bind} function | >>= |
composes a computation |m a| producing values of type |a|, with a
function that accepts a value of type |a| and returns a computation of type
|m b|. The function |>>| defines a special case of bind that discards
the intermediate value:

< (>>) :: Monad m => m a -> m b -> m b
< ma >> mb = ma >>= \_ -> mb

The |do| notation is syntactic sugar for the \textit{bind}
operator: |do { x <- f; g }| means |f >>= \x->g|.

Particular monads can be built from basic monad types such as the
identity monad (|Identity|) and monad transformers including the
failure (|FailT|), mutable state (|StateT|), and exception (|ErrorT|)
transformers. These transformers are combined into different monad
stacks with |Identity| at the bottom. Constructor and extractor
functions such as |StateT| and |runStateT| provide the signatures of
the functions for building and running particular
monads/transformers.

In order to support extensible effects, a feature needs to abstract
over the monad implementation used. Any implementation which includes
the required operations is valid. These operations are captured in
type classes such as |MonadState| and |MonadError|, also called
\emph{monad subclasses}.  The type classes (denoted by subscript M)
are used to require a monad stack to support a
particular effect without assuming a particular stack
configuration.\footnote{Supporting two instances of the same effect
requires extra machinery~\cite{zipper}.} Each class offers a set of
primitive operations, such as |get| to access the state for
|MonadState|.

\paragraph{Algebraic laws} Each monad (sub)class includes a set of
algebraic laws that govern its operations.  These laws are an integral
part of the definition of the monad type classes and constrain the
possible implementations to sensible ones. Thus, even without knowing
the particular implementation of a type class, we can still modularly
reason about its behavior via these laws. This is crucial for
supporting modular reasoning~\cite{effectiveadvice}.

The first three laws for the |Monad| class are standard, while the
last law (|fmap_bind|) relates |fmap| and |bind| in the usual way.
Each monad subclass also includes its own set of laws. The laws for
various subclasses can be found scattered throughout the functional
programming literature, such as for failure~\cite{gibbons11just} and
state~\cite{effectiveadvice,gibbons11just}. Yet, as far as we know,
\name is the first to systematically bring them together. Furthermore, although most
laws have been presented in the semantics literature in one form or another, we have not
seen some of the laws in the functional programming literature.
One such example are the laws for the exception class:

\begin{itemize}
\item The |bind_throw| law generalizes the |bind_fail| law: a sequential
      computation is aborted by throwing an exception.
\item The |catch_throw1| law states that the exception handler is invoked
      when an exception is thrown in a |catch|.
\item The |catch_throw2| law indicates that an exception handler is redundant
      if it just re-throws the exception.
\item The |catch_return| law states that a |catch| around a pure computation is redundant.
\item The |fmap_catch| law states that pure functions (|fmap f|) distribute on the right
      with |catch|. %This is obviously not true for impure computations.
\end{itemize}

% \paragraph{Exception Laws}
%  There
% are two laws for this interaction. The |catch_throw| law specifies that when
% the handler function (the second argument of |catch|) is |throw| then the
% computation |m|, which is been handled, should be returned. Intuitively, the
% exceptional value for the |throw| operation is simply the value yielded by |m|,
% so the resulting computation of throwing that value should just be equivalent
% to |m|.  The |catch_throw'| specifies that handling a thrown exception, should
% result in applying the handle function |h| to the exceptional value. The
% interaction between |catch| and |return| is also important and captured by the
% |catch_return| law: if a computation is pure then it does not throw exceptions,
% and there trying to catch an exception should have no effect on the original
% computation. Finally, there is also an interaction between |fmap| and |catch|
% (the law |fmap_catch|), which essentially expresses that |fmap| and |catch|
% distribute over each other.

\paragraph{Other definitions} Our monad library contains a number of
other classes, definitions and laws apart from the definitions
discussed here. This includes infrastructure for other types of
effects (e.g. writer effects), as well as other infrastructure from
the MTL.  There are roughly 30 algebraic laws in total.
%The complete code for \name can be found in the online repository.

\input{src/ModularEffects/References_Figure}

%===============================================================================
\section{Modular Monadic Semantics}

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

\input{src/ModularEffects/FeatureEffects}

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
Figure~\ref{fig:references} illustrates this approach with definitions for the
functor for expressions and the evaluation and typing algebras for the
reference feature. Other features have similar definitions.

For the sake of presentation the definitions are slightly simplified
from the actual ones in Coq. For instance, we have omitted issues
related to the extensibility of the syntax for values (|Value|) and
types (|Type|).  We refer the interested reader to MTC~\cite{mtc} and
the \name Coq code for these details.  |Value| and |Type| are treated
as abstract datatypes with a number of constructor functions: |loc|,
|stuck|, |unit|, |tRef| and |tUnit| denote respectively reference
locations, stuck values, unit values, reference types and unit
types. There are also matching functions |isLoc| and |isTRef| for
checking whether a term is a location value or a reference type,
respectively.

The type |RefF| is the functor for references. It has
constructors for creating references (|Ref|), dereferencing (|DeRef|) and
assigning (|Assign|) references. The evaluation algebra |evalRef| uses
the state monad for its reference environment, which is captured
in the type class constraint |MonadState Store m|.  The typing algebra
(|typeofRef|) is also monadic, using the failure monad to denote
ill-typing.

% The definition of the algebra is quite straightforward.
% itself is standard and looks almost like the monolithic version
% defined over a non-extensible expression type.  One small difference
% is the use of |rec| instead of a recursive call. A more significant
% difference is the use of the observation function |isLoc| to
% simulate a case analysis on values computed in the recursive call.
% As
% discussed in Section~\ref{m} it is the use of these observation
% functions that makes the approach trully modular.\BO{reference?}  In a
% monolithic version a conventional case analysis would have been used
% instead.

% Similarly to the
% evaluation algebra, an observation function |isTRef| is used.

%-------------------------------------------------------------------------------
\subsection{Effect-Dependent Theorems}

Monadic semantic function algebras are compatible with new effects and
algebraic laws facilitate writing extensible proofs over these monadic
algebras. Effects introduce further challenges to proof reuse,
however: each combination of effects induces its own type soundness
statement. Consider the theorem for a language with references which
features a store $\sigma$ and a store typing $\Sigma$ that are related
through the store typing judgement $\Sigma \vdash \sigma$:

%format Sigma = "\Varid{\Sigma}"
%format mu = "\sigma''"
%format sigma = "\Varid{\sigma}"

\vspace{2mm}
\noindent\fbox{
\begin{minipage}{.93\columnwidth}
\begin{gather*}
\forall e, t, \Sigma, \sigma.
    \left\{\begin{array}{c}
    | typeof e == return t | \\
    \Sigma \vdash \sigma
    \end{array}\right\} \rightarrow \\
  \exists v, \Sigma', \sigma'.
   \left\{\begin{array}{c}
   |put sigma >> eval e == put mu >> return v| \\
   \Sigma' \supseteq \Sigma \\
   \Sigma' \vdash v : t \\
   \Sigma' \vdash \sigma'
   \end{array}\right\}
\tag{\textsc{LSound}$_S$}
\label{thm:SoundS}
\end{gather*}
\end{minipage}
}
\vspace{2mm}

\noindent Contrast this with the theorem for a language with errors,
which must account for the computation possibly ending in an exception
being thrown:

\vspace{2mm}
\noindent\fbox{
\begin{minipage}{.93\columnwidth}
\begin{gather*}\forall e, t. |typeof e == return t|
    \rightarrow \\ (\exists v. |eval e == return v| \wedge \vdash v : t) \vee (\exists x. |eval e == throw x|)
\tag{\textsc{LSound}$_E$}
\label{thm:SoundE}
\end{gather*}
\end{minipage}
}

\vspace{2mm}


Clearly, the available effects are essential for the formulation of
the theorem. A larger language which involves both exceptions and
state requires yet another theorem where the impact of both effects
cross-cut one another\footnote{A similar
proliferation of soundness theorems can be found in
TAPL~\cite{pierce}.}:

\vspace{2mm}
\noindent\fbox{
\begin{minipage}{.93\columnwidth}
\begin{gather*}
\forall e, t, \Sigma, \sigma.
    \left\{\begin{array}{c}
    | typeof e == return t | \\
    \Sigma \vdash \sigma
    \end{array}\right\}
 \rightarrow \\
  \exists v, \Sigma', \sigma'.
   \left\{\begin{array}{c}
   |put sigma >> eval e == put mu >> return v| \\
   \Sigma' \supseteq \Sigma \\
   \Sigma' \vdash v : t \\
   \Sigma' \vdash \sigma'
   \end{array}\right\} \\
\vee \\
  \exists x.
   |put sigma >> eval e == throw x|
\tag{\textsc{LSound}$_\mathit{ES}$}
\label{thm:SoundES}
\end{gather*}
\end{minipage}
}
\vspace{2mm}
% \BO{Wondering whether some additional notes on $\Sigma$ related portions is
% useful.}

Modular formulations of \ref{thm:SoundE} and \ref{thm:SoundS} are
useless for proving a modular variant of \ref{thm:SoundES} because
their induction hypotheses have the wrong form. The hypothesis for
\ref{thm:SoundE} requires the result to be of the form |return v|,
disallowing |put mu >> return v| (the form required by \ref{thm:SoundS}).
Similarly, the hypothesis for \ref{thm:SoundS} does not
account for exceptions occurring in subterms. In general, without
anticipating additional effects, type soundness theorems with fixed
sets of effects cannot be reused modularly.

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
