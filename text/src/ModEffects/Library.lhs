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

\input{src/ModEffects/Figures/3MT_Overview_Figure}


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
