%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt

\section{Related Work}\label{sec:mod:relatedwork}

%This section discusses related work.
%%The main novelty of our
%%work is that it combines the 3 axis of modularity in Figure~\ref{j}
%%with the ability to do modular proofs.

While previous work has explored the basic techniques of modularizing dynamic
semantics of languages with effects, our work is the first to show how to also
do modular proofs. Adding the ability to do modular proofs required the
development of novel techniques for reasoning about modular components with
effects.

%\BO{TODO: how do syntactic approaches deal with the problem? Make sure we discuss
%VeriML; perhaps Gonthier's canonical instances}

%-------------------------------------------------------------------------------
\subsection{Functional Models for Modular Side Effects}

% \paragraph{Effect Systems}
% Effect systems (also known as type-and-effect
% systems)~\cite{Lucassen:EffectSystems} form a popular non-monadic approach for
% making side effects explicit. However, they only describe (and do not define)
% programs that already have a meaning independent of the effect system. Hence,
% the effect annotations cannot adapt component behavior.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Monads and Monad Transformers}
Since Moggi~\cite{Moggi89a} first proposed monads to model side-effects, and
Wadler~\cite{Wadler92a} popularized them in the context of Haskell, various
researchers~(e.g., \cite{jones93,steele}) have sought to modularize monads.
Monad transformers emerged \cite{cenciarelli93asyntactic,liang95monad} from this
process, and in later years various alternative implementation designs
facilitating monad (transformer) implementations, have been developed, including
Filinksi's layered monads~\cite{Filinski:LayeredMonads} and Jaskelioff's
Monatron~\cite{monatron}.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Monads and Subtyping}
Filinski's MultiMonadic MetaLanguage
(M$^3$L)~\cite{Filinski:MonadicSemantics,Filinski:MonadsInAction} embraces the
monadic approach, but uses subtyping (or subeffecting) to combine the effects of
different components. The subtyping relation is fixed at the program or language
level, which does not provide the adaptability we achieve with constrained
polymorphism.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Algebraic Effects and Effect Handlers}
In the semantics community the algebraic theory of computational
effects~\cite{plotkin02notions} has been an active area of research. Many of the
laws about effects, which we have not seen before in the context of functional
programming, can be found throughout the semantics literature. Our first four
laws for exceptions, for example, have been presented by
Levy~\cite{levy06monads}.

A more recent model of side effects are effect handlers. They were introduced by
Plotkin and Pretnar~\cite{handlers} as a generalization from exception handlers
to handlers for a range of computational effects, such as I/O, state, and
nondeterminism. Bauer and Pretnar~\cite{eff} built the language \emph{Eff}
around effect handlers and show how to implement a wide range of effects in it.
Kammar et al.~\cite{hia} showed that effect handlers can be implemented in terms
of delimited continuations or free monads.

The major advantage of effect handlers over monads is that they are more easily
composed, as any composition of effect operations and corresponding handlers is
valid. In contrast, not every composition of monads is a monad. In the future,
we plan on investigating the use of effect handlers instead of monad
transformers, which could potentially reduce the amount of work involved on
proofs about interactions of effects.


%%It would be
%%interesting to investigate the use of effect handlers instead of the monad
%%transformers, but at the time of writing

%%However, we are
%%not aware of any work on reasoning about programs with effect
%%handlers.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Other Effect Models}
Other useful models have been proposed, such as \emph{applicative
  functors}~\cite{mcbride08applicative} and
\emph{arrows}~\cite{hughes98generalisingmonads}, each with their own axioms and
modularity properties.

%-------------------------------------------------------------------------------
\subsection{Modular Effectful Semantics}

There are several works on how to modularize semantics with effects, although
none of these works considers reasoning.

Mosses~\cite{msos} modularizes structural operational semantics by means of a
label transition system where extensible labels capture effects like state and
abrupt termination.  Swierstra~\cite{swierstra08dtc} presents modular syntax
with functor coproducts and modular semantics with algebra compositions. To
support effects, he uses modular syntax to define a free monad. The effectful
semantics for this free monad is not given in a modular manner, however.
Jaskelioff et al.~\cite{jaskelioff11modularity} present a modular approach for
operational semantics on top of Swierstra's modular syntax, although they do not
cover conventional semantics with side-effects. % \BO{Humm; I'd rephrase this!}
%First <- we can do First in the final version :P
Both Schrijvers and Oliveira~\cite{schrijvers10zipper+tr} and %later
Bahr and Hvitved~\cite{bahr11compositional} have shown how to define modular
semantics with monads for effects; this is essentially the approach followed in
this paper for modular semantics.

%-------------------------------------------------------------------------------
\subsection{Effects and Reasoning}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Non-Modular Monadic Reasoning}
Although monads are a purely functional way to encapsulate
computational-effects, programs using monads are challenging to reason about.
The main issue is that monads provide an abstraction over purely functional
models of effects, allowing functional programmers to write programs in terms of
abstract operations like |>>=|, |return|, or |get| and |put|. One way to reason
about monadic programs is to remove the abstraction provided by such
operations~\cite{hutton08reasoning}. However, this approach is fundamentally
non-modular.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Modular Monadic Reasoning}
Several more modular approaches to modular monadic reasoning have been pursued
in the past.

One approach to modular monadic reasoning is to exploit
\emph{parametricity}~\cite{reynolds83types,wadler89theorems}.
Voigtl\"ander~\cite{voigt09free} has shown how to derive parametricity theorems
for type constructor classes such as |Monad|. Unfortunately, the reasoning power
of parametricity is limited, and parametricity is not supported by
proof-assistants like Coq.

A second technique uses \emph{algebraic laws}. Liang and
Hudak~\cite{liang96modular} present one of the earliest examples of using
algebraic laws for reasoning. They use algebraic laws for reader monads to prove
correctness properties about a modular compiler.  In contrast to our work, their
compiler correctness proofs are pen-and-paper and thus more informal than our
proofs. Since they are not restricted by a termination checker or the use of
positive types only, they exploit features like general recursion in their
definitions.  Oliveira et al.~\cite{effectiveadvice} have also used algebraic
laws for the state monad, in combination with parametricity, for modular proofs
of non-interference of aspect-oriented advice. Hinze and Gibbons discuss several
other algebraic laws for various types of monads~\cite{gibbons11just}.  However,
as far as we know, we are the first to provide an extensive mechanized library
for monads and algebraic laws in Coq.
% \BO{Harrison's thesis? More? This is the most important line of related work!}

\subsection{Mechanization of Monad Transformers}
Huffmann~\cite{huffmann:transformers} illustrates an approach for mechanizing
type constructor classes in Isabelle/HOL with monad transformers.  He considers
transformer variants of the resumption, error and writer monads, but features
only the generic functor, monad and transformer laws. The work tackles many
issues that are not relevant for our Coq setting, such as lack of parametric
polymorphism and explicit modeling of laziness.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
