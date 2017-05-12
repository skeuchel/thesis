%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

\section{Reasoning \`{a} la Carte}\label{sec:mod:reasoningalacarte}

In Section \ref{sec:mod:datatypesalacarte} we focused on programming in
Haskell. In this Section we turn our attention towards performing modular
constructions of datatypes, functions and inductive proofs in a proof-assistant
like Agda or Coq.

%\subsection{Modular Definitions in Coq}

%{
%format tau = "\tau"
%format .   = "."
%format ×   = "\times"
%format mu  = "\mu"
%format muX  = "\mu{X}"

Unfortunately, we cannot directly translate the definitions of the
\emph{Datatypes \`a la Carte} approach of Section
\ref{sec:mod:datatypesalacarte} to a proof-assistant. These assistants commonly
require all datatype definitions to be to be \emph{strictly-positive} so that
all datatypes denote proper inductive definitions.  Lifting this restriction,
i.e. allowing arbitrary non strictly-positive recursive datatypes, renders the
theory of the proof-assistant inconsistent \cite{cpdt}.


We define \emph{strictly positive types} (SPT) by using the following generative
grammar~\cite{constructingstrictlypositivetypes}:

< tau ::= X | 0 | 1 | tau + tau | tau × tau | K -> tau | muX . tau

where |X| ranges over type variables and |K| ranges over constant
types,~i.e. an SPT with no free type variables. The constants |0| and
|1| represent the empty and unit types, the operators |+|, |×|, |->|
and |mu| represent coproduct, cartesian product, exponentiation
and least fixed point construction.
%}

For |FixDTC f| from Section \ref{sec:mod:datatypesalacarte} to be strictly
positive means that the argument functor |f| has to be strictly-positive,
i.e. it corresponds to a term built with the above grammar with one free type
variable.


%{
%format :-> = "\mapsto"

As a counter example, inlining the non-strictly positive functor |X :-> (X ->
Int) -> Int| into |FixDTC| yields the datatype declaration

> data NSP = NSP ((NSP -> Int) -> Int)

This is a valid Haskell declaration, but it does not satisfy the positivity
requirements and is hence rejected by Coq. While Coq can automatically determine
the positivity for any concrete functor by inspecting its definition, it cannot
do so for an abstract functor like the one that appears in the definition of
|FixDTC|. Hence, Coq conservatively rejects |FixDTC|.
%}

Of course, we have no intention of using non-strictly positive functors for our
application and would like to provide the evidence of strict-positivity to the
fixpoint type constructor. Mini-Agda~\cite{miniagda} for example allows
programmers to annotate strictly-positive and negative positions of type
constructors. Unfortunately, Agda and Coq do not provide us with this
possibility and a different approach is needed to define type-level fixed-points
and fold operators. 



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
