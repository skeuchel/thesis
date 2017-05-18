%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

\section{Reasoning \`{a} la Carte}\label{sec:mod:reasoningalacarte}

Our goal is to extend the DTC's approach from \emph{modular programming} to
include \emph{modular reasoning}. In this Section, we give a brief overview of
reasoning in proof-assistants in general before moving towards modular reasoning
in the next Sections. Moreover, we also discuss restrictions of the
proof-assistant settings, which are necessary for logical consistency, but which
prevents us from porting the Haskell definitions to a proof-assistant directly.

\subsection{Propositions as Types}

Researchers in logic and computer science have discovered parallels between
logics and type systems for \textlambda-calculi. For example, the connectives of
propositional logic correspond to a simply-typed lambda calculus with some base
type, disjoint sums and cartesian products \cite{curry1934functionality}. Hence
types of the simply-typed lambda calculus can also be interpreted as
propositions in propositional logic.  Moreover, a program of a particular type
encodes a constructive proof of the corresponding proposition. Hence proving is
just programming.

This correspondence is not limited to propositional logic and simple types, but
has been observed for a variety of logics: propositional, predicate,
second-order, intuitionistic, classical, modal, and linear logics
\cite{propositionsastypes}. It is also known as the Curry-Howard correspondence
or the propositions-as-types interpretation. Wadler \cite{propositionsastypes}
gives a nice write-up and a historic account.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.98\columnwidth}
      \begin{tabular*}{\columnwidth}{ll@@{\quad}c@@{\quad}ll}
        Implication & $A \Rightarrow B$       &  & Function          & $A \to B$               \\
        Disjunction & $A \vee B$              &  & Disjoint sum      & $A + B$                 \\
        Conjunction & $A \wedge B$            &  & Product           & $A \times B$            \\ \hline
        Universal   & $\forall x \in A. B[x]$ &  & Dependent product & $\Pi_{(x : A)} B(x)$    \\
        Existential & $\exists x \in A. B[x]$ &  & Dependent sum     & $\Sigma_{(x : A)} B(x)$ \\
      \end{tabular*}
    \end{minipage}
  }
  \caption{Correspondences for propositional and predicate logic}
  \label{fig:mod:propastypes}
\end{figure}

This correspondence serves as the basis for many type-theory based
proof-assistant like Agda, Coq, NuPRL and Twelf. These systems support in
particular dependent-types which correspond to universal and existential
quantifiers in predicate logic that allows us to implement complex mathematical
properties.


\subsection{Induction Principles}
Another feature commonly found in proof-assistants are inductive datatype
definitions and reasoning about values of inductive types via recursion. As an
example, consider a definition of natural numbers and natural number addition:

\begin{code}
data Nat = Zero | Succ Nat

plus :: Nat -> Nat -> Nat
plus Zero      n = n
plus (Succ m)  n = Succ (plus m n)
\end{code}

To prove an easy proposition like the right-neutrality of $Zero$ we can
write a function that follows the recursive structure of the $plus$ function:
\begin{spec}
plusZero :: forall (m :: Nat). plus m Zero = m
plusZero Zero      = Refl
plusZero (Succ m)  = cong Succ (plusZero m)
\end{spec}

In the same way that we can implement functions using recursion schemes in
programming, we can implement proofs using similar schemes. These schemes are
called \emph{induction schemes} or \emph{induction principles}. For example,
for the natural numbers we can implement the following induction principle:

\begin{spec}
indNat ::
  forall (P :: Nat -> Prop). 
    P Zero ->
    (forall (m :: Nat). P m -> P (Succ m)) ->
    forall (m :: Nat). P m
indNat P pzero psucc = go
  where
    go :: forall (m :: Nat). P m
    go Zero      = pzero
    go (Succ m)  = psucc (go m)
\end{spec}

Notice the similarity to the natural number fold. In fact, |indNat| is a
dependent version of the fold. The second and third argument |pzero|
respectively |psucc| corresponding to the constructors, are called the
\emph{proof algebra} analogously to the term \emph{algebra} use for folds.
Analogously to re-implementing |plus| using folds, we can reimplement the
|plusZero| using the induction principle:
\begin{spec}
plusZero2 :: forall (m :: Nat). plus m Zero = m
plusZero2 = indNat (\m -> plus m Zero = m) Refl (cong Succ)
\end{spec}


%% One benefit of using induction principles instead of writing recursive proofs
%% directly, is that the \emph{induction hypotheses} for recursive positions are
%% automatically available without a need for a recursive calls. This helps proof
%% automation.
The main benefit that induction principles have for our purposes is that it
gives us a way to open the closed recursive structure of proofs: in the same way
that we universally implement modular semantic functions using modular algebras
with a generic fold operator we will implement modular induction proofs by using
modular proof algebras using a generic induction principle.

\subsection{Strict Positivity}

% In Section \ref{sec:mod:datatypesalacarte} we focused on programming in
% Haskell. In this Section we turn our attention towards performing modular
% constructions of datatypes, functions and inductive proofs in a proof-assistant
% like Agda or Coq.

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
