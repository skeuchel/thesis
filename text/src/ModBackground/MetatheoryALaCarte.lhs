%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

%if False

> {-# LANGUAGE RankNTypes ImpredicativeTypes TypeOperators #-}
> {-# LANGUAGE MultiParamTypeClasses FlexibleInstances #-}
> {-# LANGUAGE OverlappingInstances FlexibleContexts #-}

> module MetatheoryALaCarte where

%endif

\section{Metatheory \`a la Carte}\label{sec:mod:mtc}

This section summarizes the necessary parts of the \emph{Meta-Theory \`a la
  Carte} (MTC) approach to modular datatypes in Coq.  For the full details of
MTC, we refer the reader to the original paper~\cite{mtc}.  MTC encodes data
types and folds with a variant of Church
encodings~\cite{bohm85automatic,pfenning90inductively} based on Mendler
folds~\cite{uustalu00mendler}.


%-------------------------------------------------------------------------------
\subsection{Mendler Church Encodings and Folds for Semantics}

%format Fix = "\Varid{Fix}"
%format fold = "\Varid{fold}"

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}
    \begin{code}
      type MAlgebra f a = forall r. (r -> a) -> f r -> a

      type MFix f = forall a . MAlgebra f a -> a

      mfold :: MAlgebra f a -> MFix f -> a
      mfold alg fa = fa alg
    \end{code}
  \end{minipage}
}
\caption{Modular datatypes using Mendler-Church encodings}
\label{fig:mod:mendlerchurchencoding}
\end{figure}

In comparison to ordinary Church encodings, the Mendler Church encodings (|MFix
f|) differ in their use of Mendler algebras (|MAlgebra f a|) instead of ordinary
|F|-algebras as shown in Figure \ref{fig:mod:mendlerchurchencoding}. Mendler
algebras take an additional function argument of type (|r -> a|) for their
recursive calls. To enforce structurally recursive calls, arguments which appear
at recursive positions have a polymorphic type |r|.  Using this polymorphic type
prevents case analysis, or any type of inspection, on those arguments.  Mendler
folds (|mfold fa alg|) are defined by directly applying a Church encoded value
|fa| to a Mendler algebra |alg|. All these definitions are non-recursive and can
thus be expressed in Coq.


%% \footnote{ %% Some definitions requireimpredicativity.
%%For example to allow |Fix (f: Set -> Set) -> Set| %% %%for |f (Fix f) : Set|.}


\paragraph{Example} As a simple example, consider a language for boolean
expressions supporting boolean literals and conditionals as shown in Figure
\ref{fig:mod:mendlerchurchexample}.

%format myEval = "\Varid{eval}"

\begin{figure}[t]
\fbox{
  \hspace{-0.4cm}%
  \begin{minipage}{\columnwidth}
    \begin{code}
      data BoolF e = BLit Bool | If e e e
      type Value = Bool

      ifAlg :: MAlgebra BoolF Value
      ifAlg eval (BLit b)       = b
      ifAlg eval (If e1 e2 e3)  = if (eval e1) then eval e2 else eval e3

      myEval :: MFix BoolF -> Value
      myEval = mfold ifAlg

    \end{code}
  \end{minipage}
}
\caption{Boolean expressions using Mendler-Church encodings}
\label{fig:mod:mendlerchurchexample}
\end{figure}

The evaluation algebra |ifAlg| for this language takes the function argument
|eval| for evaluating recursive positions. Hence the recursive calls are
explicit. The evaluation function |myEval| simply folds the |ifAlg| algebra.


%% Unlike conventional Church encodings and folds, and indicate the evaluation
%% order.
%% This allows us to control evaluation and avoid relying on the
%% evaluation order of the meta-language.

%if False

which has a small impact on the definitions of the |in_t| and |out_t| functions:

> -- in_t :: f (MFix f) -> MFix f
> -- in_t fexp = \alg -> alg (mfold alg) fexp

> -- out_t :: Functor f => MFix f -> f (MFix f)
> -- out_t exp = mfold (\rec fr -> fmap (\r -> in_t (rec r)) fr) exp

%endif



%if False

In other
words, definitions that inspect values in recursive positions such as:

%format dots = "\ldots"

< ifEval :: MAlgebra IfF Value
< ifEval eval (If (If e1 e2 e3) e4 e5) = dots

do not type-check.

%endif



%-------------------------------------------------------------------------------
\subsection{Modular Composition of Features}\label{sec:comp}

\input{src/ModBackground/Figures/SalCa_TypeClasses}

MTC adapts the \emph{Data Types \`a la Carte} (DTC)~\cite{dtc} approach for
composing |F|-algebras to Mendler algebras. MTC defines a number of type classes
with laws in order to support proofs.  These classes and laws are summarized in
the table in Figure~\ref{fig:SalCa_Typeclasses}.  The second column notes
whether the base instances of a particular class are provided by the user or are
automatically inferred with a default instance. Importantly, instances of all
these classes for feature compositions (using |:+:|) are built automatically.


\paragraph{Modular Functors}
The |Functor| and functor subtyping |:<:| classes are a direct adaptation
of the corresponding DTC type classes.

%% class provides the |fmap| method and is an adaptation of
%% the corresponding type class in Haskell. In contrast with the Haskell
%% version, the two functor laws are part of the definition. The class |
%% :<: | represents a subtyping relation between two functors |f| and
%% |g|.

%% Because feature syntax is defined by means of
%% functors, such as |BoolF|, it can easily be composed with functor
%% composition:
%%
%% This class is an adaptation of the corresponding class in DTC and
%% it includes two additional laws which govern the behavior of functor
%% projection and injection (|inj_prj| and |prj_inj|).

The class |WF_Functor| ensures that |fmap| distributes through injection, and
the class |DistinctSubFunctor| ensures that injections from two different
subfunctors are distinct. These properties are necessary to modularize reasoning
along functor composition.


\paragraph{Modular Algebras}
MTC defines a single generic Coq type class, |FAlg|, for the definition of
semantic algebras that encompasses both, ordinary |F|-algebras and Mendler
algebras. Semantic functions can be explicitly named and |FAlg| take a (|name|)
as an index. The |Mixin| type slightly generalizes Mendler algebras by using an
additional type parameter instead of the universal type quantification. This
generalization is also useful for defining non-inductive language features such
as general recursion or higher-order binders.

Feature compositions are handled generically by the following instance:

< instance (FAlg n t a f, FAlg n a g) => FAlg n t a (f :+: g) where
<   f_algebra eval (Inl fexp)  = f_algebra eval fexp
<   f_algebra eval (Inr gexp)  = f_algebra eval gexp

The type class |WF_FAlg| provides a well-formedness condition for every
composite algebra. Finally, the type class |PAlg| provides the definitions for
proof algebras that we discuss in Section \ref{ssec:mod:modularproofs}.

\paragraph{Example}



%if False

\paragraph{Constructing and destructing Church-encoded terms}
Two standard constructions from the initial algebra semantics
of datatypes (which are based on folds) are generic constructor (|in_t|)
and destructor functions (|out_t|).

> in_t :: f (MFix f) -> MFix f
> in_t fexp = \alg -> alg (mfold alg) fexp

< out_t :: Functor f => MFix f -> f (MFix f)
< out_t exp = mfold (\rec fr -> fmap (in_t . rec) fr) exp

%if False

TYPING PROBLEM

< out_t :: forall f. Functor f => MFix f -> f (MFix f)
< out_t exp = mfold (\rec fr -> (fmap :: ((r -> MFix f) -> f r -> f (MFix f))) (\r -> in_t (rec r)) fr) exp

%endif

The |in_t| function builds a new term from the application of
|f| to some subterms. The |out_t| function exposes the toplevel functor again.
These functions can be combined with the methods |prj| and |inj|
from the class |:<:| to provide smarter generic constructor (|inject|) and
destructor (|project|) functions:

> inject :: (g :<: f) => g (MFix f) -> MFix f
> inject gexp = in_t (inj gexp)

> project ::  (g :<: f, Functor f) =>
>             MFix f -> Maybe (g (MFix f))
> project exp = prj (out_t exp)

The advantage of these constructors is that they
Specific smart constructors for terms like boolean literals or
conditionals are recovered as follows:

> lit :: (ArithF :<: f) => Nat -> MFix f
> lit n = inject (Lit n)

\vspace{-.5cm}

< cond  :: (IfF :<: f)
<       => MFix f -> MFix f -> MFix f -> MFix f
< cond c e1 e2 = inject (If c e1 e2)


%if False

> cond  :: forall f. (IfF :<: f) => MFix f -> MFix f -> MFix f -> MFix f
> cond c e1 e2 alg = inject ((If :: (MFix f -> MFix f -> MFix f -> IfF (MFix f)))
>                               c e1 e2) alg

%endif

\name requires these functions
to allow construct Church-encoded terms and to provide support
for pattern matching over those terms.

%endif


\subsection{Modular Proofs}\label{ssec:mod:modularproofs}

Each feature builds extensible datatypes by abstracting them over a
super-functor. Because this super-functor is abstract, the complete set of cases
needed by a proof algebra is unknown within a feature. To perform induction, a
feature must therefore dispatch proofs to an abstract proof algebra over this
super-functor. The components of this proof algebra are built in a distributed
fashion among individual features. These components can then be composed to
build a complete proof algebra for a concrete composition of functors.


%if False

%format T_1 = "\Varid{T}_1"
%format T_2 = "\Varid{T}_2"
%format EqF_name = "\Varid{EqF}_{name}"
%format ArithT = "\Varid{Arith}_F"
%format BoolT = "\Varid{Logic}_F"

As an example, consider the lemma that the type equality function
|eqType| is sound:
\begin{gather}
|forall t_1 t_2. eqType t_1 t_2 == true -> t_1 == t_2|
\tag{|EqP|}
\end{gather}
This property can be captured in a proof algebra:
\[ |PAlg EqF_name f f (exists e: EqP e)| \]
A feature can build a proof of |EqP| for a specific type |t| by folding
this proof algebra over |t|. Features also provide specific instances of
this proof algebra for the types they introduce:
\[  |PAlg EqF_name TBoolF f (exists e: EqP e)| \]

A concrete language with boolean and natural types
provides a proof algebra of the lemma by composing
the proof algebras for the two separate type functors
and instantiating the super-functor |f| to |TNatF :+: TBoolF|.
% < PAlg EqF_name TNatF (TNatF :+: TBoolF) (exists e: EqP e)
% < PAlg EqF_name TBoolF (TNatF :+: TBoolF)  (exists e: EqP e)
% The |p_algebra| component of each of these algebras is a proof that
% the |Eq_P| holds for the specified subfunctor and can be built
% independently in the feature
% that defines that subfunctor.
By instantiating |f| to other functor compositions, the proof algebras
of the individual features can easily be reused in other languages.

%The modular setting requires every case analysis on every church
%encoded datatype to be handled by a sublemma. This is necessary because the
%super-functor of these church encodings is abstract,
%so the complete set cases are not known locally; they have to be handled in
%a distributed fashion. Hence, modular lemmas built from proof algebras
%are not just an important tool for reuse in MTC -- they are the main
%method of constructing extensible proofs.

%endif



%if False

\paragraph{Inversion lemmas} To facilitate modular proof development,
MTC relies heavily on \emph{inversion lemmas} like
\[ \Sigma \vdash |v| : |TBool| \rightarrow \exists b. |isBool v = Just
b| \]
This inversion lemma expresses a contract on the modular definitions of
typing and |isBool|. It states that if value |v| has type |TBool|,
then |v| is indeed a boolean value.  Any language that includes both a
feature that uses boolean values and another feature that uses other
types of values must have an instance of this inversion lemma.  These
inversion lemmas are known as \emph{feature
interactions}~\cite{featureinteractions} in the setting of modular
component-based frameworks. In essence, a feature interaction is
functionality (e.g., a function or a proof) that is only necessary
when two features are combined.  Our modular approach supports feature
interactions by capturing them in type classes. A missing case can
then be easily added as a new instance of that type class without
affecting or overriding existing code.

%endif

% An example from
% this study is the inversion lemma which states that values with type
% nat are natural numbers: $\vdash$ |x| : |nat| $\rightarrow$ |x :: N|.
% The
% Bool feature introduces a new typing judgment, WT-BOOL for boolean
% values.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
