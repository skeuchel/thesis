%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

%if False

> {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts #-}

> module Extensibility where

%endif

%===============================================================================
\section{Background: Meta-Theory \`a la Carte}\label{s:mtc}

This section summarizes the necessary parts of the
\emph{Meta-Theory \`a la Carte} (MTC) approach to modular datatypes in
Coq.  For the full details of MTC, we refer the reader to the original paper~\cite{mtc}.

%-------------------------------------------------------------------------------
\subsection{Mendler Church Encodings and Folds for Semantics}

MTC encodes data types and folds with a variant of Church
encodings~\cite{bohm85automatic,pfenning90inductively} based on Mendler
folds~\cite{uustalu00mendler}.  The advantage of Mendler folds is that
recursive calls are explicit, allowing the user to precisely control the
evaluation order. The Mendler-Church encodings represent (least) fixpoints and folds as
follows:

%format Fix = "\Varid{Fix}"
%format fold = "\Varid{fold}"


> type Mendler f a = forall r. (r -> a) -> f r -> a

> type MFix f = forall a . Mendler f a -> a

> mfold :: Mendler f a -> MFix f -> a
> mfold alg fa = fa alg

Mendler algebras (|Mendler| |f| |a|) use a function argument of type (|r
-> a|) for their recursive calls. To enforce structurally recursive
calls, arguments which appear at recursive positions have a
polymorphic type |r|.  Using this polymorphic type prevents case
analysis, or any type of inspection, on those arguments.
Mendler-Church encodings (|MFix f|) are functions of type |forall a
. Mendler f a -> a|.  Mendler folds are defined by directly applying a
Church encoded value |fa| to a Mendler algebra |alg|. All these
definitions are non-recursive and can thus be expressed in Coq.

%% \footnote{ %% Some definitions requireimpredicativity.
%%For example to allow |Fix (f: Set -> Set) -> Set| %% %%for |f (Fix f) : Set|.}


\paragraph{Example} As a simple example, consider a language
for boolean expressions supporting boolean literals and
conditionals:

> data BoolF e = BLit Bool | If e e e

> type Value = Bool

The evaluation algebra for this language is defined as follows:

> ifAlg :: Mendler BoolF Value
> ifAlg eval (BLit b)       = b
> ifAlg eval (If e1 e2 e3)  = if (eval e1) then eval e2 else eval e3

Unlike conventional Church encodings and folds, the recursive calls (|eval|)
are explicit and indicate the evaluation order.
% This allows us to control evaluation and avoid relying on the
% evaluation order of the meta-language.

%if False

which has a small impact on the definitions of the |in_t| and |out_t| functions:

> -- in_t :: f (MFix f) -> MFix f
> -- in_t fexp = \alg -> alg (mfold alg) fexp

> -- out_t :: Functor f => MFix f -> f (MFix f)
> -- out_t exp = mfold (\rec fr -> fmap (\r -> in_t (rec r)) fr) exp

%endif

\noindent The evaluation function simply folds the |ifAlg| algebra:

%format myEval = "\Varid{eval}"

> myEval :: MFix BoolF -> Value
> myEval = mfold ifAlg

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

MTC adapts the \emph{Data Types \`a la Carte} (DTC)~\cite{swierstra08dtc}
approach for composing |f|-algebras to Mendler algebras.

% TOM: This text feels lost.
% --------------------------
% Differently from DTC,
% MTC definitions are regulated by a number of laws to support
% modular proofs.
% Furthermore, to support modular proofs a number of
% additional type classes is also required.

\paragraph{Modular Functors} Because feature syntax is defined by means of
functors, such as |BoolF|, it can easily be composed with functor
composition:
%if False

> infixr 7 :+:

%endif

> data (:+:) f g a = Inl (f a) | Inr (g a)

\noindent The syntax of a language of both conditional and simple
arithmetic expressions, for example, is |Fix (ArithF :+: BoolF)| where

> data ArithF e = Lit Int | Add e e

Feature semantics are expressed as Mendler algebras and can be
composed in a similar way.

\input{src/ModularEffects/SalCa_TypeClasses}

\paragraph{Type Classes}
Unlike DTC, MTC defines a number of type classes with laws in order to support
proofs.  These classes and laws are summarized in the table in
Figure~\ref{fig:SalCa_Typeclasses}.  The second column notes whether the base
instances of a particular class are provided by the user or are automatically
inferred with a default instance.  Importantly, instances of all these classes
for feature compositions (using |:+:|) are built automatically.

The |Functor| class provides the |fmap| method and is an adaptation of
the corresponding type class in Haskell. In contrast with the Haskell
version, the two functor laws are part of the definition. The class |
:<: | represents a subtyping relation between two functors |f| and
|g|. This class is an adaptation of the corresponding class in DTC and
it includes two additional laws which govern the behavior of functor
projection and injection (|inj_prj| and |prj_inj|). The class
|WF_Functor| ensures that |fmap| distributes through injection, and
the class |DistinctSubFunctor| ensures that injections from two
different subfunctors are distinct. Unlike DTC, MTC defines a single
generic Coq type class, |FAlg|, for the definition of semantic
algebras.  |FAlg| is indexed by the name of the semantic
function (|name|). Note that the type |Mixin|:

> type Mixin t f a = (t -> a) -> f r -> a

\noindent is a slight generalization of Mendler algebras, which is
useful for defining non-inductive language features such as general
recursion or higher-order binders. The type class |WF_FAlg| provides a
well-formedness condition for every composite algebra. Finally,
the type class |PAlg| provides the definitions for proof algebras.


%if False

\paragraph{Modular Mendler Algebras}
Using the type class |FAlg| we can define algebras modularly
for each functor. For example, the following instance

< instance FAlg "eval"

A type class is defined for every semantic function. For example,
the evaluation function has the following class:


\noindent In this class |evalAlg| represents the evaluation algebra
of a feature |f|.

MTC name deals with composite functors with a single generic instance
that works for any algebra:

< instance (Eval f, Eval g) => Eval (f :+: g) where
<   evalAlg eval (Inl fexp)  = evalAlg eval fexp
<   evalAlg eval (Inr gexp)  = evalAlg eval gexp

Finally, overall evaluation is defined as:

< eval2 :: Eval f => MFix f -> Value
< eval2 = mfold evalAlg

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

%%\input{src/Subtyping}
\vspace{-.08cm}
\subsection{Modular Proofs}\label{subsec:modproofs}
\vspace{-.07cm}
The main novelty of MTC is its modular approach to inductive
proofs. Regular structural induction is not available for Church
encodings, so MTC adapts the proof methods used in the \emph{initial
algebra semantics of data
types}~\cite{goguen77initial,malcolm90thesis} -- in particular
\emph{universal properties} -- to support modular inductive proofs
over Church encodings. Proofs are written in the same modular style as
functions, using proof algebras (class |PAlg| in
Figure~\ref{fig:SalCa_Typeclasses}).  These algebras are folded over
the terms and can be modularly combined.  Unlike function algebras,
proof algebras are subject to an additional constraint which ensures
the validity of the proofs (|proj_eq|).

% For instance, the law
%|proj_eq| states that the new term produced by application of the
%algebra is equal to the original term.\BO{other constraints?}

\paragraph{Sublemmas} Each feature builds extensible datatypes by
abstracting them over a super-functor. Because this
super-functor is abstract, the complete set of cases needed by a proof
algebra is unknown within a feature. To perform induction, a feature
must therefore dispatch proofs to an abstract proof algebra over this
super-functor. The components of this proof algebra are built in a
distributed fashion among individual features. These components can
then be composed to build a complete proof algebra for a
concrete composition of functors.

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

%-------------------------------------------------------------------------------
\subsection{No Effect Modularity}\label{s:mtc:problem}

%format refAlg = "\Varid{eval_{Ref}}"
%format excAlg = "\Varid{eval_{Err}}"
%format ErrF = "\Varid{Err}_F"


Unfortunately, effect modularity is not supported in MTC. Consider
two features: mutable references |RefF| and errors |ErrF|. Both of
these introduce an effect to any language, the former state and the
latter the possibility of raising an error. These effects show up
in the type of their evaluation algebras:

< refAlg :: Mendler RefF (Env -> (Value,Env))
< excAlg :: Mendler ErrF (Maybe Value)

MTC supports the composition of two algebras over different functors as long as
they have the same carrier. That is not the case here, making the two algebras
incompatible. This problem can be solved by anticipating both effects in both
algebras:

< refAlg :: Mendler RefF (Env -> (Maybe Value,Env))
< excAlg :: Mendler ErrF (Env -> (Maybe Value,Env))

This anticipation is problematic for modularity: the algebra
for references mentions the effect of errors even though it does not involve
them, while a language that includes references does not necessarily
feature errors.  More importantly, the two algebras cannot be
composed with a third feature that introduces yet another effect
(e.g., local environments) without further foresight. It is
impossible to know in advance all the effects that new
features may introduce.
