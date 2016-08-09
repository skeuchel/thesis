%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt
%include exists.fmt

\section{Case study}
\label{sec:casestudy}

As a demonstration of the advantages of our approach over MTC's
Church-encoding based approach, we have ported the case study from
\cite{mtc}.

The study consists of five reusable language features with soundness
and continuity\footnote{of step-bounded evaluation functions} proofs
in addition to typing and evaluation functions.
Figure~\ref{fig:MiniMLSyntax} presents the syntax of the expressions,
values, and types provided by the features; each line is annotated
with the feature that provides that set of definitions.

\input{src/Modularity/MiniMLSyntax}

In this section we discuss the benefits and trade-offs we have
experienced while porting the case study to our approach.

\paragraph{Code size}

By the move to a datatype-generic approach the underlying modular
framework grew from about 2500 LoC to about 3500 LoC. This includes
both the universe of containers and polynomial functors and the
generic implementations of fold, induction and equality.

The size of the implementation of the modular feature components is
roughly 1100 LoC per feature in the original MTC case study. By
switching from Church-encodings to a datatype-generic approach we
stripped away on average 70 LoC of additional proof obligations needed
for reasoning with Church-encodings per feature. However, instantiating
the MTC interface amounts to roughly 40 LoC per feature while our approach
requires about 100 LoC per feature for the instances.

By using the generic equality and generic proofs about its properties
we can remove the specific implementations from the case study. This
is about 40 LoC per feature. In total we could reduce the average size
of a feature implementation to 1050 LoC.

\paragraph{Impredicative sets}\label{ssec:impredicativeset}

The higher-rank type in the definition of |FixMTC|

< FixMTC (f :: Set -> Set) = forall ((a :: Set)). Algebra f a -> a

causes |FixMTC f| to be in a higher universe level than the domain of
|f|. Hence to use |FixMTC f| as a fixpoint of |f| we need an
impredicative sort. MTC uses Coq's impredicative-set option for this
which is known to lead to logical inconsistencies.

When constructing the fixpoint of a container we do not need to raise
the universe level and can thus avoid using impredicative sets.

\paragraph{Induction principles}

%{
%format .         = "."
%format indArith2 = ind "_{" A "}^2"

Church encodings have problems supporting proper induction principles,
like the induction principle for arithmetic expressions |indArith| in
Section \ref{ssec:modularinductivereasoning}. MTC uses a
\emph{poor-man's induction principle} |indArith2| instead.

< indArith2 ::
<   forall ((p   :: (Arith -> Prop)).
<   forall ((hl  :: (forall n. p (InMTC (Lit n)))).
<   forall ((ha  :: (forall x y. p x -> p y -> p (InMTC (Add x y)))).
<   Algebra ArithF (exists a. p a)

The induction principle uses a dependent sum type to turn a proof
algebras into a regular algebra. The algebra builds a copy of the
original term and a proof that the property holds for the copy. The
proof for the copy can be obtained by folding with this algebra. In
order to draw conclusions about the original term two additional
\emph{well-formedness} conditions have to be proven.
%}
\begin{enumerate}

\item The proof-algebra has to be well-formed in the sense that it
really builds a copy of the original term instead of producing an
arbitrary term. This proof needs to be done only once for every
induction principle of every functor and is about 20 LoC per
feature. The use of this well-formedness proof is completely automated
using type-classes and hence hidden from the user.

\item The fold operator used to build the proof using the algebra
needs to be a proper fold operator, i.e. it needs to satisfy the
universal property of folds.

< foldMTC :: Algebra f a -> FixMTC f -> a
< foldMTC alg fa = fa alg
<
< type UniversalProperty (f :: * -> *) (e :: FixMTC f)
<   =  forall a (alg :: Algebra f a) (h :: FixMTC f -> a).
<        (forall e. h (inMTC e) = alg h e) ->
<          h e = foldMTC alg e

In an initial algebra representation of an inductive datatype, we have
a single implementation of a fold operator that can be proven
correct. In MTC's approach based on Church-encodings however, each
term consists of a separate fold implementation that must satisfy the
universal property.

\end{enumerate}

Hence, in order to enable reasoning MTC must provide a proof of the
universal property of folds for every value of a modular datatype that
is used in a proof. This is mostly done by packaging a term and the
proof of the universal property of its fold in a dependent sum type.

> type FixUP f = exists ((x :: FixMTC f)). UniversalProperty f x

\paragraph{Equality of terms}

Packaging universal properties with terms obfuscates equality of terms
when using Church-encodings. The proof component may differ for the
same underlying term.

This shows up for example in type-soundness proofs in MTC. An
extensible logical relation |WTValue (v ,t)| is used to represent
well-typing of values. The judgement ranges over values and types. The
universal properties are needed for inversion lemmas and thus the
judgement needs to range over the variants that are packaged with the
universal properties.

However, knowing that |WTValue (v, t)| and |proj1 t = proj1 t'| does
not directly imply |WTValue (v ,t')| because of the possibly distinct
proof component. To solve this situation auxiliary lemmas are needed
that establish the implication. Other logical relations need similar
lemmas. Every feature that introduces new rules to the judgements must
also provide proof algebras for these lemmas.

In the case study two logical relations need this kind of auxiliary
lemmas: the relation for well-typing and a sub-value relation for
continuity. Both of these relations are indexed by two modular types
and hence need two lemmas each. The proofs of these four lemmas, the
declaration of abstract proof algebras and the use of the lemmas
amounts to roughly 30 LoC per feature.

In our approach we never package proofs together with terms and hence
this problem never appears. We thereby gain better readability of
proofs and a small reduction in code size.

\paragraph{Adequacy}

Adequacy of definitions is an important problem in mechanizations. One
concern is the adequate encoding of fixpoints. MTC relies on a
side-condition to show that for a given functor |f| the folding |inMTC
:: f (FixMTC f) -> FixMTC f| and unfolding |outMTC :: FixMTC f -> f
(FixMTC f)| are inverse operations, namely, that all appearing |FixMTC
f| values need to have the universal property of folds. This
side-condition raises the question if |FixMTC f| is an adequate
fixpoint of |f|. The pairing of terms together with their proofs of
the universal property do not form a proper fixpoint either, because
of the possibility of different proof components for the same
underlying terms.

Our approach solve this adequacy issue. The |SPF| type class from
Figure \ref{fig:strictlypositivefunctor} requires that |in| and |out|
are inverse operations without any side conditions on the values and
containers give rise to proper |SPF| instances.


%if False
\paragraph{Refinement types}

The paper \cite{3mt} presents follow-up work
that uses the original MTC framework. It tackles
the problem of modular type-safety proofs for languages
with side-effecting features.

The following rule is used in \cite{3mt} for an extensible
relation of well-typed monadic computations.

< WFVM_Return ::
<     (v :: FixMTC vf) (t :: FixMTC tf) (mt : MT (FixMTC T)),
<     WFValue v t ->
<     {mt' : MT {t' : FixMTC T | proj1_sig t = proj1_sig t'} &
<       fmap (@proj1_sig _ _) mt' = mt} -> ...

%endif

%if False
\paragraph{Equality testing}

The implementation of equality testing in MTC proceeds in the same way
as other semantic functions: as folds of an algebra.

The carrier type of the algebra is |Fix d -> Bool| where |d| is the
abstract super-functor for types. The properties of the equality
typeclass from Figure \ref{fig:equalityclass} are established by
proof-algebras. However, the implementation is not entirely modular.

The algebra for the |FunType| functor relies on an additional function

> eq_TArrow :: SPF d =>
>   (Fix d -> Bool) -> (Fix d -> Bool) ->
>   Fix d -> Bool

that given the equality functions for two terms, constructs and
equality function for |TArrow|, i.e. if the given value was
constructed using |TArrow| it performs checking equality recursively
using the two given functions and otherwise it returns |False|. This
function also needs to be implemented by means of an algebra that
needs to be defined for |FunType| and any other functor for types and
is hence an instance of feature interaction in MTC. Using a generic
implementation of equality we can thus not only avoid boilerplate
code, but also cut down on feature interactions.
%endif
