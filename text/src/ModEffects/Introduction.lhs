%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

\section{Introduction}

Formalizing the metatheory of languages with side-effects is a challenging
problem. Existing non-modular formalizations typically assume a concrete set of
effects that the feature of a particular language at hand is using. The
\emph{semantic functions}, \emph{theorem statements} (such as
\emph{type-soundness}) and corresponding \emph{proofs} of these formalizations
have the concrete set of effects hardwired.


%-------------------------------------------------------------------------------
\subsection{No Effect Modularity}

%format refAlg = "\Varid{eval_{Ref}}"
%format excAlg = "\Varid{eval_{Err}}"
%format ErrF = "\Varid{Err}_F"

The statement of type soundness for a language depends intimately on the effects
it uses, making it particularly difficult to achieve modularity. Consider
defining two features in MTC: mutable references |RefF| and errors |ErrF|. Both
of these introduce an effect to any language, the former state and the latter
the possibility of raising an error. These effects show up in the type of their
evaluation algebras:

< refAlg :: Mendler RefF (Env -> (Value,Env))
< excAlg :: Mendler ErrF (Maybe Value)

MTC supports the composition of two algebras over different functors as long as
they have the same carrier. That is not the case here, making the two algebras
incompatible. This problem can be solved by anticipating both effects in both
algebras:

< refAlg :: Mendler RefF (Env -> (Maybe Value,Env))
< excAlg :: Mendler ErrF (Env -> (Maybe Value,Env))

This anticipation is problematic for modularity: the algebra for references
mentions the effect of errors even though it does not involve them, while a
language that includes references does not necessarily feature errors.  More
importantly, the two algebras cannot be composed with a third feature that
introduces yet another effect (e.g., local environments) without further
foresight. It is impossible to know in advance all the effects that new features
may introduce.

Hence, a key challenge in modularizing effects is how to generalize every
definition -- \emph{semantic functions}, \emph{theorem statements} and
\emph{proofs} -- to a form that is \emph{general} enough to account for any
desired set of \emph{potential effects} instead of hardwiring one specific set
of effects.


%-------------------------------------------------------------------------------
\subsection{Achieving Modularity}
Fortunately, for semantic functions there is already a good solution:
\emph{monads} and \emph{monad transformers}. Monads are a well-established
mechanism for defining the semantics of languages with effects. Moreover, monads
give a \emph{uniform representation} for effectful computations independent of
the effects which is an important point for modularization. With the help of
monad transformers, monads can be modularly composed.

For each effect, a monad subclass captures a set of primitive operations.
These abstract type classes form the main interface that is used for
implementing and reasoning about features and their effects, instead of using a
particular monad (or monad stack) directly. This ensures that definitions are
general enough without assuming a concrete implementation. Reasoning about
monadic programs is commonly performed using \emph{equational reasoning}
\cite{justdoit, effectiveadvice} which is a prevalent techniques in functional
programming. For each of the monad type-classes, a set of algebraic laws governs
the interaction between primitive operations.


%-------------------------------------------------------------------------------
\subsection{Overview}

This chapter uses introduces the 3MT approach to tackle modular type-safety
proofs for effectful languages.

\paragraph{Semantics}
Monads form the underlying mechanism to define the semantics of languages
denotationally and monad transformers are used to modularize the
semantics. Section \ref{sec:mod:monadlibrary} introduces the 3MT monad library
that we use throughout this chapter and Section \ref{sec:mod:monadicsemantics}
combines \emph{modular datatypes} and \emph{monads} to define denotational
semantics with effects on a per-feature basis, without fixing the particular set
of effects or language constructs

\paragraph{Soundness}
To solve the key challenge of modularizing and reusing theorems and proofs of
type soundness, we split the classic type soundness theorems into three separate
parts:
\begin{enumerate}
\item
  Reusable \emph{feature theorems} capture the essence of type soundness for an
  individual feature. They depend on that feature's syntax, typing relation,
  semantic function and only the effects used therein. At the same time, they
  abstract over the syntax, semantics and effects of other features. This means
  that the addition of new features with other types of effects \emph{does not
    affect} the existing feature theorem proofs.

  To achieve the abstraction over other effects, a feature uses a polymorphic
  monad that is constrained by monad subclasses. As a consequence, it only
  establishes the well-typing of the resulting denotations with respect to the
  effects of the declared subclass constraints.

\item
  Reusable \emph{effect theorems} fix the monad of denotations and consequently
  the set of effects. They take well-typing proofs of monadic denotations
  expressed in terms of a constrained polymorphic monad and which mention only a
  subset of effects, and turn them into well-typings with respect to a fixed
  monad and all the effects it provides.

  Effect theorems reason fully at the level of denotations and abstract over the
  details of language features like syntax and semantic functions. Consequentely
  the same effect theorem will work for any languages that use the particular
  combination of effects captured by the theorem.

\item
  Finally, \emph{language theorems} establish type soundness for a particular
  language. They require no more effort than to instantiate the set of features
  and the set of effects (i.e., the monad), thus tying together the respective
  feature and effect theorems into an overall proof.
\end{enumerate}
%
Section \ref{sec:mod:monadictypesafety} examines \emph{feature theorems} and
Section \ref{sec:mod:effectlangtheorems} concerns itself with \emph{effect
  theorems} and \emph{language theorems}. Section \ref{sec:mod:casestudy}
discusses our case study of 5 features with their feature theorems, 8 different
effect theorems and 28 fully mechanized languages, including a mini-ML variant
with errors and references and Section \ref{sec:mod:relatedwork} compares
our approach to related work.
% before concluding in Section \ref{sec:mod:conclusion}.



%if False
\name solves this long-standing problem by splitting these theorems into two
separate and reusable parts: a \emph{feature theorem} that captures the
well-typing of denotations produced by the semantic function of an invidual
feature with respect to only the effects used, and an \emph{effect theorem} that
adapts well-typings of denotations to a fixed superset of effects.  The proof of
type soundness for a particular language simply combines these theorems for its
features and the combination of their effects.


\name combines \emph{modular datatypes} and \emph{monads} to define denotational
semantics with effects on a per-feature basis, without fixing the particular set
of effects or language constructs.

% Existing work already provides three important ingredients towards this goal:
% \emph{monads}, \emph{modular datatypes} and \emph{modular induction}. With
% monads and modular datatypes semantic functions can be modularly defined for
% each language feature without hard-wiring a particular set of effects or
% language constructs.

One well-established problem with \emph{type soundness} proofs for denotational
semantics is that they are notoriously brittle with respect to the addition of
new effects.

%To modularize proofs about these effectful semantic functions, \name shows that
%it is crucial to formulate the right theorems.

\name solves
this long-standing problem by splitting these theorems into two separate and
reusable parts: a \emph{feature theorem} that captures the well-typing of
denotations produced by the semantic function of an invidual feature with
respect to only the effects used, and an \emph{effect theorem} that adapts
well-typings of denotations to a fixed superset of effects.  The proof of type
soundness for a particular language simply combines these theorems for its
features and the combination of their effects.
%
To establish both theorems, \name uses two key reasoning techniques:
\emph{modular induction} and \emph{algebraic laws} about effects. Several
effectful language features, including references and errors, illustrate the
capabilities of \Name. A case study reuses these features to build fully
mechanized definitions and proofs for 28 languages, including several versions
of mini-ML with effects.


% The main contribution of this paper is to show how to modularize the theorems
% and proofs for these modular monadic definitions.

\begin{comment}
  Monads are needed to avoid hard-wiring a fixed set of effects into the
  definitions; modular datatypes avoid hard-wiring a fixed set of language
  constructs; and modular induction

  Previous work also shows that the combination of \emph{monads} and
  \emph{modular datatypes} is sufficient to effectively modularize semantic
  functions.  However for modularizing theorem statements (such as
  \emph{type-soundness}) and corresponding proofs we also need modular
  induction.

  All three ingredients are needed to effectively modularize theorem statements
  and proofs.

  The combination of monads and modular datatypes has already been shown to
  effectively deal with the modularization of semantics functions.

  The main challange in adding effects to the modular meta-theory framework is
  how to generalize \emph{theorem statements} (such as \emph{type-soundness})
  and corresponding \emph{proofs} to a form that is \emph{general} enough to
  account for all potential effects

  Hence, the key question is what form the general theorem should take. It
  cannot hardwire the effects, but must instead specifically cater to
  establishing type soundness with respect to any desired set of effects.

  This framework builds on previous work which has already shown how to
  modularize meta-theory using modular encodings of datatypes with a
  corresponding (modular) induction principle. However that work was limited to
  languages without effects.

  However,
  dealing with the corresponding modular monadic theorem statements and proofs
  offers significant new challenges that have not been addressed before.

  Since we cannot assume the concrete set of effects, We overcome this problem
  by generilize the theorem statement and prove type-soundness in two steps.

  When dealing with languages with effects the set of effects for different,
  modularly defined language features, may be different. As a result it is not
  possible to antecipate the concrete

  In previous work we have shown how to modularize meta-theory using Church
  encodings of datatypes with a corresponding (extensible) induction
  principle. An important limitation of that work was that it could only handle
  \emph{pure} languages.

  However, dealing with corresponding modular monadic theorem statements and
  proofs offers significant new challenges that have not been addressed
  before. In particular defining a modular \emph{type-soundness} statement is
  challanging because existing non-modular type-soundness theorems typically
  assume a concrete set of effects that is required for the particular proof in
  hand.  Since we cannot assume the concrete set of effects, We overcome this
  problem by generilize the theorem statement and prove type-soundness in two
  steps.

  We use algebraic laws on monads at a fundamental level.
\end{comment}

%endif


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
