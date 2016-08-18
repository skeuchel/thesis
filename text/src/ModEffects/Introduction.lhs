%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

\section{Introduction}

\subsection{Effectful Languages}
\subsection{Monadic effects}

This paper presents \Name, a framework for \emph{modular} mechanized meta-theory
of languages with \emph{effects}. Using \Name, individual language features and
their corresponding definitions -- \emph{semantic functions}, \emph{theorem
statements} and \emph{proofs} -- can be built separately and then reused to
create different languages with fully mechanized meta-theory.  \name combines
\emph{modular datatypes} and \emph{monads} to define denotational semantics with
effects on a per-feature basis, without fixing the particular set of effects or
language constructs.

% Existing work already provides three important ingredients towards this goal:
% \emph{monads}, \emph{modular datatypes} and \emph{modular induction}. With
% monads and modular datatypes semantic functions can be modularly defined for
% each language feature without hard-wiring a particular set of effects or
% language constructs.

One well-established problem with \emph{type soundness} proofs for
denotational semantics is that they are notoriously brittle with
respect to the addition of new effects.

%To modularize proofs about these effectful semantic functions, \name shows that
%it is crucial to formulate the right theorems.

The statement of type soundness for a language depends intimately on the effects
it uses, making it particularly challenging to achieve modularity. \name solves
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

  Monads are a well-established providing the semantics of languages with
  effects; with the help of qualified types and monad transformers, monads can
  be modularly composed.

  \emph{Monads} and \emph{monad transformers} are a well-established way

  we have already shown how to modularize languages without effects. When adding
  effects every definition -- \emph{semantic functions}, \emph{theorem
    statements} and \emph{proofs} -- has to be suitable generalized to accounts
  for potential effects.  For semantic functions, \emph{monads} and \emph{monad
    transformers} have already been shown as an effective way to generalize such
  definitions.

  The main challange in adding effects to the modular meta-theory framework is
  how to generalize \emph{theorem statements} (such as \emph{type-soundness})
  and corresponding \emph{proofs} to a form that is \emph{general} enough to
  account for all potential effects

  Hence, the key question is what form the general theorem should take. It
  cannot hardwire the effects, but must instead specif- ically cater to
  establishing type soundness with respect to any de- sired set of effects.

  This framework builds on previous work which has already shown how to
  modularize meta-theory using modular encodings of datatypes with a
  corresponding (modular) induction principle. However that work was limited to
  languages without effects. The challange in adding effects is they essentially
  change every definition: \emph{semantic functions}, \emph{theorem statements}
  and \emph{proofs}. Fortunately, for semantic functions there is already a good
  solution: \emph{monads}.  Monads are a well-established mechanism for
  providing the semantics of languages with effects; with the help of qualified
  types and monad transformers, monads can be modularly composed. However,
  dealing with the corresponding modular monadic theorem statements and proofs
  offers significant new challenges that have not been addressed before. In
  particular defining a modular \emph{type-soundness} statement is non-trivial
  because existing non-modular type-soundness theorems typically assume a
  concrete set of effects that is required for the particular proof in hand.
  Since we cannot assume the concrete set of effects, We overcome this problem
  by generilize the theorem statement and prove type-soundness in two steps.

  Dealing modularly with effects is challenging because effects essentially
  change every definition: \emph{semantic functions}, \emph{theorem statements}
  and \emph{proofs}.  Fortunately, for semantic functions there is already a
  good solution: \emph{monads}.  Monads are a well-established mechanism for
  providing the semantics of languages with effects; with the help of qualified
  types and monad transformers, monads can be modularly composed.

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


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
