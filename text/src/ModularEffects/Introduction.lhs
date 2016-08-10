%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

\section{Introduction}
\label{sec:intro}

Theorem provers are actively used to mechanically verify large-scale
formalizations of critical components, including programming language
meta-theory~\cite{poplmark}, compilers~\cite{leroy09cc}, large
mathematical proofs~\cite{gonthier13engineering} and operating system
kernels~\cite{klein10seL4}. Due to their scale and complexity, these
developments can be quite time consuming, often demanding multiple
man-years of effort.

It is reasonable to expect that variations can simply
extend and reuse the original development in order to leverage the
large investment of resources in these formalizations.
This is unfortunately often not the case, as even small extensions
can require significant additional effort.
Adding a new language feature to a programming language formalization or
compiler, for example, involves significant redesigns that
have a cross-cutting impact on nearly all definitions and proofs in the
formalization. This leads to a copy-paste-patch approach to reuse with
several modified copies of the original development, making it difficult to
compose new features and ultimately leading to a maintenance nightmare.
%is desirable to structure their design as modularly as possible to
%enable easy modification and reuse. To this end, proof assistants such
%as Coq and Agda have powerful modularity constructs including modules,
%type classes and expressive forms of dependent types. Unfortunately,
%these modularity constructs are designed to support the addition of
%new definitions and proofs. When extension cut across these modularity
%boundaries by requiring a modification to existing definitions, as
%when adding a new piece of syntax to the expressions of a language,
%users are forced to manually edit the development, leading to a
%cut-paste-patch approach to reuse.
Dissatisfied with this situation, several
researchers~\cite{poplmark,shao10certified,stampoulis10VeriML,gonthier13engineering}
have called for better ways to modularize mechanical formalizations.

This work extends the current state-of-the-art in modular
mechanizations by solving a well-known and long-standing open problem
with denotational semantics: type soundness proofs are notoriously
brittle with respect to the addition of new effects. This is an
important problem because effects are pervasive in programming
language formalizations: in addition to extensions to syntax and
semantics, new features usually introduce new effects to the
denotations. Without a more robust formulation of type soundness, the
addition of new effects requires cross-cutting changes to type
soundness theorem statements and proofs.

Initially the semantics themselves were also brittle with respect to
effects~\cite{mosses84sdt,lee1989realistic}, but
\emph{monads}~\cite{Moggi89a,Wadler92a} have been found to provide the
necessary robustness to denotations. Yet as far as we know, the brittleness 
of (denotational) type soundness proofs has remained an open problem since it was raised by Wright and
Felleisen~\cite{wright94syntactic} to motivate their own type-soundness
approach. The framework we present here, \emph{modular monadic meta-theory} (\Name), is
the first in 20 years to provide a substantial solution. Using \Name, we develop a
novel approach to proving type soundness for monadic denotational
semantics in a way that is modular in the set of effects used. Proofs for
individual features do not depend on effects they do not use and hence
are robust to extension.

%%For example, it would be reasonable to expect that
%%after verifying a C compiler, verifying a C compiler with some
%%extensions requires a proportionaly equal effort to verify the language
%%extensions.
%Unfortunately, this is often not the case. Existing formal developments are
%usually \emph{monolithic} and extensions involve significant redesigns that
%have a pervasive impact on nearly all definitions and proofs in the
%formalization.

% \begin{figure}
% \begin{center}
% \includegraphics[scale=0.5]{src/modaxis.png}
% \end{center}
% \caption{Three dimensions of modularity.}
% \label{sec:axis}
% \vspace{-.5cm}
% \end{figure}

The solution builds on Meta-Theory \`{a} la Carte (MTC)~\cite{mtc}, a Coq
framework for the mechanization of formal programming language meta-theory that
supports modular extension of existing definitions. With MTC it is possible to
develop meta-theory which is modular in two dimensions: \emph{language features}
on the one hand and \emph{functions} and \emph{proofs} over these features on
the other hand. MTC adapts ideas from existing programming language
solutions~\cite{swierstra08dtc,oliveira09modular} to the \emph{expression
problem}~\cite{wadler98expression-problem} for functions and features, and adds
\emph{modular induction} for proofs.

\name adds a third modularity dimension to MTC: modular addition of new \emph{effects}. 
\name enables the separate definition of features with
effectful semantic functions and proofs over these functions, and reuse of
these features in formalizations of multiple languages.

To make denotations robust with respect to effects, \name uses the
established solution, \emph{monads}. In Coq, \emph{type
classes}~\cite{wadler89how-to} enable semantic function definitions
that are constrained, yet polymorphic in the monad. This allows the
inclusion of a feature in any language which supports a superset of
its effects. When a language is composed from different effectful
features, \emph{monad transformers}~\cite{liang95monad} are used to instantiate
the denotation's monad with all the effects required by the modular
components.

To solve the key challenge of modularizing and reusing theorems and proofs of 
type soundness, we split the classic type soundness theorems into three parts:
%%are highly challening because their traditional
%%formulations depend intimately
%%on the effects (such as state or exceptions) used by a language. As a
%%consequence, soundness statements over different sets of effects are
%%fundamentally incompatible and cannot be reused for supersets of
%%effects. \name overcomes this problem by splitting the problem into three
%%key theorems.
\begin{enumerate}
\item Reusable \emph{feature theorems} capture the essence
      of type soundness for an individual feature. 
      They depend only on that feature's syntax, typing relation, semantic function and the
      effects used therein. At the same time,
      they abstract over the syntax, semantics and effects of other features.
      This means that the addition of new features with other types of effects 
      \emph{does not affect} the existing feature theorem proofs. 

      To achieve the abstraction over other effects, a feature uses a constrained
      polymorphic monad. As a consequence, it only establishes the well-typing of the resulting
      denotations with respect to the effects declared in the constraints. 

\item Reusable \emph{effect theorems} fix the monad of denotations and consequently
      the set of effects. They take well-typing proofs of monadic denotations 
      expressed in terms of a constrained polymorphic monad and which mention only a subset of
      effects, and turn them into well-typings with respect to a fixed monad and all the effects it
      provides.
      
      Effect theorems reason fully at the level of denotations and
      abstract over the details of language features like syntax and semantic
      functions.

%       capture the overall interaction of
%       effects and evaluation for a particular combination of effects. Proofs
%       of this kind of theorem depend only on the set of effects used in
%       evaluation, and are orthogonal to features. Consequentely the same effect theorem
%       will work for any languages that use the particular combination of
%       effects captured by the theorem.



%%Proofs of this kind of theorem are independent
%%from any details of the features' semantic functions:
%%they only need to know that a feature preserves the reusable feature theorem.
\item Finally, \emph{language theorems} 
      establish type soundness for a particular language. 
      They require no more effort than to 
      instantiate the set of features and the set of effects (i.e., the monad), 
      thus tying together the respective feature and effect theorems into an overall proof.
\end{enumerate}
To establish the first two theorems, \name relies on modular induction and algebraic
laws about effects. As far as we know, it applies
the most comprehensive set of such laws to date, as
each effect utilized by a feature needs to
be backed up by laws and interactions between different
effects must also be governed by laws. These laws are crucial for
modular reasoning in the presence of effects.

% \BO{Expand and say something about case studies.}

\begin{comment}
An essential problem with existing development methodologies is that
they fail to deal with \emph{crosscutting concerns}. The problem is
not very different from problems which have been previously identified
in general software development.  As Tarr et al~\cite{f} argues most
programming languages tend to favor one form of decomposition, which
allows software to be modularized in certain way. Figure~\ref{sec:axis}
illustrates three different types of decomposition in which software
can be modularized. In the case of theorem provers like Coq, which can be viewed as functional
programming languages, the use of inductive datatypes allows
natural support for the modularization of \emph{operations} and \emph{proofs}.
However, as epitomized by the \emph{Expression Problem}~\cite{g}, if it is necessary
to extend the inductive datatypes with new cases then several
crosscutting changes are needed to update the operations and proofs.
Furthermore the introduction of effects in existing operations
requires pervasive changes to propagate effects in all
calling functions. In other words, while functional languages support
modularity naturally along the operations/proofs axis, they do not support
modularity well in the other two axis.


Previous work already provides three important ingredients towards
this goal: \emph{monads}~\cite{wadler}, \emph{modular
datatypes}~\cite{m} and \emph{modular induction}~\cite{e}. Monads are a
well-established way providing the semantics of languages with
effects; with the help of qualified types~\cite{j} and monad
transformers~\cite{k}, monads can be modularly composed. Modular
datatypes allow parts of a datatype and corresponding functions to be
defined separately and are helpful to localize particular features of
programming languages. Monads and modular datatypes have already
been shown to be an effective means to modularize

More recently it has been shown how to add
a modular form of induction on top of a variant of modular datatypes.
With modular induction it becomes possible to define

With monads and modular datatypes
semantic functions can be modularly defined for each language feature
without hard-wiring a particular set of effects or language
constructs~\cite{o}.

Previous work has already done significant progress towards
the development of modular techniques.

In previous work, we have proposed a solution for allowing modularity
in two dimensions simultaneously: operations/proofs and language constructs.
While for operations we were able, for the most part, to built on
existing solutions to the expression problem for mainstream languages,
dealing with proofs modularly required new techniques. In particular,
we had to develop new techniques which allowed us to express
\emph{inductive proofs} in a modular way. However, that work did
not provide a modular solution for effects. As a result, our meta-theory
framework was effectively limited to \emph{pure} languages.

In this work we provide a \emph{modular} solution for effects
that in combination with MTC allows the development of modular meta-theory
for languages with \emph{effects}. Much like our previous work,
dealing only with operations (not proofs) can, for the most part,
be done using existing techniques~\cite{j}. However, once again, the
key challenge lies in how to modularize theorems and proofs along the
three dimensions of modularity.
\end{comment}

\paragraph{}
In summary, the specific contributions of this work are:
\begin{itemize}

\item A reusable framework, \Name, for mechanized meta-theory of languages with effects.
This framework includes a mechanized library for monads, monad transformers and
corresponding algebraic laws in Coq. Besides several laws for
specific types of effects, the library also includes laws for
the interactions between different types of effects.

\item A new \emph{modular} proof method for type-soundness proofs of denotational semantics.

\item A case study of a family of fully mechanized languages, including
a mini-ML variant with errors and references. The case study comprises
28 languages, 8 different effect theorems and 5 features with their feature theorems.

\end{itemize}

\noindent\name is implemented in the Coq proof assistant and the code is available at
\url{http://www.cs.utexas.edu/~bendy/3MT}.
% Our implementation minimizes the
% programmer's burden for adding new features by automating the boilerplate with
% type classes and default tactics.
%%Moreover, the framework already provides modular
%%components for mini-ML as a starting point for new language formalizations.
% We also provide a complimentary Haskell
% implementation of the computational subset of code used in this paper.

%if False

This new approach for semantics builds on a lot of existing work:
modular monadic semantics, solutions to the expression problem,
mechanization-friendly techniques for representing binders, and
modular proof methods. However, we emphasize that our work does not
simply combine existing techniques in a straightforward way.
In fact, to make all of these techniques work smoothly in a theorem
prover like Coq, we had to overcome significant technical problems.
Therefore, some additional contributions of our work include:

\begin{itemize}

\item {\bf Modular Components in Type Theory:} We demonstrate how to
define modular components in languages without general recursion.
Unlike Data Types \'a la Carte, we cannot use inductively defined
(functor) data types to represent values, as Coq does not allow us to
express their fixpoint.

  Instead, we use (Mendler-style) fold-like encodings to represent values.
  This avoids the need for general type-level fixpoints.

\item {\bf Modular reasoning techniques:} It is not enough
  to define modular semantic components: we must also be
  able to modularly reason about those components. We show
  how to adapt initial algebra semantics reasoning techniques
  to our setting of modular components. We also have to
  to reason about modular monadic components in a modular way.

\end{itemize}

%endif

%-------------------------------------------------------------------------------
\paragraph{Code and Notational Conventions}

While all the code underlying this paper has been developed in Coq,
the paper adopts a terser syntax for its many code fragments.  For the
computational parts, this syntax exactly coincides with Haskell
syntax, while it is an extrapolation of Haskell syntax style for
propositions and proof concepts. Following MTC, the Coq code requires the
impredicative-set option due to the use of Church encodings.

%if False
\subsection{Old text}

The state-of-the art is not very scalable. As the size of languages
grow and we moved from small core calculi to real-world programming
languages, the interesting subset of the language tend to remain
small, while many sugaring constructs are added to the language. This
means that as the size of languages grow, more tedious and error-prone
work is required to deal with routine language constructs.
Instead of pen-and-paper formalizations, we can use proof assistants to
machine check the formalization. Although mechanization alone does not
solve the reusability issue (and in fact it can introduce additional problems),
it does help with scalability because the machine help finding errors in the
formalization and the verification process is automated.




Implementations of programming language use interpreters; whereas
most techniques for formalizing semantics and proofs use logical relations.
There is a gap between implementations and formalizations. Some
work on modularizing implementations; rather less work on modularizing
formalizations.

\begin{verbatim}
These are a collection of notes of relevant
information like useful references, goals,
potential research directions and potential
hurdles that may need to be overcome.

I'll take my personal view when writing these
notes, but I encourage others to add their own
views too so that we get synchronized.

============= PROJECT GOALS =============

1 sentence description:

  A Modular and Mechanizable Monadic Denotational
  Approach to Semantics and Proofs

(This is not intended as a title, though it could
be). I believe this is what we are looking for.

Some explanation of the benefits:

  - Denotational is good because, at least for
  purely functional
    languages, proofs are quite nice.

  - Monadic is good because it tries to bring the
  nice properties of the
    denotational approach to the impure world. The
    question is: can we get nice
    denotational-style proofs also in the impure
    world?

  - Mechanizable is good because automates
  checking of proofs and
    bolsters confidence in proofs.

  - Modular is good because we want to get
  reusable framework for
    semantics and make formalization of extensions
    easier.

Analyzing our goal a bit further, I think there
are actually a few different things that we are
trying to achieve:

  1) Modular proofs;

  2) A Monadic denotational approach to Semantics
  and Proofs.

Also there's an orthogonal direction, which is
whether it's mechanically or manually done.

So, we could try to be doing modular proofs using
a different style (say operational semantics); or
we could try to investigate a monadic denotational
approach without being modular (I think there's
some work in this area, but I don't think there
are attempts to mechanize those proofs); or we
could try to investigate either of these in a
pen-and-paper approach.

====================== OUTCOMES/CONTRIBUTIONS
======================

I guess there would be 2 main outcomes:

  - Modular semantic proofs in proof assistants
  like Coq (without
    additional tools);

  - Formalizations based on a denotational style,
  amenable to nice,
    algebra of programing style proofs.

I think those are pretty good claims, but they
will only be very strong if we are able to prove
something non-trivial.

=============== PLAN ===============

What's the plan?

I think if we want to achieve this goal, we need
to ultimately aim at having a Coq framework with
several modular components that can be plugged in
together:

  - Modular language constructs
     * arithmetic expressions; * boolean
     expressions; * binding: more realistic
     programming constructs (definitions,
     variables)?; * side-effects (state,
     exceptions, continuations, ...) * closures
     (lambda's)?  * recursion?

  - Modular semantics:
     * modular dynamic semantics (interpreters,
     compilers); * modular static semantics (type
     system)?;

  - Modular proofs
    * adequacy of semantics; * soundness(progress
    + preservation)?

  - Monadic library (needed for adding effectful
  features);

============================== CHALLENGES/RESEARCH
DIRECTIONS ==============================

We have already started building the framework,
but there are a few foreseeable challenges ahead.
I think the stuff marked with a ? In PLAN, will
provide some challenge and we may have to consider
whether or not to tackle it. Comments next:

- binding: binding is always a challenge in
mechanical formalizations.  By now we know a few
ways to deal with this (ex: locally nameless
representations). But in the denotational style
HOAS is common. The problem is that HOAS and Coq
do not get along well. How about PHOAS?

- closures: the challenge is how to model the
dynamic semantics of a language with closures in
Coq modularly? The untyped lambda is Turing
complete, so writing the interpreter directly
should not be possible in Coq. I believe the way
to deal with the untyped lambda calculus is to use
Inductive relations instead of an interpreter. But
inductive relations are non-modular. Can they be
modular? Is there another way to deal with
closures?

  - recursion: This suffers from a similar issue
  as closures;

  - modular static semantics and soundness: This
  may be an interesting direction, but
    I mark this as a challenge because I don't
    know on easy this would be.

Also we will have challenges in Figuring out how
to make things work in Coq (example: type classes
for monads).

============================= WHAT HAVE WE
ACHIEVED ALREADY =============================

  - Modular interpreters in a setting without
  general recursion like
    Coq: Although there are approaches to modular
    interpreters, they fundamentally rely on
    general recursion at both the type and value
    level. We have shown how we can exploit Church
    encodings to overcome this problem.

  - Reasoning about Church encodings: it's all
  good and well to define
    semantics using Church encodings, but how do
    we reason about Church encoded program in
    Coq?. Our solution to this lies on the
    observation that Church encodings are
    basically folds and we can reason about them
    using the theory that we know about folds.  We
    (Ben :)) figured the Coq technicalities to
    make this work nicely.

  - Some innovations on Swiestra's Data types a la
  carte (like the
    notion of FAlgebras and laws).

I think these are already effective contributions.
(Although in a paper they may not come as
individual contributions).

========== REFERENCES ==========

  - Laurence Day's thesis provides a nice
  literature review of work on
    modular monadic interpreters:

    \url{http://www.cs.nott.ac.uk/~led/papers/led_transferreport.pdf}

  - The following ESOP paper is interesting as it
  shows proofs based
    on a modular denotational approach:

    Modular Denotational Semantics for Compiler
    Construction: Sheng Liang and Paul Hudak,
    Springer, 1996

  - The seminal paper "A syntactic approach to
  type soundness" is relevant
    due to the argument that denotational-style
    proofs are not reusable if we add new
    extensions. A relevant question is: can monads
    fix this?

  - Coding Recursion a la Mendler
   www.cs.ut.ee/~varmo/papers/wgp00.ps.gz

  Mendler-style recursion, universal properties
  and other goodies.

  - Fold and Unfold for Program Semantics
   http://www.cs.nott.ac.uk/~gmh/semantics.ps

  Argument that folds are great for denotational
  semantics.  Our argument is that folds are a bit
  naive (don't scale to realistic features).
\end{verbatim}
%endif
