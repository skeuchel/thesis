%include lhs2TeX.fmt
%include forall.fmt
%include Formatting.fmt

%if False

\begin{code}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude (flip, (.), ($), Functor(..), Monad(..), undefined)

class Monad f where
  return :: a -> f a
  (>>=)  :: f a -> (a -> f b) -> f b
\end{code}

%endif


%-------------------------------------------------------------------------------
\section{Key Design Choices}\label{sec:knotdesign}

This section discusses concepts, that influenced the design of \Knot, which
makes it easier to understand the specification of \Knot in the next section and
motivate some of the made choices. Section \ref{ssec:knotdesign:freemonad}
explain requirements that \Knot puts on sorts to guarantee that boilerplate
lemmas for them can be automatically generated. \Knot has two different kinds of
meta-variables. The intuition behind them and their treatment are discussed in
Section \ref{ssec:knotdesign:localglobal}. Section
\ref{ssec:knotdesign:contextparametricity} extends the requirements of Section
\ref{ssec:knotdesign:freemonad} from sorts to relations to ensure that their
boilerplate is derivable.

%-------------------------------------------------------------------------------
\subsection{Free Monadic Presentations}\label{ssec:knotdesign:freemonad}

One of the remaining questions is for which class of languages is the
substitution boilerplate derivable? To find the answer to this question, observe
that it is folklore that the syntax of lambda calculi has a monadic structure:
We can for example model well-scoped terms of the untyped lambda calculus as an
ordinary monad on sets using nested datatypes \cite{nested,monadic}, or
well-scoped and well-typed terms of the simply-typed lambda calculus using a
generalization of monads \cite{monadic,monadsnotendo,relativemonads}. In these
cases, the variable constructor represents the \emph{unit} (also called return)
of the monad and (simultaneous) substitution of all variables the \emph{bind}.

However, the syntax of lambda calculi not only has a monadic structure, but it
even has a structure that is similar to \emph{free monads}. This is very
fortunate since the monadic operations of free monads are derivable from a base
functor. We use this in the design of \Knot and require that all sorts with
variables follow this structure to make substitutions generically derivable.

We will briefly revise the free monads and their generic construction in
Haskell. Subsequently, we present a Haskell definition of well-scoped terms of
the untyped lambda calculus and relate it to the generic definition of free
monads. Finally, we discuss the design implications for the \Knot specification
language.

\subsubsection{Free Monads on Sets in Haskell}\label{sssec:freemonad:haskell}

%{
%% Reset global formatting
%format Z = "\Conid{Z}"

Consider the monad of leafy binary trees |Tree|.

\begin{code}
data Tree a = Leaf a | Fork (Tree a) (Tree a)

instance Monad Tree where
  return           = Leaf
  Leaf a    >>= m  = m a
  Fork l r  >>= m  = Fork (l >>= m) (r >>= m)
\end{code}

The return of the monad is given by constructing a leaf from a value and the
monadic bind replaces a leaf by a new tree depending on which value the leaf
contained. Or put differently, the bind encodes a simultaneous substitution of
leaves by trees. The tree datatype has a particular structure: The |Leaf|
constructor that forms the return of the monad is the only one that contains
a value of the parameter type. Such monads are \emph{free monads} and can
be generically constructed from a base pattern functor.

Figure \ref{fig:freemonad:set} shows the generic free monad construction.
|FreeSet| constructs a free monad for a given pattern functor. The effect on
variables is completely defined in the instance and we only need to traverse
|f|-structures to get to the variable cases. Consequently, the |Monad| instance
only requires functoriality of |f|.

\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      data FreeSet f a where
        ReturnSet  ::  a -> FreeSet f a
        StepSet    ::  f (FreeSet f a) -> FreeSet f a

      instance Functor f => Monad (FreeSet f) where
        return   =  ReturnSet
        t >>= f  =  case t of
          ReturnSet a  ->  f a
          FreeSet x    ->  FreeSet (fmap (>>=f) x)
      \end{code}
    \end{minipage}
  }
  \caption{Free Monads in Haskell}
  \label{fig:freemonad:set}
\end{figure}

We can then alternatively define |Tree| using |FreeSet| and inherit the
generic |Monad| instance for free:

\begin{code}
type Tree' = Free (,)
\end{code}


\subsubsection{Well-scoped Lambda Terms}\label{sssec:freemonad:wellscopedexample}

\begin{figure}[t!]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      data Nat = Z | S Nat

      data Fin (d :: Nat) where
        FZ  ::  Fin (S d)
        FS  ::  Fin d -> Fin (S d)

      data Lam (d :: Nat) where
        Var  ::  Fin d -> Lam d
        App  ::  Lam d -> Lam d -> Lam d
        Abs  ::  Lam (S d) -> Lam d

      substLam :: Lam d₁ -> (Fin d₁ -> Lam d₂) -> Lam d₂
      substLam (Var x)      m = m x
      substLam (App t1 t2)  m = App (substLam t1 m) (substLam t2 m)
      substLam (Abs t)      m = Abs (substLam t (upSubLam m))

      upSubLam :: (Fin d₁ -> Lam d₂) -> (Fin (S d₁) -> Lam (S d₂))
      upSubLam m FZ      = Var FZ
      upSubLam m (FS x)  = substLam (m x) (Var . FS)
      \end{code}
    \end{minipage}
  }
  \caption{Intrinsically Well-Scoped de Brujn terms}
  \label{fig:freemonad:wellscopedlambda}
\end{figure}

{ % FEXISTSPROD SCOPE

%\input{src/MacrosFExists}
\newcommand{\wellscopedtermvar}[2]{{#1} \vdash^\text{var}_\text{tm} {#2}}

We can define the well-scoped terms of the untyped lambda calculus using
generalized algebraic datatypes (GADTs). This representation is also known as
\emph{intrinsically well-scoped de Bruijn terms}\cite{stronglyttypedterm}.
Figure \ref{fig:freemonad:wellscopedlambda} shows the construction. We use
natural numbers to denote the number of variables that are in scope and bounded
naturals |Fin d| to represent variables. In essence, |Fin d| corresponds to the
well-scopedness predicates on variables $\wellscopedtermvar{d}{n}$ in Figure
\ref{fig:wellscopedness:overview} with the term-level index |n| removed. The
|Lam| type encodes the well-scoped lambda terms. The parameter |d| encodes the
free variables that can potentially appear. In the case of an abstraction its
incremented to account for the new lambda-bound variable. Figure
\ref{fig:freemonad:wellscopedlambda} also defined a simultaneous substitution
operator |substLam|. A substitution is represented using functions of type |Fin
d₁ -> Lam d₂| that substitutes all |d₁|-variables by lambda terms with free
variables in |d₂|. When going under a lambda binder during the substitution
needs to be adjusted for the introduced variable which is handled by |upSubLam|
\footnote{See \cite{monadic} for a termination argument for the mutually
  recursively defined |substLam| and |upSubLam|.}. |Lam| together with its
simultaneous substitutions form a Kleisli triple in the sense of \cite{monadic}
and a monad relative on |Fin| in the sense of
\cite{monadsnotendo,relativemonads}.
}

Notice, that similar to the bind of the |Tree| datatype, the substitution
operator of |Lam| only applies the substitution in the variable case and
otherwise passes it through unchanged or extended. This suggests, that we may
copy the construction of a free monad on sets to functors on |Nat -> Set|. This
generic construction\footnote{We have not shown that this construction is indeed
  free in any formal sense.} and a generic definition of simultaneous
substitution can be found in Section \ref{ssec:appendix:freemonad} of the
appendix. Also shown in the appendix is an instantiation of |Lam| from a base
functor.


\subsubsection{Design Implications}\label{sssec:freemonad:implications}

We want substitution boilerplate to be derivable for all \Knot specifications
and hence apply the insights of this section by enforcing a free monadic shape
on syntactic sorts with variables. As already indicated in the example
specification in Section \ref{sec:knotbyexample}, we always treat the variable
case separately from the other cases. Furthermore, we require that there is
exactly one one distinguished \emph{variable constructor} per namespace which
has a \emph{reference occurrence} as its only argument. All other constructors
only contain \emph{binding occurrences} and subterms. This rules out languages
for normal forms, but as they require custom behavior (renormalization) during
substitution \cite{anormalform,clf} their substitution boilerplate cannot be
derived generically anyway.

Our interpretation of \Knot specifications using de Bruijn terms and our
implementations differ from the presentation in this Section. We use traditional
algrbraic datatypes for our term representation and extrinsic well-scoping
predicates instead of the intrinsically well-scoped representation of this
section. Both representations are equivalent and this choice does not impact the
derivability of the boilerplate. We use single place shifting and substitution
instead of simultaneous renaming and substitution to make the generalization
to multiple namespaces easier. This is not a restriction since all (well-scoped)
simultaneous substitutions can be written as a sequence of single place shifting
and substitution \cite{debruijndecidability, unidb}.


%}


%% A key principle is the distinction between \emph{locally bound} and \emph{free}
%% variables at the meta-level. This allows us to recognize \emph{context
%% parametric} rules which in turn enables us to extend the \emph{free-monadic
%% view} on syntax \cite{monadic,knotneedle} of \Knot to relations. At the
%% syntax-level this view requires one distinguished \emph{variable constructor}
%% per namespace which has a \emph{reference occurrence} as its only argument and
%% all other constructors only contain \emph{binding occurrences} and subterms.
%%
%% At the level of relations this translates to one distinguished \emph{variable
%%   rule} per namespace (or more specifically per environment clause). This
%% variable rule has a single lookup as its only premise and the sorts of the
%% environment data match the sorts of the indices of the relation. The variable
%% rule uses exactly one \emph{free meta-variable}; all other rules only contain
%% \emph{locally bound} meta-variables and do not feature lookup premises.  In
%% other words, the variable rule is the only not context parametric rule.
%%
%% These restrictions allow us to generically establish the substitution lemmas
%% for relations. Consider the small proof tree on the left:
%% % , where $A$ is the subtree for the typing judgement of $e_1$.
%%
%% The distinction between variable and regular constructors follows
%% straightforwardly from \Knot's free-monad-like view on syntax.  This rules out
%% languages for normal forms, but as they require custom behavior
%% (renormalization) during substitution \cite{anormalform,clf} their substitution
%% boilerplate cannot be defined generically anyway.


%-------------------------------------------------------------------------------
\subsection{Local and Global Variables}\label{ssec:knotdesign:localglobal}

In the variable rule of \fexistsprod{}
\[ \inferrule* [right=\textsc{TVar}]
      {x : \tau \in \Gamma}
      {\typing{\Gamma}{x}{\tau}} \\\\
\]
the variable $x$ is used as a reference and is bound in the context $\Gamma$.

On the other hand, in the judgement
\[ \typing{\Gamma}{(\lambda y : \tau. y)}{\tau \to \tau}. \] the variable $y$
appears in both, a binding position and a reference position.  The reference use
of $y$ has to refer to the enclosing binding and not to a binding in the context
$\Gamma$.

Following the literature on \emph{locally nameless}~\cite{locallynameless} and
\emph{locally named}~\cite{externalinternalsyntax} representations we call $y$ a
\emph{locally bound} variable (aka locally scoped variables \cite{pitts2015}),
or more concisely a \emph{local variable}, and $x$ a \emph{global} or \emph{free
  variable}.

The distinction between local and global variables goes back to at least
Frege~\cite{begriffsschrift} and representations such as locally nameless and
locally named have internalized this distinction. These concepts do not commit
us to a particular representation of variable binding, such as a locally
nameless representation. Rather, these notions arise naturally in
meta-languages.

Frege characterizes global variables as variables that can possibly stand for
anything while local variables stand for something very specific. Indeed, the
variable rule is parameterized over the global (meta-)variable which can refer
to any variable in the typing context. As previously mentioned, $y$ can only
possibly refer to the enclosing binder. This distinction is also visible in the
de Bruijn representation: The variable rule is parameterized over an index for
variable $x$. A local reference, however, is always statically determined. For
instance, the index for $y$ in the judgement above is necessarily 0.

The type-substitutions in the rules \textsc{TTApp} for type-application and
\textsc{TPack} for packing existential types operate on local variables
only.
%%\stevennote{TODO}{This is not really a coincidence. Locally substituting a
%%  global variable is not unthinkable but is very particular.  Can this be
%%  expressed in a good way?}
For reasons, that are explained in Section
\ref{ssec:knotdesign:contextparametricity} below, we enforce substitutions in
the definition of relations to only operate on local variables.

We adopt the Barendregt variable convention in \Knot at the meta-level. Two
locally bound meta-variables that have distinct names are considered to
represent distinct object-variables, or, put differently, distinct local
variables cannot be aliased. However, global meta-variables with distinct names
can be aliased, i.e. represent the same object-variable.


%-------------------------------------------------------------------------------
\subsection{Context Parametricity}\label{ssec:knotdesign:contextparametricity}

The variable rule is special in the sense that it is the only rule where a
global variable is used. The variable rule performs a lookup of the type in the
implicit typing context. More generally, \Knot implicitly assumes that any
global variable, independent of an explicit lookup, is bound in the context.  As
a consequence, the use of a global variable inspects the context.

We call a rule \emph{not context parametric}, iff it makes any assumptions about
the context, e.g. through inspection with a global variable. The variable rule
of \fexistsprod's typing relation is the only not context parametric rule. The
other rules either pass the context through unchanged to the premises, or pass
an extended context to the premises without inspecting the prefix. We call these
rules \emph{context parametric}.

Context parametricity is important for the automatic derivation of boilerplate.
For instance, for the semi-formal substitution lemma of \fexistsprod's typing
relation in Section \ref{sec:gen:semiformal:metatheory}, the inductive step of
each regular rule consists of applying the same rule again modulo commutation of
substitutions. Independent of the language at hand, this is automatically
possible for any context parametric rule.

To understand this, not that in the proof, the substitution is in fact a
substitution of a global variable. Hence, it represents a context change. Since
context parametric rules do not make assumptions about the context, they are
naturally compatible with any changes to the context as long as the change can
be properly reflected in the indices. For this we needed the commutation of two
type substitutions. However, this will always be a substitution of a global
variable which comes from the lemma we are proving, and a local variable from
the definition of the relation. Intuitively, such a commutation is always
possible.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
