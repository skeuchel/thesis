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
motivate some of the made choices. \Knot has two different kinds of
meta-variables. The intuition behind them and their treatment are discussed in
Section \ref{ssec:knotdesign:localglobal}. Sections
\ref{ssec:knotdesign:contextparametricity} and \ref{ssec:knotdesign:freemonad}
explain restrictions that \Knot puts on rules of relations to guarantee that
boilerplate lemmas for them can be automatically generated.

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

%-------------------------------------------------------------------------------
\subsection{Free Monadic Presentations}\label{ssec:knotdesign:freemonad}

One of the remaining questions is for which class of languages is the
substitution boilerplate derivable? To find the answer to this question, observe
that it is folklore that the syntax of lambda calculi has a \emph{monadic
  presentation}: We can for example model well-scoped terms of the untyped
lambda calculus as an ordinary monad on sets using nested datatypes
\cite{nested,monadic}, or well-scoped and well-typed terms of the simply-typed
lambda calculus using a generalization of monads
\cite{monadic,monadsnotendo,relativemonads}. In these cases, the variable
constructor represents the \emph{unit} of the monad and (simultaneous)
substitution of all variables the \emph{bind}.

The unit and bind morphism for monads on sets are not generically derivable.
However, for the class of \emph{free monads} the operations are derivable from a
base functor. Moreover, we can generically derive the functorial mapping for
strictly-positive functors. Consequently, we can derive a monad for every
datatype that has the structure of a free monad.

We take this fact and mimick the free monad construction on syntax: we requirie
that every sort with variables in \Knot has a \emph{free monadic presentation}.

\begin{itemize}
\item Revise Free Monads on sets in Haskell.
\item Well-scoped terms of the untyped lambda calculus.
\item
\end{itemize}




%% Influence the design of the specification language and give feedback to users
%% about problematic parts of her specification.

\subsubsection{Free Monads on Sets in Haskell}\label{sssec:freemonad:haskell}

%{
%format FreeSet = "{" Free  "}_{" Set "}"
%format ReturnSet = "{" Return  "}_{" Set "}"
%format StepSet = "{" Step  "}_{" Set "}"

%format FreeStx = "{" Free  "}_{" Stx "}"
%format ReturnStx = "{" Return  "}_{" Stx "}"
%format StepStx = "{" Step  "}_{" Stx "}"
%format MonadStx = "{" Monad  "}_{" Stx "}"
%format FunctorStx = "{" Functor  "}_{" Stx "}"
%format fmapstx = "{" fmap  "}_{" Stx "}"
%format returnstx = "{" return  "}_{" Stx "}"
%format bindstx = "{" bind  "}_{" Stx "}"

%format substLam = "{" subst  "}_{" Lam "}"
%format upSubLam = "{" upSub  "}_{" Lam "}"

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
type Tree' = Free Either
\end{code}


\subsubsection{Well-scoped Lambda Terms}

{ % FEXISTSPROD SCOPE

%\input{src/MacrosFExists}
\newcommand{\wellscopedtermvar}[2]{{#1} \vdash^\text{var}_\text{tm} {#2}}

We can define the well-scoped terms of the untyped lambda calculus using
generalized algebraic datatypes (GADTs). This represantation is also known as
intrinsically well-scoped de Bruijn terms. Figure
\ref{fig:freemonad:wellscopedlambda} shows the construction. We use natural
numbers to denote the number of variables that are in scope and bounded naturals
|Fin d| to represent variables. In essence, |Fin d| corresponds to the
well-scopedness predicates on variables $\wellscopedtermvar{d}{n}$ in Figure
\ref{fig:wellscopedness:overview} with the term-level index |n| removed. The
|Lam| type encodes the well-scoped lambda terms. The parameter |d| encodes the
free variables that can potentially appear. In the case of an abstraction its
incremented to account for the new lambda-bound variable. Figure
\ref{fig:freemonad:wellscopedlambda} also defined a simultaneous substitution
operator |substLam|. A substitution is represented using functions of type |Fin
d₁ -> Lam d₂| that substitutes all |d₁|-variables by lambda terms with free
variables in |d₂|. When going under a lambda binder during the substitution
needs to be adjusted for the introduced variable which is handled by |upSubLam|.
\footnote{See \cite{monadic} for a termination argument for the mutually
  recursively defined |substLam| and |upSubLam|.} |Lam| together with its
simultaneous substitutions form a Kleisli triple in the sense of \cite{monadic}
and a monad relative on |Fin| in the sense of
\cite{monadsnotendo,relativemonads}.
}

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

\subsubsection{Free Monadic Well-Scoped Terms}

Notice, that similar to the bind of the |Tree| datatype, the substitution
operator of |Lam| only applies the substitution in the variable case and passes
it through otherwise. This suggests, that we may copy the construction of a free
monad on sets from base functors of kind |* -> *| to functors of kind |(Nat ->
*) -> (Nat -> *)|. The datatype |FreeStx| in Figure
\ref{fig:freemonad:freewellscoped} shows how this idea is applied. Notice that
the representation of variables is not fixed to be |Fin| but turned into a
parameter for uniformity with |FreeSet|.

One of the problems is how to represent morphisms between two families |v w ::
Nat -> *| when functorially mapping |f v d -> f w d|. In general, we cannot lift
a function of type |v d₁ → w d₂| to a function of type |v (S d₁) → w (S d₂)|. We
side-step this issue by abstracting away over the representation |m| of such
morphisms in the functorial mapping and the monadic bind and require an
interpretation function |forall d₁ d₂. m d₁ d₂ -> v d₁ -> w d₂|.

\begin{figure}[t!]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      data FreeStx (f :: (Nat -> *) -> (Nat -> *)) v d where
        ReturnStx  :: v d -> FreeStx f v d
        StepStx    :: f (FreeStx f v) d -> FreeStx f v d

      class FunctorStx (f :: (Nat -> *) -> (Nat -> *)) where
        fmapstx    :: forall (v :: Nat -> *) (w :: Nat -> *) (m :: Nat -> Nat -> *).
                      (forall d₁ d₂. m d₁ d₂ -> m (S d₁) (S d₂)) ->
                      (forall d₁ d₂. m d₁ d₂ -> v d₁ -> w d₂) ->
                      forall d₁ d₂.
                      m d₁ d₂ -> f v d₁ -> f w d₂

      class MonadStx (f :: (Nat -> *) -> (Nat -> *)) where
        returnstx  ::  v d -> f v d
        bind       ::  forall (v :: Nat -> *) (w :: Nat -> *) (m :: Nat -> Nat -> *).
                       (forall d₁ d₂. m d₁ d₂ -> m (S d₁) (S d₂)) ->
                       (forall d₁ d₂. m d₁ d₂ -> v d₁ -> f w d₂) ->
                       forall d₁ d₂.
                       f v d₁ -> m d₁ d₂ -> f w d₂

      instance FunctorStx f => MonadStx (FreeStx f) where
        returnstx = ReturnStx
        bind up int t f = case t of
          ReturnStx x  -> int f x
          StepStx x    -> StepStx (fmapstx up (flip (bind up int)) f x)
      \end{code}
    \end{minipage}
  }
  \caption{Free Monads for Well-Scoped Terms}
  \label{fig:freemonad:freewellscoped}
\end{figure}


\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      newtype Sub (f :: (Nat -> *) -> (Nat -> *)) d₁ d₂ where
        Sub :: { fromSub :: Fin d₁ -> f Fin d₂ } -> Sub f d₁ d₂

      upSub :: MonadStx f => Sub f d₁ d₂ -> Sub f (S d₁) (S d₂)
      upSub (Sub m) = Sub $ \x -> case x of
        FZ   -> returnstx FZ
        FS x -> subst (m x) (returnstx . FS)

      subst :: MonadStx f => f Fin d₁ -> (Fin d₁ -> f Fin d₂) -> f Fin d₂
      subst t = bind upSub fromSub t . Sub
      \end{code}
    \end{minipage}
  }
  \caption{Free Monads in Haskell}
  \label{fig:freemonad:set}
\end{figure}

\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      data LamF (v :: Nat -> *) (d :: Nat) where
        AppF :: v d -> v d -> LamF v d
        AbsF :: v (S d) -> LamF v d

      instance FunctorStx LamF where
        fmapstx up int f t = case t of
          AppF t₁ t₂  -> AppF (int f t₁) (int f t₂)
          AbsF t      -> AbsF (int (up f) t)

      type Lam' = FreeStx LamF Fin

      substLam' :: Lam' d₁ -> (Fin d₁ -> Lam' d₂) -> Lam' d₂
      substLam' = subst
      \end{code}
    \end{minipage}
  }
  \caption{Free Monads in Haskell}
  \label{fig:freemonad:set}
\end{figure}


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


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
