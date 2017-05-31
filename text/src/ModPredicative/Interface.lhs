%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%if False

> class Functor f => SPF f where
>   type Fix f
>   inFix  :: f (Fix f) -> Fix f
>   outFix :: Fix f -> f (Fix f)

%endif

\section{Declarative Specification}
\label{sec:modpred:strictlypositivefunctors}

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

< class Functor f => PFunctor f where
<   type All          ::  forall a. (a -> Prop) -> f a -> Prop
<   all_natural       ::  forall a b (g :: a -> b) (p :: b -> Prop) (xs :: f a).
<                           All (\x -> p (g x)) xs <-> All p (fmap g xs)
<
< type PAlgebra f a (alg :: Algebra f a) (p :: a -> Prop) =
<   PFunctor f => forall ((xs :: f a)). All p xs -> p (alg xs)
<
< class PFunctor f => SPF (f :: * -> *) where
<   -- Fixed-points
<   type Fix          ::  *
<   inFix             ::  f (Fix f) -> Fix f
<   outFix            ::  Fix f -> f (Fix f)
<   in_out_inverse    ::  forall ((e :: Fix f)).      inFix (outFix e) = e
<   out_in_inverse    ::  forall ((e :: f (Fix F))).  outFix (inFix e) = e
<
<   -- Folds
<   fold              ::  forall a. Algebra f a -> Fix f -> a
<   fold_uniqueness   ::  forall a (alg :: Algebra f a) h.
<                           (forall e. h (inFix e) = alg (fmap h e)) ->
<                           forall x. h x = fold alg x
<   fold_computation  ::  forall a (alg :: Algebra f a) (x :: a),
<                           fold alg (inFix x) = alg (fmap (fold alg) x)
<
<   -- Induction
<   ind               ::  forall ((p :: Fix f -> Prop)). PAlgebra inFix p -> forall e. p e

\end{minipage}
}
\caption{Strictly-positive functor class}
\label{fig:strictlypositivefunctor}
\end{figure}

Similar to DTC
%in Section \ref{sec:mod:datatypesalacarte}
and MTC
% in Section \ref{sec:mod:mtc}
our approach relies on fixed-points of functors to model datatypes, folds to
implement functions on datatypes and on abstraction over \emph{super-functors}
and \emph{super-algebras} to achieve modularity in programming and reasoning.
We do not lump all of these concepts together in one interface because 
the modular composition of signature functor, function algebras and
proof algebras is not an essential part of the fixed-point construction. The
only concern for the fixed-point construction in our interface is the support
for modularity through opening up the recursion. We therefore separate the code
concerning fixed-points into a backend layer and abstract over its
implementation by defining a declarative specification of fixed-points and
related definitions of algebras, folds, proof algebras and induction. This
section describes the \emph{declarative specification} and Section
\ref{sec:mod:containers} presents a backend implementation based on container
types. The user-facing frontend differs from MTC mainly in the use of
\emph{modular proof algebras} and \emph{modular induction principles}. These
differences are discussed in Section \ref{sec:modpred:frontend}.

%% This section defines an interface to our approach that provides both a
%% programming part that is equivalent to DTC's functionality, and a novel
%% reasoning part. The goal is to hide the implementation details as much as
%% possible, by using an abstract declarative specification of what the
%% implementation provides, and yet provide an interface that is sufficient enough
%% to program with and reason about modular datatypes. We turn to a specific
%% implementation of this interface in terms of containers in Section
%% \ref{sec:mod:containers}.


\subsection{Programming Interface}
The |SPF| type class in Figure \ref{fig:strictlypositivefunctor} is a core part
of the interface that serves as a declarative specification of our requirements
on functors and carries the required evidence. We discuss each concept that
appears in the type class in turn starting with the programming related parts.

\paragraph{Fixed-Points}
While we need the existence of a fixed-point type of \emph{abstract
  super-functors}, it is inessential how this is constructed. This means that
instead of providing a generic fixed-point type constructor like |FixDTC| we can
alternatively provide a witness of the existence of a valid fixed-point in the
type class, i.e. we make the fixed-point an associated type of the |SPF| type
class. We thereby delay the problem of defining the fixpoint until the final signature
functor composition is created. At this point the user can either use the
generic fixed-point combinator that we define in Section
\ref{sec:mod:containers} or even define his own. |SPF| also includes the initial
algebra function |inFix| and its inverse |outFix| as members to fold/unfold one
layer of the fixed-point. Furthermore, the members |in_out_inverse| and
|out_in_inverse| are witnesses that folding/unfolding of the fixpoint type form
inverse operations.

\paragraph{Fold Operator}
|SPF| is a subclass of |Functor| so we would like to define a generic fold
operator similar to DTC's operator |foldDTC| from Section
\ref{sec:mod:datatypesalacarte}.

> foldF :: SPF f => Algebra f a -> Fix f -> a
> foldF alg = alg . fmap (foldF alg) . outFix

Unfortunately, this definition is not structurally recursive and Coq is not able
to determine its termination automatically. Hence, this definition is
rejected. This is similar to the problem of |Fix|. For any concrete functor we
can inline the definition of |fmap| to let |foldF| pass the termination check,
but again we are working with an abstract functor |f| and an abstract functorial
mapping |fmap|. We resolve this similarly by including a witness for the
existence of a valid fold operator in the |SPF| class and also witnesses
that the fold operator satisfies the universal property of folds.


%-------------------------------------------------------------------------------
\subsection{Inductive Reasoning Interface}
\label{sec:mod:modularinductivereasoning}

The |SPF| typeclass also provides an interface for inductive reasoning in terms
of an induction principle. In general, the type of an induction principle
depends on the number of constructors of a datatypes and their arities
which makes a generic definition difficult.

%{
%format . = "."

For example, consider the induction principle |indArith| for arithmetic
expressions:

< indArith ::  forall ((p   :: Arith -> Prop)).
<              forall ((hl  :: forall n.                   p (Lit n)))).
<              forall ((ha  :: forall x y.  p x -> p y ->  p (Add x y)))).
<              forall ((x :: Arith)). p x

%}

It takes a proposition |p| as parameter and inductive steps |hl| and |ha| for
each case. % of the initial algebra.
We say that |hl| and |ha| together form a \emph{proof algebra} of |p|. An
inductive step consists of showing |p| for an application of the initial algebra
given proofs of |p| for all recursive positions. In case of a literal we have no
recursive positions and in case of addition we have two. Proof algebras for
other datatypes differ in the number of cases and the number of recursive
positions.

For a generic definition of induction, we first need to develop a \emph{uniform
  representation of induction} which effectively boils down to developing a
\emph{uniform representation of proof algebras} which is the subject of the
remainder of this section.

\paragraph{All Modalities}

We first focus on the inputs of the proof algebra functions, i.e. the proofs
that the induction predicate holds for recursive positions. We use an \emph{all
  modality}~\cite{benke:universes} for signature functors to capture these
proofs. Informally, the all modality of a functor |f| and a predicate (|p :: a
-> Prop|) is a new type (|All a p :: f a -> Prop|) that denotes that the
predicate |p| holds for each (|x :: a|) in an (|f a|).

\paragraph{Example: Arithmetic Expressions}
The following type |ArithAll| is an example of an all modality for the signature
functor |ArithF| of arithmetic expressions. The constructor |ALit| encodes that
the all modality holds for literals and |AAdd| encodes that the all modality
holds for |(Add x y)| if |p| holds for both recursive positions |x| and |y|.

< data ArithAll a p :: ArithF a -> Prop where
<   ALit  ::                ArithAll a p (LitF n)
<   AAdd  :: p x -> p y ->  ArithAll a p (AddF x y)


Using the all modality definition we can write |indArith| equivalently as

%format inArith = "{\Varid{in}_{" Arith "}}"
%format indArith' = ind "_{" A "}\prime"


< indArith' ::  forall ((p  :: Arith -> Prop)).
<               forall ((h  :: forall ((xs :: ArithF Arith)). ArithAll p xs -> p (inArith xs))).
<               forall ((x :: Arith)). p x
<
< inArith :: ArithF Arith -> Arith
< inArith (LitF n)    =  Lit n
< inArith (AddF x y)  =  Add x y

The induction principle now takes a \emph{single argument} |h| that represents
the \emph{proof algebra} independent of the number of cases and arity of
constructors. Notice in particular the result of |h|. The constructor
applications in the result of the proof algebra functions of |indArith| are now
combined into a single application of the initial algebra |inArith| of |Arith|.

\paragraph{PFunctor Class}
We introduce a new typeclass |PFunctor| that carries the associated all modality
type and make |SPF| a subclass of it.


%{
%format . = "."


%}

\paragraph{Proof Algebras}

The proof algebra is now a single parameter |h|. Note that |h| shows that |p|
holds for an application of the initial algebra |inFix|. In the modular setting
however, we only want to provide proofs for sub-algebras of the initial algebra
that correspond to specific signatures and combine these \emph{proof
  sub-algebras} to a complete proof algebra for the initial algebra. To this
end, we define proof algebras in Figure \ref{fig:strictlypositivefunctor} more
generally over arbitrary algebras |alg|.

\paragraph{Induction Operator}
As a last member of |SPF| we introduce |ind| that is an induction principle for
the fixed-point type |Fix|. It takes a proof algebra of a property |p| for the
initial algebra and constructs a proof for every value of |Fix|.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
