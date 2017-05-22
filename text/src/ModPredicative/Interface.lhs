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

\section{Programming and Reasoning}
\label{sec:modpred:strictlypositivefunctors}

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

< class Functor f => PFunctor f where
<   type All :: forall a. (a -> Prop) -> f a -> Prop
<
< type PAlgebra f a (alg :: Algebra f a) (p :: a -> Prop) =
<   PFunctor f => forall ((xs :: f a)). All p xs -> p (alg xs)
<
< class PFunctor f => SPF (f :: * -> *) where
<   -- Programming interface
<   type Fix          :: *
<   inFix             :: f (Fix f) -> Fix f
<   outFix            :: Fix f -> f (Fix f)
<   fold              :: Algebra f a -> Fix f -> a
<
<   -- Reasoning interface
<   in_out_inverse    :: forall e. inFix (outFix e) = e
<   out_in_inverse    :: forall e. outFix (inFix e) = e
<   fold_uniqueness   ::
<    forall a (alg :: Algebra f a) h.
<      (forall e. h (inFix e) = alg (fmap h e)) ->
<      forall x. h x = fold alg x
<   fold_computation  ::
<     forall a (alg :: Algebra f a) (x :: a),
<       fold alg (inFix x) = alg (fmap (fold alg) x)
<   ind               ::
<     forall p. PAlgebra inFix p -> forall x. p x

\end{minipage}
}
\caption{Strictly-positive functor class}
\label{fig:strictlypositivefunctor}
\end{figure}

This section defines an interface to our approach that provides both, a
programming part that is equivalent to DTC's functionality, and a reasoning
part. The goal is to hide the implementation details as much as possible, by
using an abstract declarative specification of what the implementation provides,
and yet provide an interface that is sufficient enough to program with and
reason about modular datatypes. We turn to a specific implementation using
containers in Section \ref{sec:mod:containers}.

Similar to DTC
%in Section \ref{sec:mod:datatypesalacarte}
and MTC
% in Section \ref{sec:mod:mtc}
our approach relies on fixed-points of functors to model datatypes, folds to
implement functions on datatypes and on abstraction over \emph{super-functors}
and \emph{super-algebras} to achieve modularity in programming and reasoning.
However, the modular composition of signature functor, function algebras and
proof algebras is not an essential part of the fixed-point construction, but is
rather dealt with in another layer. The only concern for the fixed-point
construction in our interface is the support for modularity through opening up
the recursion.

\subsection{Programming Interface}
The |SPF| type class in Figure \ref{fig:strictlypositivefunctor} is a core part
of the interface that serves as a declarative specification of our requirements
on functors and carries the required evidence. We discuss each concept that
appear in the type class in turn starting with the programming related parts.

\paragraph{Fixed-Points}
While we need the existence of a fixed-point type of \emph{abstract
  super-functors}, it is inessential how it is constructed. This means that
instead of providing a generic fixed-point type constructor like |FixDTC| we can
alternatively provide a witness of the existence of a valid fixed-point in the
type class, i.e. we make the fixed-point an associated type of the |SPF| type
class. We thereby delay the problem of defining it until the final signature
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



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
