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

\section{Strictly Positive Functors}\label{sec:mod:strictlypositivefunctors}

To this end, we define the |SPF| type class in Figure
\ref{fig:strictlypositivefunctor} which serves as a declarative specification of
our requirements on functors and which carries the required evidence.

While we need the existence of a fixed point type of abstract
super-functors, it is inessential how it is constructed. This means
that instead of providing a generic fixpoint type constructor like
|FixDTC| we can alternatively provide a witness of the existence of a
valid fixpoint in the type class, i.e. we make the fixpoint an
associated type of the |SPF| type class.  We thereby delay the problem
of defining it to the specific functors. |SPF| also includes the
functions |inFix| and |outFix| as members that fold/unfold one layer
of the fixpoint.

|SPF| is a sub-class of |Functor| so we would like to define a generic fold
operator similar to DTC's operator |foldDTC| from Section
\ref{sec:mod:datatypesalacarte}.

> foldF :: SPF f => Algebra f a -> Fix f -> a
> foldF alg = alg . fmap (foldF alg) . outFix

Unfortunately, this definition is not structurally recursive and Coq
is not able to determine its termination automatically. Hence, this
definition is rejected. This is similar to the problem of |Fix|. For
any concrete functor we can inline the definition of |fmap| to let
|foldF| pass the termination check, but again we are working with an
abstract functor |f| and an abstract functorial mapping
|fmap|. Similarly, we resolve this by including a witness for the
existence of a valid fold operator in the |SPF| class.

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


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
