
%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%if False

> {-# LANGUAGE DataKinds, KindSignatures, GADTs, ExistentialQuantification, PolyKinds, TypeFamilies, TypeOperators, ScopedTypeVariables #-}

%endif

\section{Polynomial Functors}\label{sec:mod:polynomial}

In the previous section we have implemented generic functions for functorial
mappings, fixed points, folds and generic proofs about their properties.

Other common functionality can be provided with generic implementations as
well. In this section we look at a generic implementation of equality testing
and proofs about its correctness. Equality testing is used for example in the
MTC framework in the implementation of a modular type-checker that tests if both
branches of an |if| expression have the same type and that the function and
argument type of a function application are compatible. Furthermore for
reasoning about functions that use equality testing we need proofs of its
correctness. We thus include the equality function and the properties in an
equality type class that is shown in Figure \ref{fig:equalityclass}.


\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

%{
%format ^^ = "\enspace"
%format <> = "\neq"

< class Eq a where
<   eq       :: a -> a -> Bool
<   eqTrue   :: forall x y. ^^ eq x y = True   -> xs = ys
<   eqFalse  :: forall x y. ^^ eq x y = False  -> xs <> ys

%}

\end{minipage}
}
\caption{Equality type class}
\label{fig:equalityclass}
\end{figure}


When choosing an approach to generic programming there is a trade-off between
the expressivity of the approach, i.e. the collection of types it covers, and
the functionality that can be implemented generically using the approach. The
container universe is a very expressive universe that supports a generic
definitoin of fold and hence is well-suited as a solution for modularly defining
datatypes and functions. However, it is too expressive for implementing equality
generically as it also includes function types for which equality is in general
not decidable.

So instead we restrict ourselves to the universe of polynomial functors to
implement equality generically. \steven{Motivate the choice of the universe. Add
  a citation.}

\subsection{Universe}

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

> data Poly = U | I | C Poly Poly | P Poly Poly

> data ExtP (c :: Poly) (a :: *) where
>   EU  :: ExtP U a
>   EI  :: a -> ExtP I a
>   EL  :: ExtP c a -> ExtP (C c d) a
>   ER  :: ExtP d a -> ExtP (C c d) a
>   EP  :: ExtP c a -> ExtP d a -> ExtP (P c d) a

<  class Polynomial f where
<    pcode              :: Poly
<    pto                :: ExtP pcode a -> f a
<    pfrom              :: f a -> ExtP pcode a
<    ptoFromInverse     :: forall a. pto (pfrom a) = a
<    pfromToInverse     :: forall a. pfrom (pto a) = a

\end{minipage}
}
\caption{Polynomial functors}
\label{fig:polynomialuniverse}
\end{figure}

The codes |Poly| and interpretation |ExtP| of the polynomial functor
universe are shown in Figure \ref{fig:polynomialuniverse}. A
polynomial functor is either the constant unit functor |U|, the
identity functor |I|, a coproduct |C p1 p2| of two functors, or the
cartesian product |P p1 p2| of two functors. The interpretation |ExtP|
is defined as an inductive family indexed by the codes.


As an example consider the functor |FunType| that can represent
function types of an object language.

> data FunType a = TArrow a a

It has a single constructor with two recursive positions for the
domain and range types. Hence it can be represented by the code |P I
I|. The conversion functions between the generic and conventional
representation are given by

> fromFunType :: FunType a -> ExtP (P I I) a
> fromFunType (TArrow x y) = EP (EI x) (EI y)

> toFunType :: ExtP (P I I) a -> FunType a
> toFunType (EP (EI x) (EI y)) = TArrow x y

As before we define a type-class |Polynomial| that carries the
conversion functions and isomorphism proofs. The definition of the
class is also given in Figure \ref{fig:polynomialuniverse}. An
instance for |FunType| is the following, with proofs omitted:

< instance Polynomial FunType where
<   pcode              = P I I
<   pto                = toFunType
<   pfrom              = fromFunType
<   ptoFromInverse     = ...
<   pfromToInverse     = ...


\subsection{Universe Embedding}

To write modular functions for polynomial functors we proceed in
the same way as in Section \ref{sec:mod:containers} by showing that
|Polynomial| is closed under coproducts and building the functionality
of the |SPF| type class generically.

However, that would duplicate the generic functionality and would
prevent us from using polynomial functors with containers. Since
containers are closed under products and coproducts we can embed the
universe of polynomial functors in the universe of containers. In
order to do this, we have to derive a shape type from the code of a
polynomial functor and a family of position types for each shape. We
can compute the shape by recursing over the code.

< PolyS :: Poly -> *
< PolyS U        = ()
< PolyS I        = ()
< PolyS (C c d)  = PolyS c + PolyS d
< PolyS (P c d)  = (PolyS c , PolyS d)

The constant unit functor and the identity functor have only one shape
which is represented by a unit type. As in section
\ref{sec:mod:containers} the shape of a coproduct is the
coproduct of the shapes of the summands and the shape of a product is
the product of shapes of the factors. The definition of positions also
proceeds by recursing over the code.

< PolyP :: (c :: Poly) -> PolyS c -> *
< PolyP U        ()         = Empty
< PolyP I        ()         = ()
< PolyP (C c d)  (Left s)   = PolyP c s
< PolyP (C c d)  (Right s)  = PolyP d s
< PolyP (P c d)  (s1 , s2)  =
<   Either (PolyP c s1) (PolyP d s2)

The constant unit functor does not have any positions and the identity
functor has exactly one position. For coproducts the positions are the
same as the ones of the chosen summand and for a product we take the
disjoint union of the positions of the shapes of the components.

The next essential piece for completing the universe embedding are
conversions between the interpretations of the codes. The function
|ptoCont| converts the polynomial interpretation to the container
intepretation.

< ptoCont ::  (c :: Poly) ->
<             ExtP c a -> Ext (PolyS c |> PolyP c) a
< ptoCont U        EU         = Ext () (\p -> case p of)
< ptoCont I        (EI a)     = Ext () (\() -> a)
< ptoCont (C c d)  (EL x)     = Ext (Left s) pf
<   where  Ext s pf = ptoCont c x
< ptoCont (C c d)  (ER y)     = Ext (Right s) pf
<   where  Ext s pf = ptoCont c y
< ptoCont (P c d)  (EP x y)   = Ext  (s1 , s2)
<                                    (\p -> case p of
<                                       Left p   -> pf1 p
<                                       Right p  -> pf2 p)
<   where  Ext s1 pf1 = ptoCont c x
<          Ext s2 pf2 = ptoCont d y

Similarly we define the function |pfromCont| that performs the conversion in the
opposite direction. We omit the implementation.

< pfromCont ::
<   (c :: Poly) -> Ext (PolyS c |> PolyP c) a -> ExtP c a

To transport properties, like the correctness of equality in Figure
\ref{fig:equalityclass}, across these conversion functions we need to prove that
they are inverses. These proofs proceed by inducting over the code; we omit them
here.

As the last step we derive an instance of |Container| from an instance of
|Polynomial|. This way all the generic functionality of containers is also
available for polynomial functors.

< instance Polynomial f => Container f where
<   cont    =  PolyS pcode |> PolyP pcode
<   from    =  ptoCont pcode . pfrom
<   to      =  pto . pfromCont pcode
<   fromTo  =  ...
<   toFrom  =  ...


\subsection{Generic Equality}

Performing the conversions between polynomial functors and containers in the
definition of recursive functions makes it difficult to convince the termination
checker to accept these definitions. So instead of using the generic fixed point
provided by the container universe we define a generic fixed point on the
polynomial functor universe directly.

> data FixP (c :: Poly) = FixP (ExtP c (FixP c))

We define the generic equality function |geq| mutually recursively with |go|
that recurses over the codes and forms an equality function for a partially
constructed fixed point.

< geq :: (c :: Poly) -> FixP c -> FixP c -> Bool
< geq c (FixP x) (FixP y) = go c x y
<   where
<     go ::  (d :: Poly) ->
<            ExtP d (FixP c) -> ExtP d (FixP c) -> Bool
<     go U        EU         EU         = True
<     go I        (EI x)     (EI y)     = geq x y
<     go (C c d)  (EL x)     (EL y)     = go c x y
<     go (C c d)  (EL x)     (ER y)     = False
<     go (C c d)  (ER x)     (EL y)     = False
<     go (C c d)  (ER x)     (ER y)     = go d x y
<     go (P c d)  (EP x x')  (EP y y')  =
<       go c x y && go d x' y'

In the same vein we can prove the properties of the |Eq| type class for this
equality function using mutual induction over fixed points and partially
constructed fixed points.

Of course |FixP c| and |Fix (PolyS c ||> PolyP c)| are isomorphic and we can
transport functions and their properties across this isomorphism to get a
generic equality function on the fixed point defined by containers for a
conventional polynomial functor which can be used to instantiate the |Eq| type
class in Figure \ref{fig:equalityclass}.

< instance Polynomial f => Eq (Fix f)




%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
