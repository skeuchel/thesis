%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%if False

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeInType #-}
> {-# LANGUAGE TypeOperators #-}

> import Data.Kind

-- > import Introduction

%endif


%-------------------------------------------------------------------------------
\section{Containers}\label{sec:mod:containers}

%% \steven{Containers and generic programming help in getting valid
%% definitions of |fold|, |ind| and :+: instances. Use this as a
%% motivation for the section and finally deliver everything until the
%% end.}

The type-class |SPF| of Section \ref{sec:modpred:strictlypositivefunctors}
captures all the requirements on abstract functors for modular programming. We
can modularly compose algebras and proof algebras for semantics functions and
proofs. However, as discussed in Section \ref{mod:pred:spfnotmodular} |SPF|
itself is not modular in the sense that we cannot construct coproducts
(directly). In the example in Section \ref{mod:pred:bigproofexample} we avoided
that issue by manually giving the instance of the |SPF| class for the sum of the
signature functors |ArithF| and |LogicF|. This is essentially the approach taken
by \cite{schwaab:mtp}.

In this section we go the last mile and implement a modular refinement of |SPF|
using datatype-generic programming (DGP) in general and containers in
particular. The problem of defining fixed-points for a class of functors also
arises in many approaches to DGP and we can use the same techniques in our
setting. Containers are one approach to DGP that models a class of functors
which is 1) closed under coproducts 2) and admits a generic implementation of
|SPF|'s methods that respects all the restrictions of the proof-assistant
setting.

Section \ref{mod:pred:universes} discusses universes in general and Section
\ref{mod:pred:containeruniverse} and Section \ref{mod:pred:containeruniverse}
reviews the universe of containers in particular.  Sections
\ref{mod:pred:containercoproduct}, \ref{mod:pred:containerfixandfold} and
\ref{mod:pred:containerinduction} discuss the implementation of coproducts,
fixed-points \& folds and induction respectively. Finally in Section
\ref{mod:pred:containerautomation} we bridge the gap to modular programming.
We show how |Functor|, |PFunctor| and |SPF| are instantiated by containers
and discuss the automation for composing the container instances of a set
of signature functors.


%-------------------------------------------------------------------------------
\subsection{Generic Universes}\label{mod:pred:universes}
In a dependently-typed setting it is common to use a universe for generic
programming~\cite{dgpdt,benke:universes}. A universe consists of two important
parts:

\begin{enumerate}
\item A set |Code| of codes that represent types in the universe.
\item An interpretation function |Ext| that maps codes to types.
\end{enumerate}

There is a large number of approaches to DGP that vary in the class of types
they can represent and the generic functions they admit. For our application we
choose the universe of containers~\cite{constructingstrictlypositivetypes}.

An important property of the container universe is that it can represent all
strictly-positive functors~\cite{constructingstrictlypositivetypes} and allows
folds and induction to be implemented generically. Hence, we meet our goal and
do not loose any expressivity.

In Section \ref{sec:mod:polynomial} we discuss the universe of polynomial
functors. it is a sub-universe of containers in the sense that any polynomial
functor is also a container, but the universe admits more generic functions.  We
use this universe to supplement our approach with a generic implementation of
equality in Section \ref{sec:pred:polynomialequality} to achieve more reuse.


%-------------------------------------------------------------------------------
\subsection{Container Universe}\label{mod:pred:containeruniverse}
The codes of the container universe are of the form |S ||> P| where |S| denotes
a type of shapes and |P :: S -> *| denotes a family of position types indexed by
|S|. The extension |Ext c| of a container |c| in Figure
\ref{fig:containerextension} is a functor. A value of the extensions |Ext c a|
consists of a shape |s :: shape c| and for each position |p :: pos c s| of the
given shape we have a value of type |a|. We can define the functorial mapping
|gfmap| generically for any container.

< gfmap :: (a -> b) -> Ext c a -> Ext c b
< gfmap f (Ext s pf) = Ext s (\p -> f (pf p))

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}


%if False

> data Ext (p :: sk -> *) (a :: *) =
>   forall st. Ext (p st -> a)

> instance Functor (Ext p) where
>   fmap f (Ext pf) = Ext (f . pf)

> data (:>) (s :: *) (p :: s -> *)

%endif

< data Cont where
<   (|>) :: (s :: *) -> (p :: s -> *) -> Cont
<
< shape  (s |> p) = s
< pos    (s |> p) = p
<
< data Ext (c :: Cont) (a :: *) where
<   Ext :: (s :: shape c) -> (pos c s -> a) -> Ext c a

\end{minipage}
}
\caption{Container extension}

\label{fig:containerextension}
\end{figure}


\paragraph{Example}
The functor |ArithF| for arithmetic expressions can be represented as a
container functor using the following shape and position type.

> data ArithS = LitS Int | AddS
> data ArithP :: ArithS -> * where
>   AddP1 :: ArithP AddS
>   AddP2 :: ArithP AddS
> type ArithC = ArithS :> ArithP

The shape of an |ArithF| value is either a literal |Lit| with some
integer value or it is an addition |Add|. In case of |Add| we have two
recursive positions |AddP1| and |AddP2|. |Lit| does not have any
recursive positions.

The isomorphism between |ArithF| and |Ext ArithC| is witnessed
by the following two conversion functions.

< from :: ArithF a -> Ext ArithC a
< from (Lit i)   = Ext (LitS i) (\p -> case p of {})
< from (Add x y) = Ext AddS pf
<   where  pf :: ArithP AddS -> a
<          pf AddP1 = x
<          pf AddP2 = y
< to :: Ext ArithC a -> ArithF a
< to (Ext (LitS i)  pf) = Lit i
< to (Ext AddS      pf) = Add (pf AddP1) (pf AddP2)

Literals do not have recursive positions and hence we cannot come up with a
position value. In Coq one needs to refute the position value |p :: ArithP (Lit
i)| as its type is uninhabited. We use a case distinction without alternatives
as an elimination.

\subsection{Coproducts}\label{mod:pred:containercoproduct}

%{
%format Splus = "S_{+}"
%format Pplus = "P_{+}"
%format S_1   = "S_1"
%format S_2   = "S_2"
%format P_1   = "P_1"
%format P_2   = "P_2"
%format c1    = "c_1"
%format c2    = "c_2"

Given two containers |S_1 ||> P_1| and |S_2 ||> P_2| we can construct a
coproduct. The shape of the coproduct is given by the coproducts of the shape
and the family of position types delegates the shape to the families |P_1| and
|P_2|. Figure \ref{fig:containercoproducts} contains the definitions of shape
and positions of the coproduct and injection functions on the extensions.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}
  \begin{code}
    type Splus = Either S_1 S_2
    type Pplus (Left s)   = P_1 s
    type Pplus (Right s)  = P_2 s


    inl :: Ext (S_1 |> P_1) -> Ext (Splus |> Pplus)
    inl (Ext s pf) = Ext (Left s) pf
    inr :: Ext (S_2 |> P_2) -> Ext (Splus |> Pplus)
    inr (Ext s pf) = Ext (Right s) pf
  \end{code}
\end{minipage}
}
\caption{Container coproducts}
\label{fig:containercoproducts}
\end{figure}

%}

\subsection{Fixpoints and Folds}\label{mod:pred:containerfixandfold}

The universe of containers allows multiple generic
constructions. First of all, the fixpoint of a container is given by
its W-type.

< data W (c :: Cont) = Sup { unSup :: Ext c (W c) }

The definition of |Ext| is known at this point and Coq can see that
the |W c| is strictly positive for any container |c| and hence the
definition of |W| is accepted.

Furthermore, we define a fold operator generically.

< gfold :: Algebra (Ext c) a -> W c -> a
< gfold alg (Sup (Ext s pf)) =
<   alg (Ext s (\p -> gfold alg (pf p)))

We have obtained this definition by taking the usual definition 

< gfold alg x =
<   alg (gfmap (gfold alg) (unSup x))

which is essentially the same as the definition of |foldDTC| from Section
\ref{sec:mod:datatypesalacarte} and inlining the implementation of |gfmap|.
Because this exposes the structural recursion, Coq accepts the definition.
Indeed the recursive call |gfold alg (pf p)| is performed on the structurally
smaller argument |pf p|.
Note that, unlike for |foldDTC|,
inlining is possible because |gfmap| is defined uniformly for 
all containers.


\subsection{Induction}\label{mod:pred:containerinduction}
To define an induction principle for container types we proceed in the same way
as in Section \ref{sec:mod:modularinductivereasoning} by defining proof algebras
using an \emph{all-modality}~\cite{benke:universes}. The all-modality on
containers is given generically by a $\Pi$-type that asserts that |q| holds at
all positions.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}
  \begin{code}
    GAll :: (q :: a -> Prop) -> Ext c a -> Prop
    GAll q (Ext s pf) = forall ((p :: pos c s)). q (pf p)

    gind ::  forall ((c     :: Cont)) ->
             forall ((q     :: W c -> Prop)) ->
             forall ((palg  :: forall xs. GAll q xs -> q (Sup xs))) ->
             forall x. q x
    gind c q palg (Sup (Ext s pf)) =
      palg (\p -> gind c q palg (pf p))
    \end{code}
    \end{minipage}
  }
\caption{Container induction}
\label{fig:container induction}
\end{figure}

As with the implementation of the generic fold operations, enough
structure is exposed to write a valid induction function: |gind| calls
itself recursively on the structurally smaller values |pf p| to
establish the proofs of the recursive positions before applying the
proof algebra |palg|.


%-------------------------------------------------------------------------------
\subsection{Container Class}\label{mod:pred:containerautomation}

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

< class Container (f :: * -> *) where
<   cont    :: Cont
<   from    :: f a -> Ext c a
<   to      :: Ext c a -> f a
<   fromTo  :: forall x. from (to x) == x
<   toFrom  :: forall x. to (from x) == x

\end{minipage}
}
\caption{Container functor class}
\label{fig:containerfunctorclass}
\end{figure}

Directly working with the container representation is cumbersome for
the user. As a syntactic convenience we allow the user to use any
conventional functor of type |* -> *| as long as it is isomorphic
to a container functor. The type class |Container| in Figure
\ref{fig:containerfunctorclass} witnesses this isomorphism. The class
contains the functions |from| and |to| that perform the conversion
between a conventional functor and a container functor and proofs that
these conversions are inverses.

Via the isomorphisms |from| and |to| we can import all the generic
functions to concrete functors and give instances for |Functor|,
|PFunctor| and |SPF|.

< instance Container f => Functor f where
<   fmap f    = to . gfmap f . from
< instance Container f => PFunctor f where
<   All q     = GAll q . from
< instance Container f => SPF f where
<   Fix       = W S P
<   inFix     = sup . from
<   outFix    = to . unSup
<   fold alg  = gfold (alg . to)
<   ...

The important difference to the |SPF| class is that we can generically
build the instance for the coproduct of two |Container| functors

< instance (Container f, Container g) => Container (f :+: g)

\noindent by using the coproduct of their containers with the generic coproduct
construction from Section \ref{mod:pred:containercoproduct}.



%-------------------------------------------------------------------------------
\subsection{Extensible Inductive Relations}


\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

< class IFunctor i (f :: (i -> Prop) -> i -> Prop) where
<   ifmap :: forall ((a :: i -> Prop)) (b :: i -> Prop) (j :: i).
<              (forall j. a j -> b j) -> f a j -> f b j
<
< class  IFunctor i f =>
<          ISPF i (f :: (i -> Prop) -> i -> Prop) where
<   type IFix  :: i -> Prop
<   inIFix     :: forall ((j :: i)). f (IFix f i) -> IFix f i
<   outIFix    :: forall ((j :: i)). IFix f i -> f (IFix f i)
<   ifold      :: IAlgebra i f a -> forall j. IFix f j -> a j

\end{minipage}
}
\caption{Indexed strictly-positive functor class}
\label{fig:indexedstrictlypositivefunctor}
\end{figure}

Many properties are expressed as logical relations over
datatypes. These relations are represented by inductive families where
a constructor of the family corresponds to a rule defining the
relation.

When using logical relations over extensible datatypes the set of rules must be
extensible as well. For instance, a well-typing relation of values |WTValue ::
(Value, Type) -> Prop| must be extended with new rules when new cases are added
to |Value|.

Extensibility of inductive families is obtained in the same way as for inductive
datatypes by modularly building inductive families as fixpoints of functors
between inductive families. The following indexed functor |WTNatF| covers the
rule that a natural number value has a natural number type.

< data WTNatF (wfv :: (Fix vf, Fix tf) -> Prop) ::
<         (Value, Type) -> Prop where
<   WTNat :: (NatValueF :<: vf, NatTypeF :<: tf) =>
<            WTNat wfv (vi n, tnat)

MTC constructs fixed points of indexed functors also by means of
Church encodings. The indexed variants of algebras and fixed points
are

< type IAlgebra i (f :: (i -> Prop) -> i -> Prop) a =
<    forall ((j :: i)). f a j -> a j
< type IFixMTC i (f :: (i -> Prop) -> i -> Prop) j =
<    forall a. IAlgebra i f a -> a j

For type-soundness proofs we perform folds over proof-terms in order to
establish propositions on the indices and hence make use of the fold operation
provided by Church encodings. However, contrary to inductive datatypes we do not
make use of propositions on proof-terms and hence do not need an induction
principle for them. This also means that we do not need to keep track of the
universal property of folds for proof-terms.  Figure
\ref{fig:indexedstrictlypositivefunctor} defines the type class |ISPF| that
collects the necessary reasoning interface for modularly building logical
relations and indexed folds.

Since |Prop| is \emph{impredicative} in \Coq and induction-principles and
universal properties are of no concern here, MTC's approach to modular inductive
relations is sufficient for type-soundness proofs in \Coq and we can universally
instantiate |ISPF| with the definitions from MTC. However, other kinds of
meta-theoretic proofs may require induction principles for proof terms and the
approach is still limited to systems that support impredicativity.

Alternatively we can use a universe of indexed containers
\cite{indexedcontainers} that does not have the above restrictions. An
|i|-indexed container is essentially a container together with an assignment of
indices for each shape and each position of that shape.

More formally, an |i|-indexed container |S ||> P ||> R| is given by a family of
shapes |S :: i -> *| and family of position types |P :: (j :: i) -> S j -> *|
and an assignment |R :: (j :: i) -> (s :: S j) -> P j s -> i| of indices for
positions. Figure \ref{fig:indexedcontainers} gives the definition of the
extension and the fixed point of an indexed container. Similarly to containers,
one can generically define a fold operator for all indexed containers and
construct the coproduct of two indexed containers.


\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

< data ICont i where
<   (_ |> _ |> _) ::  (s :: i -> *) ->
<                     (p :: forall j. s j -> *) ->
<                     (r :: forall j s. p j s -> i) -> ICont i
<
< ishape  (s |> p |> r) = s
< ipos    (s |> p |> r) = p
< irec    (s |> p |> r) = r
<
< data  IExt (c :: ICont i)
<         (a :: i -> Prop) (j :: i) :: Prop where
<   IExt ::  (s   ::  ishape c j) ->
<            (pf  ::  forall ((p :: ipos c j s)). a (irec c j s p)) ->
<            IExt c a j
<
< data IW (c :: ICont i) (j :: i) :: Prop where
<   ISup :: IExt c IW j -> IW c j

\end{minipage}
}
\caption{i-indexed containers}

\label{fig:indexedcontainers}
\end{figure}

Fixed points and fold operators can be defined generically on that universe
similarly to Section \ref{ssec:contfixandfold}. Indexed containers are also
closed under coproducts and indexed algebras can be modularly composed using
type classes.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
