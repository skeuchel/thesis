%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

\section{Constructions \`{a} la Carte}
\label{sec:semanticfunctions}

%if False

> {-# LANGUAGE TypeFamilies, ScopedTypeVariables, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
>
> import Control.Arrow
>
> type Algebra f a = f a -> a
> data FixDTC f = InDTC { outDTC :: f (FixDTC f) }
>
> data ArithF  e = Lit  Int   | Add e e
> data BoolF   e = BLit Bool  | If e e e
>
> infixr 7 :+:
> data (:+:) f g a = Inl (f a) | Inr (g a)

%endif

This section reviews the core ideas behind DTC and MTC and presents
the infrastructure for writing modular functions over modular
datatypes. In the next section we discuss our adapted approach that
works in the restricted Coq setting.

\subsection{Fixed points}
In DTC extensible datatypes are represented as fixed
points of signature functors.

> data FixDTC f = InDTC { outDTC :: f (FixDTC f) }

For example the functors |ArithF| and |BoolF| are signatures for
arithmetic and boolean expressions.

> data ArithF  e = Lit  Int   | Add e e
> data BoolF   e = BLit Bool  | If e e e

For example |ArithDTC| is a type that features only arithmetic expressions.

> type ArithDTC = FixDTC ArithF

Different features can be combined modularly by taking the coproduct
of the signatures before taking the fixed point.

> data (:+:) f g a = Inl (f a) | Inr (g a)
> type ExpDTC = FixDTC (ArithF :+: BoolF)

\subsection{Automated injections}

Combining signatures makes writing expressions difficult. For example
the arithmetic expression |3 + 4| is represented as the term

> ex1 :: FixDTC (ArithF :+: BoolF)
> ex1 = InDTC (Inl   (Add
>                       (InDTC (Inl (Lit 3)))
>                       (InDTC (Inl (Lit 4)))))

Writing such expressions manually is too cumbersome and
unreadable. Moreover, if we extend the datatype with a new signature
other injections are needed.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

%if False

> class f :<: g where
>   inj :: f a -> g a
>   prj :: g a -> Maybe (f a)
> inject :: (f :<: g) => f (FixDTC g) -> FixDTC g
> inject x = InDTC $ inj x
> project :: (f :<: g) => FixDTC g -> Maybe (f (FixDTC g))
> project x = prj $ outDTC x

%endif

< class f :<: g where
<   inj      :: f a -> g a
<   prj      :: g a -> Maybe (f a)
<   inj_prj  :: forall a (ga :: g a) (fa :: f a).
<     prj ga = Just fa -> ga = inj fa
<   prj_inj  :: forall a (fa :: f a).
<     prj (inj fa) = Just fa
<
< inject :: (f :<: g) => f (FixDTC g) -> FixDTC g
< inject x = FixDTC $ inj x
< project :: (f :<: g) => FixDTC g -> Maybe (f (FixDTC g))
< project x = prj $ unFix x

\end{minipage}
}
\caption{Sub-functor relation}

\label{fig:subfunctorrelation}
\end{figure}

To facilitate writing expressions and make reuse possible we use the
sub-functor |f :<: g| relation shown in Figure
\ref{fig:subfunctorrelation}. The member function |inj| injects the
sub-functor |f| into the super-functor |g|. In our case we need
injections of functors into coproducts which are automated using type
class machinery. \footnote{Coq's type-class mechanism performs
backtracking. These instances do not properly work in Haskell. See
\cite{dtc} for a partial solution.}

< instance (f :<: f) where
<   inj = id
< instance (f :<: g) => (f :<: (g :+:h)) where
<   inj = Inl
< instance (f :<: h) => (f :<: (g :+:h)) where
<   inj = Inr

The |inject| function is a variation of |inj| that additionally
applies the constructor of the fixpoint type. Using the sub-functor
relation we can define smart constructors for arithmetic expressions

> lit :: (ArithF :<: f) => Int -> FixDTC f
> lit i = inject (Lit i)
> add :: (ArithF :<: f) => FixDTC f -> FixDTC f -> FixDTC f
> add a b = inject (Add a b)

that construct terms of any abstract super-functor |f| of
|ArithF|. This is essential for modularity and reuse. We can define
terms using the smart-constructors, but constructing a value of a
specific fixpoint datatype is delayed. With these smart constructors
the above example term becomes

> ex1' :: (ArithF :<: f) => FixDTC f
> ex1' = lit 3 `add` lit 4


The |prj| member function is a partial inverse of |inj|. With it we
can test if a specific sub-functor was used to build the top layer of
a value. This operation fails if another sub-functor was used. The
type class also includes proofs that witness the partial
inversion. The |project| function is a variation of |prj| that strips
the constructor of the fixpoint type. Similarly to injections, we can
automate projections for coproducts by adding corresponding
definitions to the instances above.


\subsection{Semantic functions}

In this section we define evaluation for arithmetic and boolean
expressions modularly. We use another modular datatype to represent
values. Its signatures and smart-constructors are given in Figure
\ref{fig:modularvalues}. The signature |StuckValueF| represents a
sentinel value to signal type errors during evaluation.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

> data NatValueF    v = VInt   Int
> data BoolValueF   v = VBool  Bool
> data StuckValueF  v = VStuck

> vint :: (NatValueF :<: vf) => Int -> FixDTC vf
> vint i = inject (VInt i)
> vbool :: (BoolValueF :<: vf) => Bool -> FixDTC vf
> vbool b = inject (VBool b)
> vstuck :: (StuckValueF :<: vf) => FixDTC vf
> vstuck = inject VStuck

\end{minipage}
}
\caption{Modular value datatype}

\label{fig:modularvalues}
\end{figure}

If |f| is a functor, we can fold over any value of type |FixDTC f| as
follows:

> type Algebra f a = f a -> a
> foldDTC :: Functor f => Algebra f a -> FixDTC f -> a
> foldDTC f (InDTC x) = f (fmap (foldDTC f) x)

An algebra specifies one step of recursion that turns a value of type
f a into the desired result type a. The fold uniformly applies this
operation to an entire term. All semantic functions over a modular
datatype are written as folds of an algebra.

Using type classes, we can define and assemble algebras in a modular
fashion. The class |FAlgebra| in Figure \ref{fig:falgebraclass}
carries an algebra for a functor |f| and carrier type |a|. It is
additionally indexed over a parameter |name| to allow definitions of
distinct functions with the same carrier. For instance, functions for
calculating the size and the height of a term can both be defined
using |Int| as the carrier.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

> class FAlgebra name f a where
>   f_algebra   :: name -> Algebra f a

> algebraPlus ::  Algebra f a -> Algebra g a ->
>                   Algebra (f :+: g) a
> algebraPlus f g (Inl a)  = f a
> algebraPlus f g (Inr a)  = g a

> instance  (FAlgebra name f a, FAlgebra name g a) =>
>             FAlgebra name (f :+: g) a where
>   f_algebra name =  algebraPlus
>                       (f_algebra name)
>                       (f_algebra name)

\end{minipage}
}
\caption{Function algebra infrastructure}

\label{fig:falgebraclass}
\end{figure}

We use the name |Eval| to refer to the evaluation algebra.

> data Eval = Eval

The evaluation algebras are parameterized over an abstract
super-functor |vf| for values. In case of |ArithF| we require that
integral values are part of |vf| and for |BoolF| we require that
boolean values are part of |vf|.

In the case of an |Add| in the evaluation algebra for arithmetic
expressions we need to project the results of the recursive calls to
test whether integral values were produced. Otherwise a type error
occurrs and the |stuck| value is returned.

> instance  (NatValueF :<: vf, StuckValueF :<: vf) =>
>             FAlgebra Eval ArithF (FixDTC vf) where
>   f_algebra Eval (Lit i)     =  vint i
>   f_algebra Eval (Add a b)   =
>     case (project a, project b) of
>       (Just (VInt a) , Just (VInt b))  -> vint (a + b)
>       _                                -> vstuck

Similarly, we have to test the result of the recursive call of the
condition of an |If| term for boolean values.

> instance  (BoolValueF :<: vf, StuckValueF :<: vf) =>
>             FAlgebra Eval BoolF (FixDTC vf) where
>   f_algebra Eval (BLit b)    =  vbool b
>   f_algebra Eval (If c t e)  =
>     case project c of
>       Just (VBool b) -> if b then t else e

Function algebras for different signatures can be combined together to
get an algebra for their coproduct. The necessary instance declaration
is also given in Figure \ref{fig:falgebraclass}. Finally, we can
define an evaluation function for terms given an |FAlgebra| instance
for |Eval|.

> eval ::  (Functor f, FAlgebra Eval f (FixDTC vf)) =>
>            FixDTC f -> FixDTC vf
> eval = foldDTC (f_algebra Eval)


\section{Reasoning \`{a} la Carte}
\label{sec:reasoning}

In Section \ref{sec:semanticfunctions} we focused on programming in
Haskell. In this Section we turn our attention towards performing
modular constructions of datatypes, functions and inductive proofs
in a proof-assistant like Coq.

\subsection{Modular Definitions in Coq}

%{
%format tau = "\tau"
%format .   = "."
%format ×   = "\times"
%format mu  = "\mu"
%format muX  = "\mu{X}"

Unfortunately, we cannot directly translate the definitions of Section
\ref{sec:semanticfunctions}. Coq requires all inductive definitions to
be \emph{strictly-positive}. We define \emph{strictly positive types}
(SPT) by using the following generative grammar~\cite{containers}:

< tau ::= X | 0 | 1 | tau + tau | tau × tau | K -> tau | muX . tau

where |X| ranges over type variables and |K| ranges over constant
types,~i.e. an SPT with no free type variables. The constants |0| and
|1| represent the empty and unit types, the operators |+|, |×|, |->|
and |mu| represent coproduct, cartesian product, exponentiation
and least fixed point construction.
%}
\steven{Look at definitions of strictly-positive functors in the
literature and include a definition here. Are there declarative
specifications of strictly-positive functors available or are all
definitions constructive?}

For |FixDTC f| to be strictly positive this means that the argument
functor |f| has to be strictly-positive, i.e. it corresponds to a term
built with the above grammar with one free type variable.


%{
%format :-> = "\mapsto"

As a counter example, inlining the non-strictly positive functor |X
:-> (X -> Int) -> Int| into |FixDTC| yields the invalid datatype
definition

> data NSP = NSP ((NSP -> Int) -> Int)

It does not satisfy the positivity requirements and is rejected by
Coq. While Coq can automatically determine the positivity for any
concrete functor by inspecting its definition, it cannot do so for an
abstract functor like the one that appears in the definition of
|FixDTC|. Hence, Coq also rejects |FixDTC|.
%}

Of course, we have no intention of using non-strictly positive
functors for our application and would like to provide the evidence of
strict-positivity to the fixpoint type
constructor. Mini-Agda~\cite{miniagda} for example allows programmers
to annotate strictly-positive and negative positions of type
constructors. Unfortunately, Coq does not provide us with this
possibility and a different approach is needed. To this end, we define
the |SPF| type class in Figure \ref{fig:strictlypositivefunctor} which
serves as a declarative specification of our requirements on functors
and which carries the required evidence.

While we need the existence of a fixed point type of abstract
super-functors, it is inessential how it is constructed. This means
that instead of providing a generic fixpoint type constructor like
|FixDTC| we can alternatively provide a witness of the existence of a
valid fixpoint in the type class, i.e. we make the fixpoint an
associated type of the |SPF| type class.  We thereby delay the problem
of defining it to the specific functors. |SPF| also includes the
functions |inFix| and |outFix| as members that fold/unfold one layer
of the fixpoint.

The fold operator from Section \ref{sec:semanticfunctions} also causes
problems in Coq. |SPF| is a sub-class of |Functor| so we would like to
define a generic fold operator similar to |foldDTC|.

%if False

> class Functor f => SPF f where
>   type Fix
>   inFix  :: f Fix -> Fix
>   outFix :: Fix -> f Fix

%endif

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


\subsection{Modular inductive reasoning}
\label{ssec:modularinductivereasoning}

The |SPF| typeclass also provides an interface for reasoning. It
includes proof terms that witness that folding/unfolding of the
fixpoint type form inverse operations and that the provided fold
operators satisfies the universal property of folds. The last missing
piece for reasoning is to have an induction principle available.

%{
%format . = "."

Consider the induction principle |indArith| for arithmetic expression.

< indArith ::  forall (p   :: (Arith -> Prop)).
<              forall (hl  :: (forall n.                   p (inFix (Lit n)))).
<              forall (ha  :: (forall x y.  p x -> p y ->  p (inFix (Add x y)))).
<              forall x. p x

%}

It takes a proposition |p| as parameter and inductive steps |hl| and
|ha| for each case of the initial algebra. We say that |hl| and |ha|
together form a \emph{proof algebra} of |p|. An inductive step
consists of showing |p| for an application of the initial algebra
given proofs of |p| for all recursive positions. In case of a literal
we have no recursive positions and in case of addition we have two.
Proof algebras for other datatypes differ in the number of cases and
the number of recursive positions.

In the following we develop a uniform representation of proof algebras
to allow their modularization. We use an \emph{all
modality}~\cite{benke:universes} for functors to capture the proofs of
recursive positions. Informally, the all modality of a functor |f| and
a predicate |p :: a -> Prop| is a new type |All a p :: f a -> Prop|
that says that the predicate |p| holds for each |x :: a| in an |f
a|. The following type |ArithAll| is an example of an all modality for
arithmetic expressions.

< data ArithAll a p :: ArithF a -> Prop where
<   ALit  ::                ArithAll a p (Lit n)
<   AAdd  :: p x -> p y ->  ArithAll a p (Add x y)

We introduce a new typeclass |PFunctor| that carries the associated
all modality type and make |SPF| a subclass of it. Using the all
modality definition we can write |indArith| equivalently as

%format indArith' = ind "_{" A "}\prime"

%{
%format . = "."

< indArith' ::  forall p  :: (Arith -> Prop).
<               forall h  :: (forall xs. ArithAll p xs -> p (inFix xs)).
<               forall x. p x

%}

The proof algebra is now a single parameter |h|. Note that |h| shows
that |p| holds for an application of the initial algebra |inFix|. In
the modular setting however, we only want to provide proofs for
sub-algebras of the initial algebra that correspond to specific
signatures and combine these \emph{proof sub-algebras} to a complete
proof algebra for the initial algebra. To this end, we define proof
algebras in Figure \ref{fig:strictlypositivefunctor} more generally
over arbitrary algebras. As a last member of |SPF| we introduce |ind|
that is an induction principle for the fixpoint type |Fix|. It takes a
proof algebra of a property |p| for the initial algebra and constructs
a proof for every value of |Fix|.


\subsection{Composing features}

In Section \ref{sec:semanticfunctions} we have shown how to modularly
compose signatures and semantic functions. These definitions carry
over to Coq without any problems. We now turn to modularly composing
proofs.

The |PFunctor| class also has the nice property of being closed under
coproducts.

< instance  (PFunctor f, PFunctor g) =>
<             PFunctor (f :+: g) where
<   type All a p xs =  case xs of
<                        Inl xs  -> All a p xs
<                        Inr xs  -> All a p xs

As for function algebras, we can use a type class to define and
assemble proof algebras in a modular fashion.

< class ProofAlgebra f a alg p where
<   palgebra :: PAlgebra f a alg p
<
< instance  (ProofAlgebra f a falg p,
<            ProofAlgebra g a galg p) =>
<     ProofAlgebra (f :+: a) a
<       (algebraPlus falg galg) p where
<    palgebra (Inl xs)  axs = palgebra xs axs
<    palgebra (Inr xs)  axs = palgebra xs axs

When instantiating modular functions to a specific set of signatures,
we need an |SPF| instance for the coproduct of that set. As with
algebras we would like to derive an instance for |f :+: g| given
instances for |f| and |g| as we cannot expect the programmer to
provide an instance for every possible set of
signatures. Unfortunately, |SPF| does not include enough information
about the functors to do this in a constructive way. What we need is a
refinement of |SPF| that allows us to perform this construction.

