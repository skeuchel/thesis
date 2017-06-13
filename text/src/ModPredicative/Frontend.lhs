%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%format a1
%format a2
%format p1
%format p2

%if False

> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE MultiParamTypeClasses #-}

> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeInType #-}
> {-# LANGUAGE TypeOperators #-}
>
>
> module Frontend where
>
>
> import Data.Kind
>
> data (:+:) (f :: * -> *) g a  =  Inl (f a) | Inr (g a)
>
> instance (Functor f, Functor g) => Functor (f :+: g) where
>     fmap f (Inl x) = Inl (fmap f x)
>     fmap f (Inr y) = Inr (fmap f y)
>
> type Algebra f a = f a -> a
>
> class FAlgebra name f a where
>   falgebra   :: name -> Algebra f a
>
> algebraPlus ::  Algebra f a -> Algebra g a -> Algebra (f :+: g) a
> algebraPlus f g (Inl a)  = f a
> algebraPlus f g (Inr a)  = g a
>
> instance  (FAlgebra name f a, FAlgebra name g a) =>
>             FAlgebra name (f :+: g) a where
>     falgebra name =  algebraPlus (falgebra name) (falgebra name)
>
> class Functor f => PFunctor f where
>     type All f  (a :: *) ::  (a -> *) -> f a -> *
>     -- all_fmap          ::  forall a b (g :: a -> b) (p :: b -> Prop) (xs :: f a).
>     --                           All f a p (fmap g xs) <-> All f a (\x -> p (g x)) xs
>
> type PAlgebra (f :: * -> *) (a :: *) (alg :: Algebra f a) (p :: a -> *) =
>    PFunctor f => forall (xs :: f a). All f a p xs -> p (alg xs)
>
> class Functor f => SPF (f :: * -> *) where
>   -- Fixed-points
>   type Fix f        ::  *
>   inFix             ::  f (Fix f) -> Fix f
>   outFix            ::  Fix f -> f (Fix f)
>   --in_out_inverse    ::  forall ((e :: Fix f)).      inFix (outFix e) = e
>   --out_in_inverse    ::  forall ((e :: f (Fix F))).  outFix (inFix e) = e
>
>   -- Folds
>   fold              ::  forall a. Algebra f a -> Fix f -> a
>   -- fold_uniqueness   ::  forall a (alg :: Algebra f a) h.
>   --                         (forall e. h (inFix e) = alg (fmap h e)) ->
>   --                         forall x. h x = fold alg x
>   -- fold_computation  ::  forall a (alg :: Algebra f a) (x :: a),
>   --                         fold alg (inFix x) = alg (fmap (fold alg) x)
>   --
>   -- -- Induction
>   --ind               ::  forall (p :: Fix f -> *). PAlgebra inFix p -> forall e. p e
>
> class PFunctor f => ProofAlgebra (f :: * -> *) (a :: *) (alg :: Algebra f a) (p :: a -> *) where
>     palgebra :: PAlgebra f a alg p
>
> data SumAll f g (a :: *) (p :: a -> *) :: (f :+: g) a -> * where
>     InlA :: All f a p x -> SumAll f g a p ('Inl x)
>     InrA :: All g a p y -> SumAll f g a p ('Inr y)
>
> instance (PFunctor f, PFunctor g) => PFunctor (f :+: g) where
>     type All (f :+: g) a = SumAll f g a

%endif


%-------------------------------------------------------------------------------
\section{Modularity Frontend}\label{sec:modpred:frontend}

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}
    \begin{spec}
      instance  (PFunctor f, PFunctor g) => PFunctor (f :+: g) where
          type All a p xs =  case xs of
                               Inl xs  -> All a p xs
                               Inr xs  -> All a p xs
          all_fmap = ...

      class PFunctor f =>
          ProofAlgebra f a (alg :: Algebra f a) (p :: a -> Prop)
        where
          palgebra :: PAlgebra f a alg p

      instance (ProofAlgebra f a falg p, ProofAlgebra g a galg p) =>
            ProofAlgebra (f :+: g) a (algebraPlus falg galg) p where
          palgebra (Inl xs)  axs = palgebra xs axs
          palgebra (Inr xs)  axs = palgebra xs axs
    \end{spec}
  \end{minipage}
}
\caption{Modular composition of proofs}
\label{fig:mod:proofalgebras}
\end{figure}

The modular composition of signatures and semantic functions in our approach,
based on co-products of functors, is the same as in DTC and MTC and carries over
largely unchanged to our declarative specification. Therefore we discuss only
the composition of modular proofs in this section.

Figure \ref{fig:mod:proofalgebras} contains the instance of the |PFunctor| class
for a co-product |(f :+: g)|. For both, the associated type |All| and the
property |all_fmap| a simple case distinction is sufficient.

We use the type class |ProofAlgebra|, also shown in Figure
\ref{fig:mod:proofalgebras}, to define and assemble proof algebras in a modular
fashion. The parameter |f| represents the underlying functor, |a| the carrier
type, |alg| the underlying |f|-algebra and |p| a property of the carrier.

In the definition of the |ProofAlgebra| instance for functor composition we use
the function |algebraPlus| from Figure \ref{fig:falgebraclass} in Section
\ref{sec:dtc:semanticfunctions} to composes the two function algebras |falg| and
|galg| which also forms the implementation of the |FAlgebra| instance for
co-products. To avoid any coherence concerns, we assume that algebras are always
composed using |algebraPlus| -- or equivalently the |FAlgebra| instance for
composition.

% To compose two proof algebras for function algebras that come from the
% type-class |FAlgebra| and are composed via the |FAlgebra| instance for
% co-products we actually need to apply its dictionary creation function. In Coq
% this is not a problem because |algebraPlus| is definitionally equal to the
% dictionary creation function, but this definition may potentially be
% insufficient in other systems.


\subsection{Non-Modularity of SPF}\label{mod:pred:spfnotmodular}
When instantiating modular functions to a specific set of signatures, we need an
|SPF| instance for the coproduct of that set. Ideally, as with algebras, we
would like to derive an instance for |f :+: g| given instances for |f| and |g|,
because we cannot expect the programmer to provide an instance for every
possible set of signatures.

Unfortunately, |SPF| does not include enough information about the functors to
do this in a constructive way. We cannot construct the fixed-point of the
coproduct |f :+: g| from the fixed-points of the summands |f| and |g| and
likewise for the fold and induction operators. Therefore |SPF| serves solely as
a high-level interface class.

In Section \ref{sec:mod:containers} we develop an approach that side-steps this
issue. Instead of composing fixed-points, folds and induction along coproducts of arbitrary |SPF|s,
we focus on the class of containers which are strictly-positive functors that
are 1) closed under coproducts and 2) allow a generic instantiation of |SPF|'s
interface.



\subsection{Example: Depth vs. Size}\label{mod:pred:bigproofexample}

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}

    \begin{code}
    data ArithF a = LitF Nat | AddF a a
      deriving Functor

    data ArithAll (a :: *) (p :: a -> *) :: ArithF a -> * where
      ALitF :: forall ((n :: Nat)). ArithAll a p (LitF n)
      AAddF :: forall ((a1 a2 :: a)). p a1 -> p a2 -> ArithAll a p (AddF a1 a2)

    instance PFunctor ArithF where
      type All ArithF a = ArithAll a
      all_fmap = ...
    \end{code}

    \hrule

    \begin{code}
    data LogicF a = BLitF Bool | IfF a a a
      deriving Functor

    data LogicAll (a :: *) (p :: a -> *) :: LogicF a -> * where
      ABLitF :: forall ((b :: Bool)). ArithAll a p (BLitF b)
      AIfF   :: forall ((i t e :: a)). p i -> p t -> p e -> ArithAll a p (IfF i t e)

    instance PFunctor LogicF where
      type All LogicF a = LogicAll a
      all_fmap = ...
    \end{code}
  \end{minipage}
}
\caption{Arithmetic and logical expressions}
\label{fig:mod:fullexample:signatures}
\end{figure}

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}
    \begin{code}
    type ExpF = ArithF :+: LogicF
    data Exp = Lit Nat | Add Exp Exp | BLit Bool | If Exp Exp Exp

    instance SPF ExpF where
        type Fix ExpF = Exp
        inFix (Inl (LitF n))      = Lit n
        inFix (Inl (AddF a1 a2))  = Add a1 a2
        inFix (Inr (BLitF b))     = BLit b
        inFix (Inr (IfF i t e))   = If i t e
        outFix (Lit n)      = Inl (LitF n)
        outFix (Add a1 a2)  = Inl (AddF a1 a2)
        outFix (BLit b)     = Inr (BLitF b)
        outFix (If i t e)   = Inr (IfF i t e)
        inoutinverse = ...
        outininverse = ...
        fold alg (Lit n)      = alg (Inl (LitF n))
        fold alg (Add a1 a2)  = alg (Inl (AddF (fold alg a1) (fold alg a2)))
        fold alg (BLit b)     = alg (Inr (BLitF b))
        fold alg (If i t e)   =
          alg (Inr (If (fold alg i) (fold alg t) (fold alg e)))
        folduniqueness  = ...
        foldcomputation = ...
        ind = ...
    \end{code}
  \end{minipage}
}
\caption{|SPF| instance for expressions}
\label{fig:mod:fullexample:spf}
\end{figure}

In this section we develop a complete example to showcase how the previous
definitions work. We reuse one of \cite{tapl} basic examples of structural
induction: Define a \emph{depth} and a \emph{size} function on expressions and
show that the depth is always smaller than the size. We compose expressions out
of two features that we define independently: arithmetic and logical
expressions.  Figure \ref{fig:mod:fullexample:signatures} shows the signature
functors |ArithF| (top) and |LogicF| (bottom) for the two features, their
all-modalities and |PFunctor| instances.

To avoid giving away the generic definition of fixed-points, folds and induction
from Section \ref{sec:mod:containers}, we simply instantiate the |SPF| class
manually with the non-modular datatype definition of expressions that contains
both arithmentic and logical expressions. The datatype
and the |SPF| instance are show in Figure \ref{fig:mod:fullexample:spf}.

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}

  \begin{code}
  data DepthOf = DepthOf
  depthOf :: (SPF f, FAlgebra DepthOf f Nat) => Fix f -> Nat
  depthOf = fold (falgebra DepthOf)

  instance FAlgebra DepthOf ArithF Nat where
    falgebra DepthOf (LitF n)      = 0
    falgebra DepthOf (AddF a1 a2)  = 1 + max a1 a2
  instance FAlgebra DepthOf LogicF Nat where
    falgebra DepthOf (BLitF n)     = 0
    falgebra DepthOf (IfF i t e)   = 1 + max i (max t e)
  \end{code}

  \hrule

  \begin{code}
  data SizeOf = SizeOf
  sizeOf :: (SPF f, FAlgebra SizeOf f Nat) => Fix f -> Nat
  sizeOf = fold (falgebra SizeOf)

  instance FAlgebra SizeOf ArithF Nat where
    falgebra SizeOf (LitF n)      = 1
    falgebra SizeOf (AddF a1 a2)  = 1 + a1 + a2
  instance FAlgebra SizeOf LogicF Nat where
    falgebra SizeOf (BLitF n)     = 0
    falgebra SizeOf (IfF i t e)   = 1 + i + t + e
  \end{code}

  \end{minipage}
}
\caption{Modular semantic functions}
\label{fig:mod:fullexample:semanticfunctions}
\end{figure}

Figure \ref{fig:mod:fullexample:semanticfunctions} shows the modular definition
of the two semantic functions |depthOf| and |sizeOf|.  Each feature/function
combination has a separate named |FAlgebra| instance and the semantic functions
themselves are defined as a fold over the fixed-point of any signature functor for
which an |FAlgebra| exists, including the combined |ExpF| signature functor of
arithmetic and logical expressions.

Similarly, Figure \ref{fig:mod:natpluszero} defines proof algebra instances of
|DepthSize| for each feature separately. We omit the proofs for brevity. The
final proof |depthSize| is again overloaded: we get the property for the
fixed-point of any signature functor with a |DepthSize| proof algebra instance.

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}

  \begin{code}
  type DepthSize e = depthOf e < sizeOf e
  depthSize :: (SPF f, FAlgebra DepthOf f Nat,
    FAlgebra SizeOf f Nat ProofAlgebra f (Fix f) inFix DepthSize) =>
    forall ((e :: Fix f)). DepthSize e
  depthSize = ind f DepthSize (palgebra f (Fix f) inFix DepthSize)

  instance (SPF f, ...) =>
      ProofAlgebra ArithF (Fix f) inject DepthSize
    where
      palgebra (ALitF n)            = ...
      palgebra (AAddF a1 a2 p1 p2)  = ...

  instance (SPF f, ...) =>
      ProofAlgebra LogicF (Fix f) inject DepthSize
    where
      palgebra (ABLitF b)           = ...
      palgebra (AIfF a1 a2 p1 p2)   = ...
  \end{code}
  \end{minipage}
}
\caption{Modular |DepthSize| proof}
\label{fig:mod:natpluszero}
\end{figure}





%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
