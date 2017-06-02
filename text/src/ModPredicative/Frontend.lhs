%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

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

\subsection{Right-Neutrality of Addition}

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}

    \begin{code}
    data ZeroF a = ZeroF
      deriving Functor
    data ZeroAll (a :: *) (p :: a -> *) :: ZeroF a -> * where
        ZeroA :: ZeroAll a p ZeroF
    instance PFunctor ZeroF where
        type All ZeroF a = ZeroAll a
    \end{code}

    \hrule

    \begin{code}
    data SuccF a = SuccF a
      deriving Functor
    data SuccAll (a :: *) (p :: a -> *) :: SuccF a -> * where
        SuccA :: p n -> SuccAll a p (SuccF n)
    instance PFunctor SuccF where
        type All SuccF a = SuccAll a
    \end{code}
  \end{minipage}
}
\caption{Decomposition of naturals}
\label{fig:mod:natcases}
\end{figure}

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}
    \begin{code}
    data Nat = Zero | Succ Nat
    type NatF = ZeroF :+: SuccF

    instance SPF NatF where
        type Fix NatF = Nat
        inFix (Inl ZeroF)      = Zero
        inFix (Inr (SuccF n))  = Succ n
        outFix Zero     = Inl ZeroF
        outFix (Succ n) = Inr (SuccF n)
        --inoutinverse = Refl
        --outininverse = Refl
        fold alg Zero     = alg (Inl ZeroF)
        fold alg (Succ n) = alg (Inr (SuccF (fold alg n)))
        -- folduniqueness = ...
        -- foldcomputation = Refl
        -- ind = ...
    \end{code}
  \end{minipage}
}
\caption{|SPF| instance for natural numbers}
\label{fig:mod:natfix}
\end{figure}

In this Section we develop a complete example to showcase how the previous
definitions work. We will revisit the |plusZero| proof from Section
\ref{sec:mod:inductionintro} and modularize it, i.e. splitting the natural
numbers into the |Zero| and |Succ| cases. Figure \ref{fig:mod:natcases} shows
the signature functors |ZeroF| (top) and |SuccF| (bottom) for the two cases,
their all modalities and |PFunctor| instances.

To avoid giving away the generic definition of fixed-points, folds and induction
from Section \ref{sec:mod:containers}, we simply instantiate the |SPF| class
manually with the non-modular datatype definition of naturals. The datatype
and the |SPF| instance are show in Figure \ref{fig:mod:natfix}.

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}

  \begin{code}
  data Plus = Plus
  instance FAlgebra Plus ZeroF (Nat -> Nat) where
      falgebra Plus ZeroF n = n
  instance FAlgebra Plus SuccF (Nat -> Nat) where
      falgebra Plus (SuccF m) n = Succ (m n)

  plus :: (SPF f, FAlgebra Plus f) => Fix f -> Nat -> Nat
  plus = fold (falgebra Plus)
  \end{code}
  \end{minipage}
}
\caption{Modular addition function}
\label{fig:mod:natplus}
\end{figure}

Figure \ref{fig:mod:natplus} shows the modular definition of the |plus|
function. Each case has a separate function-valued |Plus| algebra instance and
the |plus| function itself is defined as a fold over the fixed-point of any
signature functor for which a |Plus| algebra exists, including the |NatF|
signature functor of natural numbers.

Similarly, Figure \ref{fig:mod:natpluszero} defines proof algebra instances for
each case separately. The final proof |plusZero| is again overloaded: we get the
property for the fixed-point of any signature functor with a |PlusZero| proof
algebra instance.

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}


  \begin{code}
  type PlusZero m = plus m Zero == m

  instance (ZeroF :<: f, SPF f) =>
      ProofAlgebra ZeroF (Fix f) inject PlusZero
    where
      palgebra ZeroA     = Refl
  instance (SuccF :<: f, SPF f) =>
      ProofAlgebra SuccF (Fix f) inject PlusZero
    where
      palgebra (SuccA q) = Cong Succ q

  plusZero :: (SPF f, ProofAlgebra SuccF (Fix f) inFix PlusZero) =>
      forall (m :: Fix f). PlusZero m
  plusZero = ind f PlusZero (palgebra f (Fix f) (falgebra Plus) PlusZero)
  \end{code}
  \end{minipage}
}
\caption{Modular |plusZero| proof}
\label{fig:mod:natpluszero}
\end{figure}





%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
