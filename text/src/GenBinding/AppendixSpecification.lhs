%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
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

\chapter{Needle \& Knot}\label{appendix:specification}

%format FreeStx = "{" Free  "}_{" Stx "}"
%format ReturnStx = "{" Return  "}_{" Stx "}"
%format StepStx = "{" Step  "}_{" Stx "}"
%format MonadStx = "{" Monad  "}_{" Stx "}"
%format FunctorStx = "{" Functor  "}_{" Stx "}"
%format fmapstx = "{" fmap  "}_{" Stx "}"
%format returnstx = "{" return  "}_{" Stx "}"
%format bindstx = "{" bind  "}_{" Stx "}"

\section{Free Monadic Well-Scoped Terms}\label{ssec:appendix:freemonad}

The datatype |FreeStx| in Figure \ref{fig:freemonad:freewellscoped} shows the
generic construction of free monadic well-scoped terms from a base functor.
Notice that the representation of variables is not fixed to be |Fin| but turned
into a parameter for uniformity with |FreeSet|.

One of the problems is how to represent morphisms between two families |v w ::
Nat -> *| when functorially mapping |f v d -> f w d|. In general, we cannot lift
a function of type |v d₁ → w d₂| to a function of type |v (S d₁) → w (S d₂)|. We
side-step this issue by abstracting away over the representation |m| of such
morphisms and require an interpretation function |forall d₁ d₂. m d₁ d₂ -> v d₁
-> w d₂| \cite{unidb}.

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

Simultaneous substitutions, i.e. mapping variables to terms, is generically
defined in Figure~\ref{fig:freemonad:genericsubst}.

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
  \caption{Generic Simultaneous Substitution}
  \label{fig:freemonad:genericsubst}
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
  \caption{Free Monad Instantiation}
  \label{fig:freemonad:lambda}
\end{figure}

\clearpage

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
