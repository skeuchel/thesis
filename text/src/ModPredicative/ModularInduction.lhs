%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%-------------------------------------------------------------------------------
\subsection{Inductive Reasoning Interface}
\label{sec:mod:modularinductivereasoning}

The |SPF| typeclass also provides an interface for inductive reasoning. The last
missing piece for reasoning is to have an induction principle available which is
itself defined using multiple concepts.

\paragraph{Proof Algebras}

%{
%format . = "."

Consider the induction principle |indArith| for arithmetic expression.

< indArith ::  forall (p   :: (Arith -> Prop)).
<              forall (hl  :: (forall n.                   p (inFix (Lit n)))).
<              forall (ha  :: (forall x y.  p x -> p y ->  p (inFix (Add x y)))).
<              forall x. p x

%}

It takes a proposition |p| as parameter and inductive steps |hl| and |ha| for
each case of the initial algebra. We say that |hl| and |ha| together form a
\emph{proof algebra} of |p|. An inductive step consists of showing |p| for an
application of the initial algebra given proofs of |p| for all recursive
positions. In case of a literal we have no recursive positions and in case of
addition we have two. Proof algebras for other datatypes differ in the number of
cases and the number of recursive positions.

\paragraph{All Modalities}
In the following we develop a uniform representation of proof algebras to allow
their modularization. We use an \emph{all modality}~\cite{benke:universes} for
functors to capture the proofs of recursive positions. Informally, the all
modality of a functor |f| and a predicate (|p :: a -> Prop|) is a new type (|All
a p :: f a -> Prop|) that denotes that the predicate |p| holds for each (|x ::
a|) in an (|f a|).

The following type |ArithAll| is an example of an all modality for arithmetic
expressions. The constructor |ALit| encodes that the all modality holds for
literals and |AAdd| encodes that the all modality holds for |(Add x y)| if |p|
holds for both recursive positions |x| and |y|.

< data ArithAll a p :: ArithF a -> Prop where
<   ALit  ::                ArithAll a p (Lit n)
<   AAdd  :: p x -> p y ->  ArithAll a p (Add x y)

We introduce a new typeclass |PFunctor| that carries the associated all modality
type and make |SPF| a subclass of it. Using the all modality definition we can
write |indArith| equivalently as

%format indArith' = ind "_{" A "}\prime"

%{
%format . = "."

< indArith' ::  forall p  :: (Arith -> Prop).
<               forall h  :: (forall xs. ArithAll p xs -> p (inFix xs)).
<               forall x. p x

%}

The proof algebra is now a single parameter |h|. Note that |h| shows that |p|
holds for an application of the initial algebra |inFix|. In the modular setting
however, we only want to provide proofs for sub-algebras of the initial algebra
that correspond to specific signatures and combine these \emph{proof
  sub-algebras} to a complete proof algebra for the initial algebra. To this
end, we define proof algebras in Figure \ref{fig:strictlypositivefunctor} more
generally over arbitrary algebras |alg|.

\paragraph{Induction Operator}
As a last member of |SPF| we introduce |ind| that is an induction principle for
the fixpoint type |Fix|. It takes a proof algebra of a property |p| for the
initial algebra and constructs a proof for every value of |Fix|.


%-------------------------------------------------------------------------------
\section{Composing Proofs}\label{ssec:modpred:proofs}

The modular composition of signatures and semantic functions in our approach,
based on co-products of functors, is the same as in DTC and MTC. We now turn
towards the modular composition of proofs. Composing two instances of the
|PFunctor| class is straightforward by inspecting the value of |xs| of the
coproduct (|(f :+: g) a|) of the two functors.

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}
    \begin{code}
      instance  (PFunctor f, PFunctor g) => PFunctor (f :+: g) where
        type All a p xs =  case xs of
                             Inl xs  -> All a p xs
                             Inr xs  -> All a p xs

      class ProofAlgebra f a alg p where
        palgebra :: PAlgebra f a alg p

      instance  (ProofAlgebra f a falg p, ProofAlgebra g a galg p) =>
            ProofAlgebra (f :+: a) a (algebraPlus falg galg) p where
        palgebra (Inl xs)  axs = palgebra xs axs
        palgebra (Inr xs)  axs = palgebra xs axs
    \end{code}
  \end{minipage}
}
\caption{Modular composition of proofs}
\label{fig:mod:proofalgebras}
\end{figure}

As for function algebras, we can use a type class |ProofAlgebra| to define and
assemble proof algebras in a modular fashion. The parameter |f| represents the
underlying functor, |a| the carrier type, |alg| the underlying |f|-algebra and
|p| a property of the carrier.

In the definition of the |ProofAlgebra| instance for functor composition we need
to have access to the function |algebraPlus| that composes the two function
algebras |falg| and |galg|. To avoid coherence concerns, we assume that algebras
are always composed using the instance for function algebra composition and that
|algebraPlus| is the function that builds the dictionary for the composition
from the dictionary of the two subfunctors.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
