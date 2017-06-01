%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%-------------------------------------------------------------------------------
\section{Modular Frontend}\label{sec:modpred:frontend}

\begin{figure}[t]
\fbox{
  \begin{minipage}{\columnwidth}
    \begin{code}
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
    \end{code}
  \end{minipage}
}
\caption{Modular composition of proofs}
\label{fig:mod:proofalgebras}
\end{figure}

The modular composition of signatures and semantic functions in our approach,
based on co-products of functors, is the same as in DTC and MTC and carries over
largely unchanged to our declarative specification. Therefore we discuss only on
the composition of modular proofs in this section.

Figure \ref{fig:mod:proofalgebras} contains the instance of the |PFunctor| class
for a co-product |(f :+: g)|. For both, the associated type |All| and the
property |all_fmap| a simple case distinction is sufficient.

We use the type class |ProofAlgebra| to define and assemble proof algebras in
a modular fashion which is also show in Figure \ref{fig:mod:proofalgebras}.
The parameter |f| represents the underlying functor, |a| the
carrier type, |alg| the underlying |f|-algebra and |p| a property of the
carrier.

In the definition of the |ProofAlgebra| instance for functor composition we use
the the function |algebraPlus| from Figure \ref{fig:falgebraclass} in Section
\ref{sec:dtc:semanticfunctions} that composes the two function algebras |falg|
and |galg|. To compose two proof algebras for function algebras that come from
the type-class |FAlgebra| and are composed via the |FAlgebra| instance for
co-products we actually need to apply its dictionary creation function. In Coq
this is not a problem because |algebraPlus| is definitionaly equal to the
dictionary creation function, but this definition may potentially be
insufficient in other systems. To avoid any coherence concerns, we further
assume that algebras are always composed using the instance for function algebra
composition.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
