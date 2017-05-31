%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%-------------------------------------------------------------------------------
\section{Modular Frontend}\label{sec:modpred:frontend}

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
            ProofAlgebra (f :+: g) a (algebraPlus falg galg) p where
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
from the dictionary of the two sub-functors.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
