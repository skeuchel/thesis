%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

\section{Scientific Output}

This chapter is based on the contents of the article

\begin{center}
  \begin{minipage}{0.8\columnwidth}
    Delaware, B., Keuchel, S., Schrijvers, T., and Oliveira,
    B. C. d.~S. (2013).
    \newblock Modular Monadic Meta-Theory.
    \newblock In \emph{Proceedings of the 18th ACM SIGPLAN international
      conference on Functional programming}, ICFP '13, pages 319-330. ACM.
  \end{minipage}
\end{center}

\noindent The project also drew ideas from previous unpublished work of mine
(see \cite{keuchel2012modular}):

\begin{center}
  \begin{minipage}{0.8\columnwidth}
    Keuchel, S. and Schrijvers, T. (2012).
    \newblock Modular Monadic Reasoning, a (Co-)Routine.
    \newblock Presented at \emph{the 24th Symposium on Implementation and
      Application of Functional Languages}, IFL '12.
  \end{minipage}
\end{center}

In particular, the modeling of explicit continuations in the monadic typing
rules of the \Name~framework is reminiscent of a free monad or a
co-routine/resumption monad which is the basis for this previous work. The
co-routine based approach used an inductive datatype to encode computations
which turned out to be cumbersome with respect to equality and algebraic
reasoning. \Name~uses monadic values directly instead. Nevertheless, the
fundamental setup of the use of explicit continuations in the monadic typing
rules is directly influenced by my prior work. However, Benjamin Delaware took
the lead in this project and has contributed the major part of the development
and refinement of the monadic typing rules.

The reusable bind lemma was developed by me during the work on the case study
and was used to significantly cut down the number of feature interaction lemmas.

Concerning the technical development in \Coq, the \Name~monad library --
including most of the algebraic laws -- was written before I joined the project.
My main contribution lies in the development of feature theorems, language
compositions and the presentation of the case study in the publication.


% In previous work~\cite{mtc} we have shown that it is possible to
% modularize meta-theory along two dimensions: 1) language constructs and
% 2) operations and proofs. A significant limitation of that work is
% that it only considered pure languages.

% This work lifts that limitation and shows how to develop modular meta-theory for
% languages with effects. Our solution uses monads and corresponding
% algebraic laws for reasoning about different types of effects. The key
% challenge that we have solved is how to formulate and prove a general
% type-soundness theorem in a modular way that enables the reuse of feature
% proofs across multiple languages with different sets of effects.  This turned
% out to be non-trivial because existing formulations of type-soundness are very
% sensitive to the particular effects used by the language.

% As a secondary contribution, our work shows that algebraic laws about effects
% scale up to realistic verification tasks such as meta-theoretic proofs. As far
% as we know, it is their largest application to date. In this setting, the proof
% assistant Coq has been invaluable. While the typically smaller examples in the
% functional programming community can easily be dealt with by pen-and-paper
% proofs, that approach would not have been manageable for the large family of
% type-soundness proofs for mini-ML variants, as keeping track of large goals and
% hypotheses by hand would be too painful and error-prone.

%%Ultimately we have shown new ways to develop meta-theory more
%%modularly using functional programming reasoning techniques

% \steven{Point to Monad Zippers for modularly using two features that use
%   the same underlying effect.}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
