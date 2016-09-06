%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

In previous work~\cite{mtc} we have shown that it is possible to
modularize meta-theory along two dimensions: 1) language constructs and
2) operations and proofs. A significant limitation of that work is
that it only considered pure languages.

This work lifts that limitation and shows how to develop modular meta-theory for
languages with effects. Our solution uses monads and corresponding
algebraic laws for reasoning about different types of effects. The key
challenge that we have solved is how to formulate and prove a general
type-soundness theorem in a modular way that enables the reuse of feature
proofs across multiple languages with different sets of effects.  This turned
out to be non-trivial because existing formulations of type-soundness are very
sensitive to the particular effects used by the language.

As a secondary contribution, our work shows that algebraic laws about effects
scale up to realistic verification tasks such as meta-theoretic proofs. As far
as we know, it is their largest application to date. In this setting, the proof
assistant Coq has been invaluable. While the typically smaller examples in the
functional programming community can easily be dealt with by pen-and-paper
proofs, that approach would not have been manageable for the large family of
type-soundness proofs for mini-ML variants, as keeping track of large goals and
hypotheses by hand would be too painful and error-prone.

%%Ultimately we have shown new ways to develop meta-theory more
%%modularly using functional programming reasoning techniques

\steven{Point to Monad Zippers for modularly using two features that use
  the same underlying effect.}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
