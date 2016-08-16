\section{Metatheory \`a la Carte}
The recent work on \emph{Meta-Theory \`a la Carte} (MTC) \cite{mtc} is the first
to improve this situation. It is a Coq framework for defining and reasoning
about extensible modular datatypes and extensible modular functions thereby
gaining modular component reuse. MTC builds on Datatypes \`a la Carte (DTC)
\cite{dtc}, a Haskell solution to the expression problem, to achieve
modularity. Besides writing modular algebras for expressing semantic functions
as folds, MTC also supports writing generally recursive functions using mixins
and bounded fixed points.  On top of that MTC presents techniques for modularly
composing proofs by induction for structurally recursive functions and
step-bounded induction for generally recursive functions.

The transition from the Haskell setting of DTC to a proof-assistant like Coq
comes with two major hurdles. DTC relies on a general fixed point combinator to
define fixed points for arbitrary functors and uses a generic fold operation
that is not structurally recursive. To keep logical consistency, Coq applies
conservative restrictions and rejects both: a) DTC's type level fixed-points
because it cannot see that the definition is always strictly-positive, and b)
DTC's fold operator because it cannot determine termination automatically.


MTC solves both problems by using extensible Church-encodings. However, MTC's
use of extensible Church-encodings is unsatisfactory and this solution leaves
much to be desired.

\begin{enumerate}
\item
  By using Church-encodings MTC is forced to rely on Coq's impredicative-set
  option, which is known to be inconsistent with some standard axioms of
  classical mathematics.
  %% This option is known to lead to logical inconsistency, and thus
  %% undermines all formal results obtained in MTC.

\item
  The fixpoint combinator provided by Church-encodings admits too many
  functors. For inductive reasoning, only strictly-positive functors are valid,
  i.e, those functors whose fixpoints are inductive datatypes. Yet,
  Church-encodings do not rule out other functors.  Hence, in order to reason
  only about inductive values, MTC requires a witness of inductivity: the
  universal property of folds. Since every value comes with its own
  implementation of the fold operator, MTC needs to keep track of a different
  such witness for every value. It does so by decorating the value with its
  witness.

  This decoration obviously impairs the readability of the code. Moreover, since
  proofs are opaque in Coq, it also causes problems for equality of terms.
  Finally, the decoration makes it unclear whether MTC adequately encodes
  fixpoints.

\item
  Church-encodings do not support proper induction principles. MTC relies on a
  \emph{poor-man's induction principle} instead and requires the user to provide
  additional well-formedness proofs.  Even though these can be automated with
  proof tactics, they nevertheless complicate the use of the framework.
\end{enumerate}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
