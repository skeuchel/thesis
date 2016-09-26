%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt


This paper targets type-safety proofs of typed programming languages in
particular and uses the syntactic approach to programming language metatheory,
invented by Wright and Felleisen \cite{progresspreservation} and popularized by
Pierce \cite{tapl}. An important issue that arises in such formalizations is the
treatment of variable binding which typically comprises the better part of the
formalization. Most of this variable binding infrastructure is repetitive and
tedious boilerplate. By boilerplate we mean mechanical operations and lemmas
that appear in many languages, such as: 1) common operations like calculating
the sets of free variables or the domain of a typing context, appending contexts
and substitutions; 2) lemmas about operations like commutation of substitutions
or the interaction between the free-variable calculation and substitution; and
3) lemmas about semantic relations such as the preservation of well-scoping and
typing under operations.

To alleviate researchers from this burden, multiple approaches have been
developed to capture the structure of variable binding and generically take care
of the associated boilerplate. These include specification languages of syntax
with binding and scoping rules \cite{ottjfp}, tools or reflection libraries that
generate code for proof assistants from specifications
\cite{lngen,dbgen,autosubst}, generic programming libraries that implement
boilerplate using datatype generic functions and proofs \cite{gmeta} and
meta-languages that have built-in support for syntax with binding
\cite{twelf,beluga,nominal2}.

Yet, despite the multitude of existing approaches, the scope of the available
support is still limited to only the term-related boilerplate 1) and 2). Those
that do cover boilerplate of semantic relations 3) typically only provide
reusable tactics but still leave stating the lemmas and composing all the
necessary ingredients up to the developer.

This work targets boilerplate of semantic relations 3). For this purpose, we
extend \Knot\cite{knotneedle}, a specification language for abstract syntax
programming language that covers binding, with support for a rich class of
relational specifications. We identify \emph{context parametricity} as an
essential property of rules that allow arbitrary contextual changes to be
reflected locally. In particular, relations for which the variable rule is the
only non-parametric rule have the structure of a \emph{free relative monad}
\cite{monadsnotendo,relativemonads,monadic}. For these the monadic bind, which
corresponds to the substitution lemma, can be derived fully generically. We also
extend \Knot's code generator \Needle to generate definitions of relations and
boilerplate lemmas automatically and thereby greatly simplify the treatment of
semantic relations in the mechanization of programming languages. Our specific
contributions are:
%
\begin{enumerate}

\item
  We extend \Knot with natural and concise specifications of semantic relations.
  They are highly expressive, supporting mutually recursive relations and
  relations with telescopic outputs to model the semantics of multi-binders such
  as patterns

\item
  We present a type system for relational specifications that keeps track of the
  scope of meta-variables to ensure that the expressions that are used in the
  specification of relations are well-scoped. Expressions may cross binders and
  be used in a different scope, but this has to be done explicitly to avoid
  capture.

  Well-scopedness is usually left unchecked in other first-order
  approaches. Hence, \Knot provides an additional guarantee for the correctness
  of specifications.

\item
  We extend \Needle, a \Coq code generator for \Knot specifications, to produce
  inductive definition of relations, boilerplate well-scopedness, weakening and
  substitutiton lemmas for relations and corresponding syntax-directed proof
  terms. The substitution lemma is not derivable for all possible
  specifications, in which case \Needle leaves minimal proof obligations for the
  human mechanizer.

\item
  For a simplified variant of relational specification supporting only
  single-variable binding, we generically prove the correctness of key
  elaboration functions for the boilerplate lemmas.

\item
  We show that the support for relational specifications yields on average 34\%
  savings in code-size over an already assisted approach in a case-study of
  type-safety mechanizations for 10 languages. Among these is a \Knot solution
  of the \POPLmark challenge (1a + 2a) that we compare to 7 other
  solutions. Ours is by far the smallest.
\end{enumerate}

The code for \Needle and the Coq developments (compatible with Coq 8.4 and
8.5) can be found in the supplementary material.
%% are available at \url{https://users.ugent.be/~skeuchel/knot}.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
