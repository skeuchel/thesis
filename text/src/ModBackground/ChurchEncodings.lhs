%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt
%include exists.fmt

\section{Church Encodings}\label{sec:mod:churchencodings}

The Meta-Theory \`a la Carte (MTC) \cite{mtc} framework's solution to define type-level
fixed-points in a proof-assistant setting is to use Church encodings to encode
strictly-positive algebraic datatypes, or more precisely: B\"ohm-Berarducci
encodings \cite{bohm85automatic}.

\subsection{Encoding algebraic datatypes}

The untyped \textlambda-calclus only provides functions as primitives, but these can
be used to encode other datatypes. This technique was first used by
Alonzo Church and is hence named Church encoding. Church numerals are functions
representing the natural numbers. The idea is that the Church numeral $c_n$ for
the natural number $n$ applies a function $s$ $n$-times to a value $z$ similarly
to how we get $n$ by taking $n$-times the successor of zero. We can construct
the Church numeral for any concretely given natural number:
%{
%format c0
%format c1
%format c2
\begin{spec}
  c0 = \s._ \z._ z
  c1 = \s._ \z._ s z
  c2 = \s._ \z._ s (s z)
  ...
\end{spec}
%}



\subsection{Reasoning with Church Encodings}

%{
%format .         = "."

Church encodings have problems supporting proper induction principles,
like the induction principle for arithmetic expressions |indArith| in
Section \ref{ssec:modularinductivereasoning}. MTC uses a
\emph{poor-man's induction principle} |indArith2| instead.

< indArith2 ::
<   forall ((p   :: (Arith -> Prop)).
<   forall ((hl  :: (forall n. p (inMTC (LitF n)))).
<   forall ((ha  :: (forall x y. p x -> p y -> p (inMTC (AddF x y)))).
<   Algebra ArithF (exists a. p a)

The induction principle uses a dependent sum type to turn a proof
algebras into a regular algebra. The algebra builds a copy of the
original term and a proof that the property holds for the copy. The
proof for the copy can be obtained by folding with this algebra. In
order to draw conclusions about the original term two additional
\emph{well-formedness} conditions have to be proven.
%}
\begin{enumerate}

\item The proof-algebra has to be well-formed in the sense that it
really builds a copy of the original term instead of producing an
arbitrary term. This proof needs to be done only once for every
induction principle of every functor and is about 20 LoC per
feature. The use of this well-formedness proof is completely automated
using type-classes and hence hidden from the user.

\item The fold operator used to build the proof using the algebra
needs to be a proper fold operator, i.e. it needs to satisfy the
universal property of folds.

< foldMTC :: Algebra f a -> FixMTC f -> a
< foldMTC alg fa = fa alg
<
< type UniversalProperty (f :: * -> *) (e :: FixMTC f)
<   =  forall a (alg :: Algebra f a) (h :: FixMTC f -> a).
<        (forall e. h (inMTC e) = alg h e) ->
<          h e = foldMTC alg e

In an initial algebra representation of an inductive datatype, we have a single
implementation of a fold operator that can be proven correct. In MTC's approach
based on Church encodings however, each term consists of a separate fold
implementation that must satisfy the universal property.

\end{enumerate}

Hence, in order to enable reasoning MTC must provide a proof of the universal
property of folds for every value of a modular datatype that is used in a
proof. This is mostly done by packaging a term and the proof of the universal
property of its fold in a dependent sum type.

> type FixUP f = exists ((x :: FixMTC f)). UniversalProperty f x

The main novelty of MTC is its modular approach to inductive proofs. Regular
structural induction is not available for Church encodings, so MTC adapts the
proof methods used in the \emph{initial algebra semantics of data
  types}~\cite{goguen77initial,malcolm90thesis} -- in particular \emph{universal
  properties} -- to support modular inductive proofs over Church
encodings. Proofs are written in the same modular style as functions, using
proof algebras (class |PAlg| in Figure~\ref{fig:SalCa_Typeclasses}).  These
algebras are folded over the terms and can be modularly combined.  Unlike
function algebras, proof algebras are subject to an additional constraint which
ensures the validity of the proofs (|proj_eq|).

% For instance, the law
%|proj_eq| states that the new term produced by application of the
%algebra is equal to the original term.\BO{other constraints?}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
