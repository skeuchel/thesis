%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt
%include exists.fmt

%format c0
%format c1
%format c2
%format c_n = "{{" c "}_{" n "}}"

%if False

> {-# LANGUAGE ExplicitForAll #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ImpredicativeTypes #-}
> {-# LANGUAGE TypeApplications #-}
>
> module ChurchEncodings where
>
> import DatatypesALaCarte

%endif



%-------------------------------------------------------------------------------
\section{Church Encodings}\label{sec:mod:churchencodings}

The Meta-Theory \`a la Carte (MTC) \cite{mtc} framework's solution to define
type-level fixed-points in a proof-assistant setting is to use Church
encodings, or B\"ohm-Berarducci encodings to be precise
\cite{bohm85automatic}, to encode strictly-positive algebraic datatypes.


%-------------------------------------------------------------------------------
\subsection{Encoding Algebraic Datatypes}

\begin{figure}[t]
\fbox{
  \begin{minipage}{0.98\columnwidth}

< type FixC f = forall a. Algebra f a -> a
<
< foldC :: Algebra f a -> FixC f -> a
< foldC alg x = x alg
<
< inC :: forall f. Functor f => f (FixC f) -> FixC f
< inC x = \alg -> alg (fmap (foldC alg) x)
<
< outC :: forall f. Functor f => FixC f -> f (FixC f)
< outC = foldC (fmap inC)

  \hrule

< inject :: (Functor g, f :<: g) => f (FixC g) -> FixC g
< inject x = inC (inj x)
< project :: (Functor g, f :<: g) => FixC g -> Maybe (f (FixC g))
< project x = prj (outC x)

  \end{minipage}
}
\caption{Fixed-points and fold using Church encodings}
\label{fig:mod:fixchurch}
\end{figure}

The untyped \textlambda-calclus only provides functions as primitives. Yet, this is
no limitation as they can
be used to encode other datatypes. This technique was first used by
Alonzo Church and is hence named Church encoding. For instance, the Church encoding
of natural numbers is known as Church numerals. The idea is that the Church numeral $c_n$ for
the natural number $n$ applies a function $s$ $n$-times to a value $z$ similarly
to how we get $n$ by taking $n$-times the successor of zero. We can construct
the Church numeral for any concretely given natural number:
\begin{spec}
  c0 = \s._ \z._ z
  c1 = \s._ \z._ s z
  c2 = \s._ \z._ s (s z)
  ...
\end{spec}

In other words, the $n$-th Church numeral corresponds to
the fold over natural numbers instantiated for the number $n$. In fact, typing the above combinators in Haskell
yields the familiar type |c_n :: forall a. (a -> a) -> a -> a|. B\"ohm and
Berarducci \cite{bohm85automatic} proved that such an encoding is not limited to
simple datatypes like the naturals, but that all strictly-positive (and
parameterized) datatypes can be encoded in System~F in this fashion and proved
that the encoding is an isomorphism.

Specializing the type of DTC's generic fold operator from Section
\ref{sec:mod:datatypesalacarte}

< foldDTC :: Functor f => Algebra f a -> FixDTC f -> a

for a particular datatype |FixDTC f|
yields the type |Algebra f a -> a| that we use in Figure \ref{fig:mod:fixchurch} to define the
type-level fixed-point combinator |FixC| for the Church encoding of that datatype. The
generic fold operator |foldC| for this fixed-point is simply the application of
a value to the given algebra. We can also define one-level folding |inC| and
unfolding |outC| of the fixed-point which are also given in Figure
\ref{fig:mod:fixchurch}. These can in turn be used to define new |inject| and
|project| functions for the definition of smart constructors and feature
specific algebras. DTC's machinery for taking the coproduct of functors and
algebras carries over to the new fixed-point unchanged. User-defined algebras
for semantic functions only need to be altered to use the new smart
constructors.


%-------------------------------------------------------------------------------

\subsection{Reasoning with Church Encodings}

%{
%format .         = "."

The Church encoding of strictly-positive types carries over to (and can be
extended in) the Calculus of Constructions (CoC)
\cite{pfenning90inductively}. However, proper structural induction principles
for Church encodings are not provable in CoC \cite{pfenning90inductively}. Such
induction principles have to be assumed as axioms instead. MTC side-steps this
issue and uses a weaker form of induction for which it adapts the proof methods
used in the \emph{initial algebra semantics of data
  types}~\cite{goguen77initial,malcolm90thesis} -- in particular \emph{universal
  properties} -- to support inductive proofs over Church encodings.  Consider
the type signature of the function |indNat2| that represents an alternative
induction principles for the natural numbers:

\begin{spec}
indNat2 ::
  forall (P :: Nat -> Prop).
    (pzero :: P Zero) ->
    (psucc :: forall (m :: Nat). P m -> P (Succ m)) ->
    Algebra NatF (exists m. P m)
\end{spec}

The induction principle uses a dependent sum type to turn a proof algebra,
consisting of the functions |pzero| and |psucc|, into a regular algebra. The
algebra builds a copy of the original value and a proof that the property holds
for the copy. The proof for the copy can be obtained by folding with this
algebra. In order to draw conclusions about the original value two additional
\emph{well-formedness} conditions have to be proven.
%}
\begin{enumerate}

\item The proof-algebra has to be well-formed in the sense that it really builds
  a copy of the original value instead of producing an arbitrary value of the
  same type. This proof needs to be done only once for every induction principle
  of every functor and is usually short and straightforward.

  In the MTC framework, the well-formedness proof is about 20 LoC per feature
  and its use is completely automated using type-classes and hence hidden from
  the user.

\item The fold operator used to build the proof using the algebra needs to be a
  proper fold operator, i.e. it needs to satisfy the universal property of
  folds.

< type UniversalProperty (f :: * -> *) (e :: FixC f)
<   =  forall a (alg :: Algebra f a) (h :: FixC f -> a).
<        (forall e. h (inC e) = alg h e) ->
<          h e = foldC alg e

In an initial algebra representation of an inductive datatype, we have a single
implementation of a fold operator that can be proven correct. In MTC's approach
based on Church encodings however, each value consists of a separate fold
implementation that must satisfy the universal property.

\end{enumerate}

Hence, in order to enable reasoning MTC must provide a proof of the universal
property of folds for every value of a modular datatype that is used in a
proof. This is mostly done by packaging a term and the proof of the universal
property of its fold in a dependent sum type.

\begin{spec}
type FixUP f = exists ((x :: FixC f)). UniversalProperty f x
\end{spec}

One of the main novelties of MTC is that this approach to induction also gives
us modularity: Proofs are written in the same modular style as functions.
% using proof algebras (class |PAlg| in Figure~\ref{fig:SalCa_Typeclasses}).
These algebras are folded over the terms and can be modularly combined.

% Unlike
% function algebras, proof algebras are subject to an additional constraint which
% ensures the validity of the proofs (|proj_eq|).

% For instance, the law
%|proj_eq| states that the new term produced by application of the
%algebra is equal to the original term.\BO{other constraints?}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
