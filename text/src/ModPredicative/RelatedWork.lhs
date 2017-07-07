%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt

\section{Related and Future Work}\label{sec:modp:related}

There is a fairly large amount of related work on modular programming and
datatype-generic proramming. Below we discuss the most relevant related to this
chapter: work on modular proofs and datatype-generic programming in proof
assistants.

\paragraph{DGP in proof-assistants}
Datatype-generic programming started out as a form of language extension such as
PolyP \cite{jansson:polyp} or Generic Haskell \cite{loh:dsgh}. Yet Haskell has
turned out to be powerful enough to implement datatype-generic programming in
the language itself and over the time a vast number of DGP libraries for Haskell
have been proposed
\cite{cheney:ligd,syb,emgm,multirec,instantgenerics,uniplate,genericderiving}. Compared
with a language extension, a library is much easier to develop and maintain.

There are multiple proposals for performing datatype-generic programming in
proof-assistants using the flexibility of dependent-types
\cite{dgpcoq,altenkirch:gpwdtp,benke:universes,loh:gpif,indexedcontainers}. This
setting not only allows the implementation of generic functions, but also of
generic proofs. The approaches vary in terms of how strictly they follow the
positivity or termination restrictions imposed by the proof-assistant. Some
circumvent the type-checker at various points to simplify the development or
presentation while others put more effort in convincing the type-checker and
termination checker of the validity~\cite{ertt}. However, in any of the
proposals there does not seem to be any fundamental problem caused by the
positivity or termination restrictions.

\paragraph{DGP for modular proofs}
Modularly composing semantics and proofs about the semantics has also been
addressed by \cite{schwaab:mtp} in the context of programming language
meta-theory. They perform their development in Agda and, similar to our
approach, they also use a universe approach based on polynomial functors to
represent modular datatypes. They split relations for small-step operational
semantics and well-typing on a feature basis. However, the final fixed-points
are constructed manually instead of having a generic representation of inductive
families.

Schwaab and Siek did not model functors, folds or induction operators concretely
but instead rely also on manual composition of algebras. Therefore, their
definitions have a more natural directly-recursive style. But as a consequence,
some of their definitions are not structurally recursive. Unfortunately Schwaab
and Siek circumvent Agda's termination checker instead of stratifying their
definitions.

Using Coq's type classes both MTC and our approach provide more automation in
the final composition of datatypes, functions and proofs. Agda features instance
arguments that can be used to replace type classes in various cases. Schwaab and
Siek's \cite{schwaab:mtp} developments took place when Agda's implementation did
not perform recursive resolution, and as a result Agda did not support
automation of the composition to the extent that is needed for DTC-like
approaches. However, as of Agda version 2.4.2 instance argument resolution is
recursive. Hence it should now be possible to augment Schwaab and Siek's
approach with full automation for composition and also port our approach to
Agda.

A notable difference is that Schwaab and Siek do not define a dependent recursor
for induction but instead completely rely on non-dependent recursion over
relations. Therefore the needs for a strong generic induction principle does not
arise in their work and MTC's generic folds for relations is sufficient for
their approach. However, MTC's Church encodings are rejected by Agda's
type-checker because Agda is a fully predicative system.


\paragraph{Combining different DGP approaches}
We have shown an embedding of the universe of polynomial functors into the
universe of containers. Similar inclusions between universes have been
presentend in the literature \cite{morris:cspf}. Magalh\~aes and L\"oh
\cite{jpm:fcadgp} have ported several popular DGP approaches from Haskell to
Agda and performed a formal comparison by proving inclusion relations between
the approaches including a port of the |regular| Haskell library that is
equivalent to our polynomial functor universe. However, they did not consider
containers in their comparison.

DGP approaches differ in terms of the class of datatypes they capture and the
set of generic functions that can be implemented for them. Generic functions can
be transported from a universe into a sub-universe. However, we are not aware of
any DGP library with a systematic treatment of universes where each generic
function is defined at the most general universe that supports that function.


\paragraph{Automatic derivation of instances}
Most, if not all, generic programming libraries in Haskell use Template
Haskell to derive the generic representation of user-defined types and
to derive the conversion functions between them.

The GMeta \cite{gmeta} framework includes a standalone tool that also performs
this derivation for Coq. Similarly, deriving instances for |Container| and
|Polynomial| classes automatically is possible. An alternative is presented in
\cite{levitation}. Chapman et al.'s goal is to reflect the datatype declarations
of the programming language automatically in the language itself, which are then
immediately available for datatype-generic programming.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
