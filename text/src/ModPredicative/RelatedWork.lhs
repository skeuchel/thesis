%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt

\section{Related and Future Work}\label{sec:modp:related}


\paragraph{DGP in proof-assistants}
\move{Datatype-generic programming started out as a form of language extension such as
PolyP \cite{jansson:polyp} or Generic Haskell \cite{loh:dsgh}. Yet Haskell has
turned out to be powerful enough to implement datatype-generic programming in
the language itself and over the time a vast number of DGP libraries for Haskell
have been proposed
\cite{cheney:ligd,syb,emgm,multirec,instantgenerics,uniplate,genericderiving}. Compared
with a language extension, a library is much easier to develop and maintain.
}

\move{
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
}

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
relations. Therefore our work on a generic strong induction principle for
modular definitions does not any benefits to Schwaab and Siek's approach and
MTC's generic folds would be sufficient. However, MTC's Church encodings are
rejected by Agda's type-checker because Agda is a fully predicative system.



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


\paragraph{DGP for abstract syntax}
We have shown how to obtain more reuse by complementing modular definitions with
a generic equality function and generic proofs of its properties. Of course,
there is more generic functionality that can be covered by means of
datatype-generic programming like traversals, pretty-printing, parsing
etc..

One very interesting idea is to use datatype-generic programming to handle
variable binding \cite{cheney:synp,unbound}. Variable binding is an ubiquitous
aspect of programming languages. Moreover, a lot of functionality like variable
substitutions and free variable calculations is defined for many
languages. Licata and Harper \cite{licata:ubc} and Keuchel and Jeuring
\cite{sk:gcasr} define universes for datatypes with binding in Agda. Lee et
al.~\cite{gmeta} develop a framework for first-order representations of variable
binding in Coq that is based on the universe of regular tree types \cite{ertt}
and that provides many of the so-called \emph{infrastructure lemmas} required
when mechanizing programming language meta-theory (cf. Part \ref{part:gen}).

\new{
An interesting direction for future work is to combine a datatype-generic
approach to variable binding with a datatype-generic approach to modular
reasoning like ours to combine the benefits of both worlds and achieve more
reuse.
}

\paragraph{Automatic derivation of instances}
Most, if not all, generic programming libraries in Haskell use Template
Haskell to derive the generic representation of user-defined types and
to derive the conversion functions between them.

The GMeta \cite{gmeta} framework includes a standalone tool that also
performs this derivation for Coq. Similarly we also like to be able
to derive instances for the |Container| and |Polynomial| classes
automatically.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
