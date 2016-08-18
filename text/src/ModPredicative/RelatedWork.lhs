%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt

\section{Related and Future Work}\label{sec:modp:related}

\paragraph{DGP in proof-assistants}

Datatype-generic programming started out as a form of language
extension such as PolyP \cite{jansson:polyp} or Generic Haskell
\cite{loh:dsgh}. Yet Haskell has turned out to be powerful enough to
implement datatype-generic programming in the language itself and over
the time a vast number of DGP libraries for Haskell have been proposed
\cite{cheney:ligd,syb,emgm,multirec,instantgenerics,uniplate,genericderiving}. Compared
with a language extension, a library is much easier to develop and
maintain.

Using the flexibility of dependent-types there are multiple proposals
for performing datatype-generic programming in proof assistants
\cite{dgpcoq,altenkirch:gpwdtp,benke:universes,loh:gpif,indexedcontainers}. This
setting not only allows the implementation of generic functions, but
also of generic proofs. The approaches vary in terms of how strictly
they follow the positivity or termination restrictions imposed by the
proof assistant. Some circumvent the type-checker at various points to
simplify the development or presentation while others put more effort
in convincing the type-checker and termination checker of the validity
\cite{ertt}. However, in all of the proposals there does not seem to
be any fundamental problem caused by the restrictions.


\paragraph{DGP for modular proofs}

Modularly composing semantics and proofs about the semantics has also
been addressed by \cite{schwaab:mtp} in the context of programming
language meta-theory. They perform their development in Agda and
similar to our approach they also use a universe approach based on
polynomial functors to represent modular datatypes. They split
relations for small-step operational semantics and well-typing on a
feature basis. However, the final fixed points are constructed manually
instead of having a generic representation of inductive families.

Using Coq's type classes both MTC and our approach also allow for more
automation in the final composition of datatypes, functions and
proofs. Agda features instance arguments that can be used to replace
type classes in various cases. However, the current implementation
does not perform recursive resolution and as a result Agda does not
support automation of the composition to the extent that is needed for
DTC-like approaches.


\paragraph{Combining different DGP approaches}

We have shown an embedding of the universe of polynomial functors into
the universe of containers. Similar inclusions between universes have
been done in the literature \cite{morris:cspf}. Magalh\~aes and L\"oh
\cite{jpm:fcadgp} have ported several popular DGP approaches from
Haskell to Agda and performed a formal comparison by proving inclusion
relations between the approaches.

DGP approaches differ in terms of the class of datatypes they capture and the
set of generic functions that can be implemented for them. Generic functions
can be transported from a universe into a sub-universe. However, we are not
aware of any DGP library with a systematic treatment of universes where each generic
function is defined on the most general universe that supports that function.


\paragraph{DGP for abstract syntax}

We have shown how to obtain more reuse by complementing modular
definitions with a generic equality function and generic proofs of its
properties. Of course more generic functionality like traversals,
pretty-printing, parsing etc. can be covered by means of
datatype-generic programming.

One very interesting idea is to use datatype-generic programming to
handle variable binding \cite{cheney:synp,unbound}. Variable
binding is an ubiquitous aspect of programming languages. Moreover, a
lot of functionality like variable substitutions and free variable
calculations is defined for many languages. Licata and Harper
\cite{licata:ubc} and Keuchel and Jeuring \cite{sk:gcasr} define
universes for datatypes with binding in Agda. Lee et al.~\cite{gmeta}
develop a framework for first-order representations of variable
binding in Coq that is based on the universe of regular tree types
\cite{ertt} and that provides many of the so-called
\emph{infrastructure lemmas} required when mechanizing programming
language meta-theory.

An interesting direction for future work is to extend these approaches
to capture variable binding in the indices of relations on abstract
syntax and use this as the underlying representation of extensible
datatypes and extensible logical relations and thereby complementing
modular functions with generic proofs about variable binding.


\paragraph{Automatic derivation of instances}

Most, if not all, generic programming libraries in Haskell use Template
Haskell to derive the generic representation of user-defined types and
to derive the conversion functions between them.

The GMeta \cite{gmeta} framework includes a standalone tool that also
performs this derivation for Coq. Similarly we also like to be able
to derive instances for the |Container| and |Polynomial| classes
automatically.
