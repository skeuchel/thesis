%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt


\section{Related Work}\label{sec:related}

There is a myriad of earlier work on approaches to binder boilerplate in
language mechanization which generally falls in one of several categories:
meta-languages with built-in support for binding \cite{abella, beluga, twelf,
  nominal} that also take care of boilerplate automatically, code-generators
that produce code for proof-assistants \cite{lngen,dbgen}, libraries that use
reflection methods to derive code \cite{autosubst}, datatype-generic programming
libraries \cite{cfgv,gmeta} that implement boilerplate for a generic universe of
datatypes or libraries of reusable tactics \cite{phoas,dblib}. Due to the
abundance of approaches and lack of space, we focus only on related work that 
deals with semantic relations.

%-------------------------------------------------------------------------------
\paragraph{Specification Languages}
The \Ott tool \cite{ottjfp} allows the specification of concrete syntax of
languages, including binding specifications, and of inductive relations on
terms. However, well-scoping of relations is left unchecked in \Ott.  While \Ott
only generates datatype and function definitions for syntax and relations in multiple
proof-assistants, support for lemmas is provided by the additional
\LNGen\cite{lngen} tool which generates locally-nameless \Coq definitions
from an \Ott specification. It also generates syntax-related boilerplate but
does not tackle boilerplate for semantic relations.

%-------------------------------------------------------------------------------
\paragraph{Logical frameworks}
Logical frameworks like Abella \cite{abella}, Twelf
\cite{twelf} and Beluga \cite{beluga} are specifically designed to reason about
logics and programming languages. Their specialized meta-logic encourages the
use of higher-order abstract syntax (HOAS) to represent object-level variable
binding with meta-variable bindings. The advantage is that facts about
$\alpha$-equivalence and well-scoping and structural properties like
substitution, weakening and exchange are inherited from the meta-language.
Despite the large benefits of these systems, they are generally limited to
single variable binding and other constructs like patterns or recursive lets
have to be encoded by transforming the object language.

These systems also allow the use of higher-order judgements in the definition of
semantical relations and get substitution lemmas for free if the object-language
context admits exchange. If it does not admit exchange, there are techniques
like explicit contexts \cite{twelfwiki,mechanizedsml,belugaexplicitcontext} that
can be used to model relations which then require a manual proof of the
substitution lemma while still reaping all the benefits for the syntax.  This
is, for example, necessary to model dependently typed languages and also for the
\POPLmark challenge to isolate a variable in the middle of the context for
narrowing. In comparison, our derivation of substitution lemmas is independent
of any exchange property of contexts.


%-------------------------------------------------------------------------------
\paragraph{Decision procedures}
The authors of the \AutoSubst \cite{autosubst} have developed a language with
symbolic expressions for two sorts: de Bruijn terms and simultaneous de Bruijn
substitutions with an axiomatic equivalence \cite{debruijndecidability} based on
the reduction rules of the $\sigma$-calculus \cite{explicitsubstitutions} which
they show to coincide with the semantic equivalence on de Bruijn terms. They
have also developed a decision procedure, that automatically decides the
equivalence of two expressions. As a consequence, frameworks based on
simultaneous de Bruijn substitutions such as \AutoSubst can, in theory, derive
all the necessary rewrites for the inductive steps of the substitution lemma
automatically. In contrast, we derive the rewrites using syntax-directed
elaboration. However, the decision procedure of \cite{debruijndecidability} is
applicable in instances other that substitution lemmas.

%-------------------------------------------------------------------------------
\paragraph{Nominal representations}
Nominal Isabelle \cite{nominal} is an extension of the Isabelle/HOL framework
based on nominal logic \cite{nominallogic} with support for nominal datatype
terms which provides reasoning modulo $\alpha$-equivalence for free. It is also
possible to define and reason about semantic relations but for reasoning modulo
$\alpha$-equivalence we first need to show that the relations are equivariant.
These equivariance proofs are very similar to the proofs of shifting and
substitution lemmas for relation in the de Bruijn representation. We hence
conjecture that, in a nominal interpretation of \Knot, the binding functions of
\Knot are equivariant, i.e. they are binding operators in the sense of
\cite{bindingoperators} and that we can generically derive equivariance proofs
of semantics relations.

%-------------------------------------------------------------------------------
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

\section{Future Work}
\steven{Move to thesis conclusion}
An interesting direction for future work is to combine a datatype-generic
approach to variable binding with a datatype-generic approach to modular
reasoning like ours to combine the benefits of both worlds and achieve more
reuse.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
