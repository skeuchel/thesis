%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt


\section{Related Work}\label{sec:gen:casestudy:related}

There is plenty of existing work on specifications of programming language
syntax including formal machine-processable specifications. We focus only on
related work that target mechanization of meta-theory in proof-assistans.


\subsection{Specification Languages}
\Knot grew out of the \Ott specification language \cite{ottjfp} which allows the
specification of \emph{concrete syntax} of languages, including binding
specifications, and of inductive relations on terms. However, in contrast to
\Knot, well-scoping of relations is left unchecked in \Ott. The \Ott code
generator produces code for various proof assistants, including \Coq. While \Ott
only generates datatype and function definitions for syntax and relations,
support for lemmas is provided by the additional \LNGen\cite{lngen} tool which
generates syntax-related boilerplate for locally-nameless representations but
does not tackle any boilerplate for semantic relations.

Logical frameworks like Abella \cite{abella}, Twelf \cite{twelf} and Beluga
\cite{beluga} are specifically designed to reason about logics and programming
languages. Their specialized meta-logic encourages the use of higher-order
abstract syntax (HOAS) to represent object-level variable binding with
meta-variable bindings, i.e. datatype declarations in these frameworks already
serve as specifications of syntax including binding. However, generally only
direct support for single variable binding is provided and other binders have to
be encoded by transforming the object language. These systems also allow the use
of higher-order judgements which is used to model bindings at the level of
relations.


\subsection{Binding Boilerplate}

The approaches to tackle the binding boilerplate in mechanizations generally
fall in one of several categories: meta-languages with built-in support for
binding \cite{abella, beluga, twelf, nominal} that also take care of boilerplate
automatically, code-generators that produce code for proof-assistants
\cite{lngen,dbgen}, libraries that use reflection methods to derive code
\cite{autosubst}, datatype-generic programming libraries \cite{cfgv,gmeta} that
implement boilerplate for a generic universe of datatypes or libraries of
reusable tactics \cite{phoas,dblib}.

%-------------------------------------------------------------------------------
\paragraph{Logical frameworks}

%% substitution lemmas of relations are often provided for free by hypothetical
%% substitutions\footnote{If the object language context does not admit exchange
%%   the substitution lemmas for relations have to be proved manually using
%%   techniques like explicit contexts
%%   \cite{twelfwiki,mechanizedsml,belugaexplicitcontext} while still being able to
%%   reap all the benefits for the syntax.}

The advantage of logical frameworks based on higher-order abstract syntax is
that facts about $\alpha$-equivalence and well-scoping and structural properties
for substitution, weakening and exchange are inherited from the meta-language
and thus do not need to be proved separately. Substitution lemmas for semantical
relations are also provided for free if the object-language context admits
exchange. If it does not admit exchange, there are techniques like explicit
contexts \cite{twelfwiki,mechanizedsml,belugaexplicitcontext} that can be used
to model relations which then require a manual proof of the substitution lemma
while still reaping all the benefits for the syntax. This is, for example,
necessary to model dependently typed languages and also for the \POPLmark
challenge to isolate a variable in the middle of the context for narrowing. In
comparison, our derivation of substitution lemmas is independent of any exchange
property of contexts.


%-------------------------------------------------------------------------------
\paragraph{Decision Procedures}
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
\cite{genconv} define universes for datatypes with binding in Agda. Lee et
al.~\cite{gmeta} develop a framework for first-order representations of variable
binding in Coq that is based on the universe of regular tree types \cite{ertt}
and that provides many of the so-called \emph{infrastructure lemmas} required
when mechanizing programming language meta-theory (cf. Part \ref{part:gen}).

%-------------------------------------------------------------------------------
\paragraph{Nominal Representations}
Nominal Isabelle \cite{nominal} is an extension of the Isabelle/HOL framework
based on nominal logic \cite{nominallogic} with support for nominal datatype
terms which provides reasoning modulo $\alpha$-equivalence for free. It is also
possible to define and reason about semantic relations but for reasoning modulo
$\alpha$-equivalence we first need to show that the relations are equivariant.
These equivariance proofs are very similar to the proofs of shifting and
substitution lemmas for relation in the de Bruijn representation. We hence
conjecture that, in a nominal interpretation of \Knot, the binding functions of
\Knot are equivariant, i.e. they are binding operators in the sense of
\cite{bindingoperators} and that we can generically derive equivariance and
substitution lemmas for semantical relations on nominal terms.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
