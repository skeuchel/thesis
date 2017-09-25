%include lhs2TeX.fmt
%include forall.fmt
%include Formatting.fmt

\section{The \Knot Specification Language}
\label{sec:specification}

%% This section introduces \Knot, our language for specifying the abstract syntax
%% of programming languages and associated variable binder information. The
%% advantage of specifying programming languages in \Knot\ is straightforward: the
%% variable binder boilerplate comes for free for any well-formed \Knot\
%% specification.
%%
%% The syntax of \Knot\ allows programming languages to be expressed in terms of
%% different syntactic sorts, term constructors for these sorts and binding
%% specifications for these term constructors. The latter specify the number of
%% variables that are bound by the term constructors as well as their scoping
%% rules.


%-------------------------------------------------------------------------------

This section presents the \Knot~specification language for syntax with binders.

\subsection{\Knot~Syntax}

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
\textbf{Labels}\vspace{-5mm}
\[\begin{array}{l@@{\hspace{3mm}}r@@{\hspace{15mm}}l@@{\hspace{3mm}}r}
  \alpha, \beta, \gamma & \textit{Namespace label}       & s, t                  & \textit{Sort meta-variable}\\
  b                     & \textit{Binding meta-variable} & f                     & \textit{Function label}    \\
  g                     & \textit{Global meta-variable}  & E                     & \textit{Env label}         \\
  S, T                  & \textit{Sort label}            & R                     & \textit{Relation label}    \\
  K                     & \textit{Constructor label}     & r                     & \textit{Rule label}        \\
  \end{array}
\]
\textbf{Declarations and definitions}
\[\begin{array}{@@{}l@@{\hspace{2mm}}c@@{\hspace{3mm}}l@@{\hspace{5mm}}r}
  \spec      & ::=  & \ov{\decl}                                                                       & \textit{Specification}    \\
    \decl    & ::=  & \namedecl \mid \sortdecl \mid \fundecl                                           & \textit{Declaration}      \\
             & \mid & \envdecl \mid \reldecl                                                           &                           \\
  \namedecl  & ::=  & \namespace \,\alpha\,\ccol\,S                                                    & \textit{Namespace}        \\
  \sortdecl  & ::=  & \sort\,S\,\cass\,\ov{\condecl}                                                   & \textit{Sort}             \\
  \condecl   & ::=  & \texttt{+}  K\,\fieldref{g}{\alpha}                                              & \textit{Constr. decl.}    \\
             & \mid & \texttt{||} K\,\ov{\fieldbind{b}{\alpha}}\,\ov{\cpar{\cbrk{\bindspec}s \ccol S}} &                           \\
  \bindspec  & ::=  & \ov{\bsi}                                                                        & \textit{Binding spec.}    \\
  \bsi       & ::=  & b \mid f s                                                                       & \textit{Bind. spec. item} \\
  \fundecl   & ::=  & \function\, f \ccol S \cto [\ov{\alpha}]\,\cass\,\ov{\funclause}                 & \textit{Function}         \\
  \funclause & ::=  & K\,\ov{b}\,\ov{s} \cto \bindspec                                                 & \textit{Function clause}  \\
  \envdecl   & ::=  & \env\,E\,\cass\,\ov{\envclause}                                                  & \textit{Environment}      \\
  \envclause & ::=  & \texttt{+}  K                                                                    & \textit{Empty env.}       \\
             & \mid & \texttt{||} K : \alpha \cto \ov{S} : R                                           & \textit{Env. clause}      \\
%             & ::=  & \alpha \cto \ov{S}                                                               &                           \\
  \end{array}
\]
  \end{minipage}
}
\end{center}
\caption{The Syntax of \Knot}
\label{fig:SpecificationLanguage}
\end{figure}

Figure \ref{fig:SpecificationLanguage} shows the grammar of \Knot.  A
\Knot language specification $\spec$ consists of variable namespace
declarations $\namedecl$, syntactic sort declarations $\sortdecl$, function
declarations $\fundecl$, environment declarations $\envdecl$ and relation
declarations $\reldecl$. We defer explaining relation declarations until Section
\ref{ssec:inductiverelations}.

A namespace declaration $\namespace~\alpha : S$ introduces the namespace
$\alpha$ and associates it with the syntactic sort $S$. This expresses that variables of
namespace $\alpha$ can be substituted for terms of sort $S$. While most
languages feature at most one namespace per sort, it is nevertheless possible to
associate multiple namespaces with a single sort. This can be used, e.g.,
in languages with linear type systems to distinguish linearly bound from unrestricted variables.

A declaration of sort $S$ comes with two kinds of constructor declarations
$\condecl$. Variable constructors $\texttt{+} K\,\fieldref{|g|}{\alpha}$ hold a
variable reference $g$ in the namespace $\alpha$. These are the only
constructors where variables are used as references. The global variable
reference $g$ signifies that the reference is free when considering a variable
constructor in isolation. In larger symbolic expressions, also binding
variables may appear in variable constructors.

Regular constructors $K\,\ov{(b : \alpha)}\,\ov{(s : S)}$ contain
named variable bindings $\ov{(b : \alpha)}$ and named subterms $\ov{(s :
  S)}$. For the sake of presentation we assume that the variable bindings
precede subterms. The distinction between variable and regular constructors
follows straightforwardly from \Knot's free-monad-like view on syntax.  This rules
out languages for normal forms, but as they require custom behavior
(renormalization) during substitution \cite{anormalform,clf} their substitution
boilerplate cannot be defined generically anyway.

Every subterm $s$ is preceded by a binding specification $\bindspec$ that
stipulates which variable bindings are brought in scope of $s$. The binding
specification consists of a list of items $\bsi$. An item is either a singleton
variable binding $b$ of the constructor or the invocation of a function $f$,
that computes which variables in siblings or the same subterm are brought in
scope of $s$. Functions serve in particular to specify multi-binders in binding
specifications. In regular programming languages the binding specifications of
most subterms are empty; to avoid clutter we omit them in that case.

Functions are defined by function declarations $\fundecl$. The type signature
$f : S \rightarrow [\ov{\alpha}]$ denotes that function $f$ operates on terms of
sort $S$ and yields variables in namespaces $\ov{\alpha}$. The function itself
is defined by exhaustive case analysis on a term of sort $S$.  A crucial
requirement is that functions cannot be defined for sorts that have variables.
Otherwise it would be possible to change the set of variables that a pattern
binds with a substitution. The specification of the output type $\ov{\alpha}$ is
used in \cite{knotneedle} to derive subordination-based strengthening lemmas.
However, these lemmas are not necessary to derive the semantics
boilerplate. Hence, for simplicity we ignore the output type of functions and
any other subordination related information in the remainder of this paper.

Environments $E$ represent a mapping from variables in scope to additional data
such as typing information. To this end, an environment declaration $\envdecl$
consists of named clauses $K : (\alpha \cto \ov{S} : R)$ that stipulate that
variables in namespace $\alpha$ are mapped to terms of sorts
$\ov{S}$. Additionally, we specify that this clause can be substituted for
judgement of relation $R$. If the relation $R$ is omitted, then it defaults to
well-scopedness of the data. We clarify this, together with the syntax of
inductive relations, in Section \ref{ssec:inductiverelations}.

%format namespace = "{\namespace}"
%format sort = "{\sort}"
%format fun = "{\function}"
%format @ = "{\texttt{@}}"
%format case = "\Varid{case}"
%format env = "{\env}"
\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{tabular}{l@@{\hspace{0.3mm}}c@@{\hspace{0.1mm}}l@@{\hspace{0.5mm}}l@@{\hspace{0.3mm}}c@@{\hspace{0.1mm}}l}
        \multicolumn{3}{@@{}l}{|namespace Tyv : Ty|}                                 & \multicolumn{3}{@@{}l}{\sort~|Ty|~\cass}                \\
        \multicolumn{3}{@@{}l}{|namespace Tmv : Tm|}                                 &  & \texttt{+}  & |tvar (X@Tyv)|                         \\
        \multicolumn{3}{@@{}l}{|sort Pat|~\cass}                                     &  & \texttt{||} & |tarr (T1: Ty) (T2: Ty)|               \\
         & \texttt{||} & |pvar (x:Tmv) (T:Ty)|                                       &  & \texttt{||} & |tall (X:Tyv) (bindspec X T: Ty)|      \\
         & \texttt{||} & |ppair (p1: Pat) (bindspec (bind p1) p2:Pat)|               &  & \texttt{||} & |tprod (T1: Ty) (T2: Ty)|              \\
        \multicolumn{3}{@@{}l}{|sort Tm|~\cass}                                      &  & \texttt{||} & |texist (X:Tyv) (bindspec X T: Ty)|    \\
         & \texttt{+}  & |var (x@Tmv)|                                               & \multicolumn{3}{@@{}l}{|fun bind : Pat -> [Tmv]|~\cass} \\
         & \texttt{||} & |abs (x:Tmv) (T: Ty) (bindspec x t: Tm)|                    &  & \texttt{||} & |pvar x T    -> x|                     \\
         & \texttt{||} & |app (t1: Tm) (t2: Tm)|                                     &  & \texttt{||} & |pprod p1 p2 -> bind p1 , bind p2|     \\
         & \texttt{||} & |tabs (X:Tyv) (bindspec X t: Tm)|                           & \multicolumn{3}{@@{}l}{|env Env|~\cass}                 \\
         & \texttt{||} & |tapp (t: Tm) (T: Ty)|                                      &  & \texttt{+}  & |empty|                                \\
         & \texttt{||} & |pair (t1:Tm) (t2:Tm)|                                      &  & \texttt{||} & |evar  : Tmv| \cto |Ty : Typing|       \\
         & \texttt{||} & |case (t1:Tm) (p:Pat) (bindspec (bind p) t2:Tm)|            &  & \texttt{||} & |etvar : Tyv| \cto                     \\
         & \texttt{||} & |pack (T1: Ty) (t: Tm) (T2: Ty)|                            &  & & \\
         & \texttt{||} & \multicolumn{4}{@@{}l}{|unpack (t1: Tm) (X: Tyv) (x: Tmv) (bindspec (X,x) t2: Tm)|} \\
      \end{tabular}
    \end{minipage}
  }
  \caption{Example specification of $\fexistsprod$}
  \label{fig:systemfexists}
\end{figure}

\paragraph{Example} Figure \ref{fig:systemfexists} shows the \Knot~specification
of $\fexistsprod$. We start with the declaration of two namespaces: |Tyv| for
type variables and |Tmv| for term variables, which is followed by the
declarations of three sorts: types, terms and patterns and a function
declaration for |bind| that specifies the variables bound by patterns.

As announced, we have omitted the empty binding specifications $\cbrk{}$ for
readability. There are only seven non-empty binding
specifications: universal and existential quantification for types and type
abstraction for terms bind exactly one type variable, the lambda abstraction for
terms binds exactly one term variable, the unpacking of an existential binds a
type and a term variable, the pattern matching binds the variables bound by the
pattern in the body and in the product of a pattern the variables of the first
component are bound in the second.

The last declaration defines typing environments that map term variables to
types. It also states that the term variable clause is substitutable for
|Typing| judgements, defined in Section
\ref{ssec:inductiverelations}. Type variables are not mapped to any data, but a
clause still needs to be declared to require well-scopedness of types.


%-------------------------------------------------------------------------------

\subsection{Well-Formed \Knot~Specifications}\label{sec:wellformedspec}
%format spec     = "\spec"
%format condecl  = "\condecl"


%format vdashS = "\vdash_{" S "}"
\begin{figure}[t]
\begin{center}
\fbox{
  \small
  \begin{minipage}{0.98\columnwidth}
%if showFun
    \[ \begin{array}{ll}
         \VENV & ::= \ov{\alpha : S}  \hspace{2.7cm}                                                                          %% & \text{Var. assoc.}   \\
         \Phi \quad  ::=  \ov{f : S \rightarrow [\ov{\alpha}]}                                                               \\ %% & \text{Function env.} \\
         \LENV & ::= \ov{([bs]b : \alpha)},\ov{([bs]s : S)},\ov{(g @@ \alpha)},\ov{([\bindspec]~\jmv:R~\ov{\symbolicterm})} \\ %% & \text{Local env.}    \\
       \end{array}
    \]
%else
    \[ \VENV ::= \ov{\alpha : S} \hspace{1cm}
       \LENV ::= \ov{([bs]b : \alpha)}, \ov{(g @@ \alpha)}
    \]
%endif
  \hrule \vspace{2mm}
  \framebox{\mbox{$\vdash \spec$}} \\
  \[ \inferrule* [right=\textsc{WfSpec}]
       {\VENV = \ov{\alpha : T} \\
         \ov{\ov{\vdash_S \condecl}}
       }
       {\vdash
         \ov{\namespace~\alpha : T}\;
         \ov{\sort~S \cass \ov{\condecl}}
       }
  \]

  \framebox{\mbox{$\vdash_S \condecl$}} \\
  \[ \qquad
     \begin{array}{c}
       \inferrule* [right=\textsc{WfVar}]
         {\alpha : S \in \VENV
         }
         {\vdash_S K\,(g@@\alpha)} \quad\quad
%if showFun
       \inferrule*[right=\textsc{WfReg}]
         {\LENV = \ov{([\bindspec_b]b:\alpha)},\ov{([\bindspec_t]t : T)} \\
          \ov{\wfbindspec{\epsilon}{\bindspec_b}{|depsOf S|}} \\
          \ov{\wfbindspec{\epsilon}{\bindspec_t}{|depsOf S|}} \\\\
          \forall f. f~(K~\ov{b'}~\ov{t'}) = \bindspec' \Rightarrow
           \wfbindspec{\epsilon}{[b' \mapsto b,t' \mapsto t]bs'}{\ov{\beta}}
         }
         {\vdash_S K~\ov{(b : \alpha)}~\ov{([\bindspec_t]t : T)}
         }
%else
       \inferrule*[right=\textsc{WfReg}]
         {\LENV = \ov{([\bindspec_b]b:\alpha)} \\\\
          \ov{\wfbindspec{\epsilon}{\bindspec_b}{|depsOf S|}} \\
          \ov{\wfbindspec{\epsilon}{\bindspec_t}{|depsOf S|}}
         }
         {\vdash_S K~\ov{(b : \alpha)}~\ov{([\bindspec_t]t : T)}
         }
%endif
     \end{array}
  \]

  \framebox{\mbox{$\wfbindspec{\bindspec}{\bindspec}{\ov{\alpha}}$}} \\
  \[ \qquad
     \begin{array}{c}
       \inferrule* [right=\textsc{WfNil}]
         {\,}
         {\wfbindspec{\bindspec}{\epsilon}{\ov{\alpha}}
         } \quad
       \inferrule* [right=\textsc{WfSng}]
         {([\bindspec]b : \beta) \in \LENV \\
          %% \beta \in \ov{\alpha} \\
          \wfbindspec{\bindspec, b}{\bindspec'}{\ov{\alpha}} \\
         }
         {\wfbindspec{\bindspec}{b, \bindspec'}{\ov{\alpha}}
         } \\\\
%if showFun
       \inferrule* [right=\textsc{WfCall}]
         {([\bindspec]t : T) \in \LENV \\
          %% \ov{\beta} \subseteq \ov{\alpha} \\
          f : T \to [\ov{\beta}] \in \Phi \\
          \wfbindspec{\bindspec, f~t}{\bindspec'}{\ov{\alpha}}
         }
         {\wfbindspec{\bindspec}{f~t, \bindspec'}{\ov{\alpha}}
         }
%endif
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Well-formed specifications}
\label{fig:wellformedspec}
\end{figure}

This section defines which \Knot specifications are well-formed.  To simplify
the explanation of well-formedness and of the semantics of \Knot\
specifications, we disregard both function declarations and only consider
single-variable binding for the rest of this section and the following. See the
technical appendix for the extended formalisation.

Figure \ref{fig:wellformedspec} defines the well-formedness relation
$\vdash \spec$ for \Knot\ specifications. The single rule \textsc{WfSpec}
expresses that a specification is well-formed if each of the constructor
declarations inside the sort declarations is and the meta-environment $\VENV$
contains exactly the declared namespaces.

The auxiliary well-sorting relation $\vdash_S \condecl$ denotes that constructor
declaration $\condecl$ has sort $S$.  There is one rule for each constructor
form. Rule \textsc{WfVar} requires that the associated sort of the variable
namespace matches the sort of the constructor.  Rule \textsc{WfReg} handles
regular constructors. It builds a constructor-local meta-environment $\LENV$ for
binding fields $([\bindspec_b]b:\alpha)$. The binding specification
$\bindspec_b$ of a binding $b$ denotes the \emph{local scope} into which the
corresponding object-variable is introduced.  The local scope is left implicit
in the syntax; hence, it needs to be inferred in this rule. The binding
specifications of fields are checked against $\LENV$.  Also, we check clauses of
function declarations as part of this rule. We use the notation
$f~(K~\ov{b'}~\ov{t'}) = \bindspec'$ to look up the clause of $f$ for
constructor $K$. After proper renaming, the right-hand side of each functional
clause has to be consistent with $\LENV$.

The relation $\wfbindspec{\bindspec_1}{\bindspec_2}{\ov{\alpha}}$ in Figure
\ref{fig:wellformedspec} denotes that binding specification $\bindspec_2$ is
well-formed with respect to the scope $\bindspec_1$.
% and is typed heterogeneously with elements from namespaces $\ov{\alpha}$.
The relation ensures that the order of different binding items has is
consistent across all binding specifications and there are no gaps. For
instance, if one of the binding specifications is $[b_0,b_1,b_2]$ then another
field of the same constructor cannot have the binding specification
$[b_0,b_2,b_1]$ or $[b_0,b_2]$. This restriction prevents the user
from relying on a structural exchange property of environments when specifying
inductive relations which in turn enables us to deal with environment
well-scopedness generically in the derivation of judgement well-scopedness
lemmas.

Rule \textsc{WfNil} regulates the base case of an empty binding specification
that is always well-scoped. By rule \textsc{WfSng} a singleton binding is
well-scoped if the local scope $\bindspec$ is consistent with the information in
the local environment $\LENV$ and it checks the tail $\bindspec'$ in the
extended scope $\bindspec,b$.

Including function calls in the binding specification requires checking them for
well-scopedness too which can be found in Appendix
\ref{app:sec:wellformedspec}. In short: For calling a function
$(f : T \to \ov{\alpha})$ on a field $([\bindspec]t : T)$ we require
$\wfbindspec{\bindspec}{f~t}{\ov{\alpha}}$, i.e. the local scope of the function
call is the binding specification of $s$. However, this forbids cyclic binding
specifications. As a consequence it is impossible to define scoping constructs
such as recursive scoping. This is a trade-off between expressivity and
simplicity. We plan to add multiple (potentially circular) input scopes in
future work, so that recursive constructs can be checked with two scopes: one
for declaration heads and one for declaration bodies.

%if False
\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$\vdash \envdecl$}} \\
  \vspace{-5mm}
  \[ \inferrule* [right=\textsc{WfEnv}]
                 {\vdash_E \envclause_i \quad (\forall i)}
                 {\vdash \env~E~\ov{\envclause}}
  \]
  \framebox{\mbox{$\vdash_E \envclause$}} \\
  \vspace{-5mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{WfEnvClause}]
                 {\,}
                 {\vdash_E : \alpha \rightarrow \ov{S}}
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Well-formed environment specifications}
\label{fig:wellformedctxspec}
\end{figure}
%endif


%-------------------------------------------------------------------------------

\subsection{Symbolic Expressions}

\stevennote{MOVED FROM OVERVIEW}{
Because this rule inspects the context $\Gamma$ we call it \emph{not context
  parametric}. The other rules either pass the context through unchanged or pass
an extended context to the premises. We call these rules \emph{context
  parametric}.
%
Rule \textsc{TAbs} deals with abstractions over terms in terms. The
meta-variable $y$ appears in a different mode in the conclusion than the
meta-variable $x$ in the variable rule. The $\lambda$-abstraction binds the
variable $y$ and we call it a \emph{binding occurrence} whereas the $x$ in the
variable rule is a \emph{reference} or \emph{use occurrence}.
%
Following the literature on \emph{locally nameless}~\cite{locallynameless} and
\emph{locally named}~\cite{externalinternalsyntax} representations we call $y$ a
\emph{locally bound} variable (aka locally scoped variables \cite{pitts2015}),
or more concisely a \emph{binding variable}, and $x$ a \emph{global} or
\emph{free variable}. Another example is the judgement
$\typing{\Gamma}{(\lambda y. y)~x}{\tau}$. Here $y$ is again locally bound and
$x$ has to be bound in $\Gamma$ for the judgement to be well-scoped. In this
example, the meta-variable $y$ appears in both binding and referencing
positions.
%
The distinction between locally bound and free variables goes back to at least
Frege \cite{begriffsschrift} and representations such as locally nameless and
locally named have internalized this distinction. Frege characterizes free
variables as variables that can possibly stand for anything while locally bound
variables stand for something very specific. Indeed, in the above judgement, the
use of $y$ can only denote a reference to the directly enclosing
abstraction. These concepts do not commit us to a particular representation of
variable binding. Rather, these notions arise naturally in meta-languages.
%
The rules \textsc{TTApp} for type-application and \textsc{TPack} for packing
existential types use a type-substitution operation $[\alpha\mapsto\sigma]\tau$
that substitutes $\sigma$ for $\alpha$ in $\tau$. \textsc{TTApp} performs the
substitution in the conclusion while \textsc{TPack} does so in the premise. The
substituted type-variable $\alpha$ is locally bound in both rules.
}

\stevennote{MOVED FROM OVERVIEW}{
As the term in the conclusion remains a type application, we want to apply rule
\textsc{TTApp} again. However, the \colorbox{light-gray}{type} in the conclusion
does not have the appropriate form. We first need to commute the two substitutions
with one of the common interaction lemmas
\begin{align}
  [\beta\mapsto \sigma][\alpha \mapsto \sigma'] =
  [\alpha \mapsto [\beta\mapsto\sigma]\sigma'][\beta\mapsto\sigma] \label{lem:substcomm}
\end{align}
%
Intuitively this commutation is possible because $\beta$ is a free variable
while $\alpha$ is locally bound and because context parametric rules are
naturally compatible with any changes to the context.
}

\stevennote{MOVED FROM OVERVIEW}{
A key principle is the distinction between \emph{locally bound} and \emph{free}
variables at the meta-level. This allows us to recognize \emph{context
parametric} rules which in turn enables us to extend the \emph{free-monadic
view} on syntax \cite{monadic,knotneedle} of \Knot to relations. At the
syntax-level this view requires one distinguished \emph{variable constructor}
per namespace which has a \emph{reference occurrence} as its only argument and
all other constructors only contain \emph{binding occurrences} and subterms.
%
At the level of relations this translates to one distinguished \emph{variable
  rule} per namespace (or more specifically per environment clause). This
variable rule has a single lookup as its only premise and the sorts of the
environment data match the sorts of the indices of the relation. The variable
rule uses exactly one \emph{free meta-variable}; all other rules only contain
\emph{locally bound} meta-variables and do not feature lookup premises.  In
other words, the variable rule is the only not context parametric rule.
%
These restrictions allow us to generically establish the substitution lemmas
for relations. Consider the small proof tree on the left:
% , where $A$ is the subtree for the typing judgement of $e_1$.
}

\begin{figure}[t!]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
    \small
    \[ \begin{array}{@@{}l@@{\hspace{2mm}}c@@{\hspace{2mm}}l@@{\hspace{10mm}}r}
         \symbolicterm & ::=  & s \mid K~\ov{b}~\ov{\symbolicterm} \mid \symbolicweaken~\symbolicterm~\bindspec & \textit{Symbolic exp.} \\
                       & \mid & K~g \mid K~b \mid  \symbolicsubst~b~\symbolicterm~\symbolicterm                 &                        \\
       \end{array}
    \]

  %---------------------------------------------------------------------------
  \hrule \vspace{2mm}
  \framebox{\mbox{$\wfsym{\bindspec}{\symbolicterm}{S}$}} \\
  \[ \qquad
     \begin{array}{c}
       \inferrule* [right=\textsc{SymReg}]
         {K : (\ov{[\bindspec_b]b:\alpha}) \to
              (\ov{[\bindspec_t]t:T}) \to S \\\\
          \ov{([\{b \mapsto b'\}\bindspec_b]b':\alpha) \in \LENV} \\
          \ov{\LENV; \bindspec,\{b \mapsto b'\}\bindspec_t \vdash \symbolicterm : T}
         }
         {\wfsym{\bindspec}{K~\ov{b'}~\ov{\symbolicterm}}{S}
         } \\\\
       \hspace{-5mm}
       \inferrule* [right=\textsc{SymVar}]
         {[\bindspec]s:S \in \LENV}
         {\wfsym{\bindspec}{s}{S}
         } \quad
       \inferrule* [right=\textsc{SymGbl}]
         {K : \alpha \to S \\\\
          (g@@\alpha) \in \LENV
         }
         {\wfsym{\bindspec}{K~g}{S}
         } \quad
       \inferrule* [right=\textsc{SymLcl}]
         {K : \alpha \to S \\\\
          ([\bindspec]b:\alpha) \in \LENV
         }
         {\wfsym{\bindspec,b,\bindspec'}{K~b}{S}
         } \\\\
       \inferrule* [right=\textsc{SymWeaken}]
         {\wfsym{\bindspec}{\symbolicterm}{S}
         }
         {\wfsym{\bindspec, \bindspec'}{\symbolicweaken~\symbolicterm~\bindspec'}{S}
         } \\\\
       \inferrule* [right=\textsc{SymSubst}]
         {([\bindspec]x:\alpha) \in \LENV \\
          (\alpha:T) \in \VENV \\
          \wfsym{\bindspec}{\symbolicterm_1}{T} \\
          \wfsym{\bindspec, x}{\symbolicterm_2}{S}
         }
         {\wfsym{\bindspec}{\symbolicsubst~x~\symbolicterm_1~\symbolicterm_2}{S}
         } \\
     \end{array}
  \]

  \end{minipage}
}
\end{center}
\caption{Symbolic expressions and their well-formedness}
\label{fig:symbolicevaluation}
\end{figure}

This section defines \emph{symbolic expressions} on top of specification
declarations. These are needed for the declaration of inductive relations on
sorts. The general idea is that we extend sort terms with meta-variables and
with symbolic constructs for meta-operations such as substitution. These
meta-variables are distinct from the object-language variables. We can for
example have a meta-variable for a term of a sort that has no namespaces.

Figure \ref{fig:symbolicevaluation} (top) contains the grammar for symbolic
expressions. An expression is a meta-variable $s$ or a regular constructor
applied to variable bindings and other symbolic expressions
$(K~\ov{b}~\ov{\symbolicterm})$.  For variable constructors we need to make a
distinction between global $(K~g)$ and local references $(K~b)$. Furthermore, a
symbolic expression can also be a reified substitution
$(\symbolicsubst~b~\symbolicterm_1~\symbolicterm_2)$, that denotes a
substitution of $\symbolicterm_1$ for $b$ in $\symbolicterm_2$. We only allow
substitution of locally bound variables to ensure context parametricity. The
last expression former is a refied weakening
$(\symbolicweaken~\symbolicterm~\bindspec)$ that makes context changes
explicit. For example consider $\eta$-reduction for $\fexistsprod$:
$$|abs x T (app (weaken t x) (var x))| \longrightarrow_\eta |t|.$$
Here the term $t$ is assumed to be in the outer context of the whole expression
and is explicitly weakened under the abstraction. The symbolic weakening implies
and replaces freshness conditions. We discuss larger examples of symbolic
expressions after introducing inductive relations in Section
\ref{ssec:inductiverelations}.


%-------------------------------------------------------------------------------
\subsection{Expression Well-formedness}

When using symbolic expressions we also want to ensure that these are
well-sorted and well-scoped with respect to the specification and scoping rules
that are defined by the binding specifications of the sorts. Symbolic
expressions can themselves introduce new bindings and local references have to
be checked to be locally bound. Therefore, we need to keep track of all local
bindings that are in scope. We reuse the representation of binding
specifications $\bindspec$ to also represent \emph{local scopes}.

The checking is complicated by the fact that arbitrary expressions
may appear in a term constructor that contains a binding specification with
function calls. So to define well-scopedness of expressions, we first have to
define symbolic evaluation of functions on expressions. This evaluation
normalizes function calls $f~\symbolicterm$ down to ordinary binding
specifications that only contain function calls on meta-variables
$f~s$. During evaluation we need to pattern match regular term constructions
against function clauses. This pattern matching yields a symbolic environment
$\symbolicenv$ that maps binding meta-variables to new names and sort
meta-variables to expressions. Symbolic environments $\symbolicenv$ are
defined in Figure \ref{fig:symbolicevaluation} (top).

\paragraph{Symbolic Evaluation} Figure \ref{fig:symbolicevaluation} (middle)
contains definitions for the symbolic evaluation as a big-step operational
semantics. The relation $\evalbig{\symbolicenv}{\bindspec_1}{\bindspec_2}$
defines the evaluation of the binding specification $\bindspec_1$ with respect
to environment $\symbolicenv$.

Rule \textsc{EvalNil} handles the empty case and rule \textsc{EvalSng} the
singleton case in which we simply use the new name of the binding variable and
evaluate recursively. The case of a function call is delegated to the relation
$\evalbigf{f}{\symbolicterm}{\bindspec}$ that explains the evaluation of the
function $f$ on the expression $\symbolicterm$. The straightforward case of a
meta-variable is handled by \textsc{EvalCallVar}. Rule \textsc{EvalCallCon}
handles expressions built by a regular constructor. It builds up an
environment $\symbolicenv$ that maps the left-hand side |(overline x)
(overline s)| of the function clause to the fields of the symbolic
construction and evaluates the right-hand side of the clause.

Notably absent from the symbolic evaluation are rules for reified
substitutions and reified weakenings. The de Bruijn representation admits for
example the rule
$$
\inferrule* []
 { \evalbigf{f}{\symbolicterm_2}{\bindspec'}
 }
 { \evalbigf{f}{\symbolicsubst~x~\symbolicterm_1~\symbolicterm_2}{\bindspec'}
 }.
$$
Yet, adding this rule would break subject reduction of symbolic
evaluation. The reason is that the typing of $\bindspec$ in Figure
\ref{fig:symbolicevaluation} (bottom) is not strong enough to keep track of
the scope when performing substitutions or weakenings. In essence, the result
cannot be $\bindspec'$ but has to be ``$\bindspec'$ without $x$''. Tracking
scopes during substitutions or other user-defined functions is the focus of
research on \emph{binding safe programming}~\cite{freshlook,romeo}. In the
framework of \cite{freshlook}, $\bindspec'$ in the premise and conclusion of
the above rule are two distinct (chains of) weak links with distinct types
which are in a commutative relationship with the world inclusion induced by
the substitution.

We side-step the issue by sticking to the simple scope checking of Figure
\ref{fig:symbolicevaluation} (bottom) and effectively disallow symbolic
substitutions and weakenings to appear in positions that are accessed by
functions. Another consequence is that substitution and weakening are only
allowed ``at the end of the context''. These restrictions are usually met by
relations for typing and operational semantics, and thus do not get in the
way of type-safety proofs. However, it may be too restrictive for other kinds
of meta-theoretical formalizations.


%% The two remaining rules \textsc{EvalCallWeaken} and \textsc{EvalCallSubst}
%% explain evaluation in case of symbolic weakening or substitution. These
%% operations only affect free variables in a term and do not change its binding
%% structure.  Hence the rules ignore the operation and directly evaluate the
%% function on the original symbolic term.


% \begin{figure}[t]
% \begin{center}
% \fbox{
%   \begin{minipage}{0.95\columnwidth}
%   \framebox{\mbox{$\wfsym{\bindspec}{\symbolicterm}{S}$}} \\
%   \vspace{-7mm}
%   \[ \begin{array}{c}
%      \inferrule* [right=\textsc{SymVar}]
%        {[\bindspec]s:S \in \LENV}
%        {\wfsym{\bindspec}{s}{S}
%        } \\\\
%      \inferrule* [right=\textsc{SymGlobal}]
%        {K : \alpha \to S \\ (g@@\alpha) \in \LENV
%        }
%        {\wfsym{\bindspec}{K~g}{S}
%        } \\\\
%      \inferrule* [right=\textsc{SymLocal}]
%        {K : \alpha \to S \\ ([\bindspec]b:\alpha) \in \LENV
%        }
%        {\wfsym{\bindspec,b,\bindspec'}{K~b}{S}
%        } \\\\
%      \inferrule* [right=\textsc{SymReg}]
%        {K : (\ov{[\bindspec_b]b:\alpha}) \to
%             (\ov{[\bindspec_t]t:T}) \to S \\
%         \ov{\evalbig{\ov{b \mapsto b'}, \ov{t \mapsto \symbolicterm}}{\bindspec_b}{\bindspec_{b'}}} \\
%         \ov{([\bindspec_{b'}]b':\alpha) \in \LENV} \\
%         \ov{\evalbig{\ov{b \mapsto b'}, \ov{t \mapsto \symbolicterm}}{\bindspec_t}{\bindspec_{\symbolicterm}}} \\
%         \ov{\LENV; \bindspec,\bindspec_{\symbolicterm} \vdash \symbolicterm : T}
%        }
%        {\wfsym{\bindspec}{K~\ov{b'}~\ov{\symbolicterm}}{S}
%        } \\\\
%      \inferrule* [right=\textsc{SymWeaken}]
%        {\wfsym{\bindspec}{\symbolicterm}{S}
%        }
%        {\wfsym{\bindspec, \bindspec'}{\symbolicweaken~\symbolicterm~\bindspec'}{S}
%        } \\\\
%      \inferrule* [right=\textsc{SymSubst}]
%        {([\bindspec]x:\alpha) \in \LENV \\ (\alpha:T) \in \VENV \\
%         \wfsym{\bindspec}{\symbolicterm_1}{T} \\
%         \wfsym{\bindspec, x}{\symbolicterm_2}{S}
%        }
%        {\wfsym{\bindspec}{\symbolicsubst~x~\symbolicterm_1~\symbolicterm_2}{S}
%        } \\
%      \end{array}
%   \]
%
%   \end{minipage}
% }
% \end{center}
% \caption{Well-formed symbolic expression}
% \label{fig:wellformedsymbolicexpressions}
% \end{figure}

\paragraph{Well-formedness}
Finally, Figure \ref{fig:symbolicevaluation} (bottom) shows the definition of
well-formedness of symbolic expressions. The relation
$\wfsym{\bindspec}{\symbolicterm}{S}$ denotes that the symbolic expression
$\symbolicterm$ has sort $S$ and is well-formed in scope $\bindspec$ under the
local environment $\LENV$.

The rule \textsc{SymVar} looks up the sort and scope of a meta-variable for a
sort term in $\LENV$. Variable constructors are handled by two rules.  Rule
\textsc{SymLcl} is used in case the variable is bound locally and $\bindspec'$
represents the difference to the scope of the binding. Global variables are
handled by rule \textsc{SymGbl}. The case of a regular constructor is handled by
rule \textsc{SymReg}. For each of the fields $[\bindspec_t]t:T$ the binding
specification $\bindspec_t$ the corresponding symbolic expression
$\symbolicterm$ is checked in the extended scope
$(\bindspec,\{b \mapsto b'\}\bindspec_t)$ where $\{b \mapsto b'\}$ denotes
simultaneous renaming of the bindings $b$ to $b'$. Rule $\textsc{SymWeaken}$
strengthens the scope $\bindspec,\bindspec'$ of a symbolic weakening
$(\symbolicweaken~\symbolicterm~\bindspec')$. The symbolic expression
$\symbolicterm$ is checked in the stronger scope $\bindspec$. Finally, rule
$\textsc{SymSubst}$ takes care of single variable substitutions.  The expression
$\symbolicterm_2$ lives in the extended scope $\bindspec,b$. Hence, only
substitution of the last introduced binding is allowed. The sort and scope of
the substitute $\symbolicterm_1$ have to agree with that of $b$.


%-------------------------------------------------------------------------------

\subsection{Inductive Relations}\label{ssec:inductiverelations}

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
    \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l@@{\hspace{-6mm}}r}
        \jmv          & ::=  &                                                                      & \textit{Judgement var.}        \\
        \reldecl      & ::=  & \relation\, \cbrk{E} \,R\,\ov{S}\,:=\,\ov{\ruledecl}                 & \textit{Relation decl.}        \\
                      & \mid & \relation\, R\,\ov{S}\,:=\,\ov{\ruledecl}                            &                                \\
        \ruledecl     & ::=  & \texttt{+} r : \lookup\cto\judgement \quad\mid\quad \texttt{||} r : \ov{\formula}\cto\judgement ; \ov{f = \rulebindspec}                                & \textit{Rule decl.}            \\
%         \ruledecl     & ::=  & \texttt{+} r : \lookup\cto\judgement                                 & \textit{Rule decl.}            \\
%                       & \mid & \texttt{||} r : \ov{\formula}\cto\judgement ; \ov{f = \rulebindspec} &                                \\
        \formula      & ::=  & \lookup \mid \cbrk{\rulebindspec}~\jmv:\judgement                    & \textit{Formula}               \\
        \lookup       & ::=  & \cbrc{x \cto \ov{\symbolicterm}}                                     & \textit{Lookup}                \\
        \judgement    & ::=  & R~\ov{\symbolicterm}                                                 & \textit{Judgement}             \\
        \rulebindspec & ::=  & \ov{\rbsi}                                                           & \textit{Rule binding spec.}    \\
        \rbsi         & ::=  & b \cto \ov{\symbolicterm} \mid f~\jmv                                & \textit{Rule bind. spec. item} \\
      \end{array}
    \]
  \end{minipage}
}
\end{center}
\caption{Syntax for relations}
\label{fig:grammarrelations}
\end{figure}

Figure \ref{fig:grammarrelations} shows the grammar for specification of
relations. A relation declaration $\reldecl$ introduces a new relation $R$ with
an optional environment index $E$ and indices $\ov{S}$. For the purpose of variable
binding, we regard the first sort index to be classified by the remaining ones. The
environment $E$ itself is left implicit in the rules; only environment changes
are explicitly stated. Each $\reldecl$ contains a list of named rules $r$ of
which there are two kinds. Regular rules
$\texttt{||} r : \ov{\formula}\cto\judgement; \ov{f = \rulebindspec}$ contain a
list of formulas as premises and conclude in a judgement which is simply a
relation between symbolic expressions. We also allow the definition of function
counterparts at the level of relations, but instead of having a separate
declaration form, we declare them inline with relations.

A formula is either a variable lookup in the environment, that gives
access to the associated data, or a judgement that can be named with judgement
variables. Similar to binding specification of sort fields, judgements are
prefixed with rule binding specifications $\rulebindspec$ that alter the
implicit environment. These consist of a list of items: either
singleton binding variables mapped to associated data $\ov{\symbolicterm}$ or
function calls $(f~\jmv)$ on judgements. The second kind of rules are variable
rules $\texttt{+} r : \lookup\cto\judgement$ that only contain a single lookup
as a premise.

Note that allowing lookups in regular rules is a departure from our
free-monadic view on syntax. Furthermore, we do not require that variable rules
are declared for each environment clause. The reason is that relations that do
not fit into this view are quite common, e.g. most algorithmic type systems
require renormalization during substitution. Hence, we provide support for these
relations and leave proof obligations for the user in order to generate
substitution lemmas. Each regular rule that makes use of lookups gives rise to
an obligation. If there is no explicit variable rule for an environment clause,
the corresponding derived rule needs to be proven.

%format relation = "{\relation}"

\begin{figure}[t]
\fbox{
\begin{minipage}{0.99\columnwidth}
\begin{tabular}{l@@{\hspace{2mm}}c@@{\hspace{1mm}}l}
\multicolumn{3}{l}{|relation [Env] Typing Tm Ty|~\cass}                                                        \\
 & \texttt{+}  & |Tvar :  {x -> T} -> Typing (var x) T|                                                        \\
 & \texttt{||} & |Tabs :  [x -> T1] Typing t (weaken T2 x) -> Typing (abs x T1 t) (tarr T1 T2)|                \\
 & \texttt{||} & |Tapp :  Typing t1 (tarr T11 T12) -> Typing t2 T11 -> Typing (app t1 t2) T12|                 \\
 & \texttt{||} & |Ttabs : [X -> ] Typing t T -> Typing (tabs X t) (tall X T)|                                  \\
 & \texttt{||} & |Ttapp : Typing t1 (tall X T12) -> Typing (tapp t1 T2) (subst X T2 T12)|                      \\
 & \texttt{||} & |Tpack : Typing t2 (subst X U T2) -> Typing (pack U t2 (texist X T2)) (texist X T2)|          \\
 & \texttt{||} & |Tunpack : Typing t1 (texist X T12) ->|                                                       \\
 &             & \quad |[X -> , x -> T12] Typing t2 (weaken T2 [X,x]) -> Typing (unpack t1 X x t2) T2|         \\
 & \texttt{||} & |Tpair : Typing t1 T1 -> Typing t2 T2 -> Typing (prod t1 t2) (tprod T1 T2)|                   \\
 & \texttt{||} & |Tcase : Typing t1 T1 -> (wtp: PTyping p T1) ->|                                              \\
 &             & \quad |[bind wtp] Typing t2 (weaken T2 (bind p)) -> Typing (case t1 p t2) T2|                 \\
\multicolumn{3}{l}{|relation [Env] PTyping Pat Ty|~\cass}                                                      \\
 & \texttt{||} & |Pvar : PTyping (pvar x T) T ; bind = x -> T|                                                 \\
 & \texttt{||} & |Pprod : (wtp1: PTyping (pvar x T1) T1) ->|                                                   \\
 &             & \quad  |(wtp2: [bind wtp1] PTyping p2 (weaken T2 (bind p1))) ->|                              \\
 &             & \quad |PTyping (ppair p1 p2) (tprod T1 T2) ;|                                                 \\
 &             & \qquad |bind = bind wtp1, bind wtp2|                                                          \\
\end{tabular}
\end{minipage}
}
\caption{Typing relation for $\fexistsprod$}
\label{fig:systemfexiststyping}
\end{figure}

\paragraph{Example} Figure \ref{fig:systemfexiststyping} contains the definition
of the typing relation |Typing| for $\fexistsprod$ terms that extends the
specification of Figure \ref{fig:systemfexists}. The relation makes use of the
typing environment |Env| and has two indices: terms |Tm| and types |Ty|.  The
variable rule |Tvar| gets the type of a term variable from the environment. The
regular rule |Tabs| specifies the typing of term abstractions. Here the domain
type |T2| changes scope and needs to be explicitly weakened in the premise. In
contrast, in the rule |Ttabs| the body of the universal quantification is under
a binder in the conclusion and it does not change its scope so no weakening is
performed. The rule for type applications |Ttapp| shows the use of symbolic
substitution in the conclusion and the rule |Tpack| for packing existentials
shows symbolic substitution in the premise. Finally, in the rule |Tunpack| we
need to weaken the type |T2| explicitly with the type variable |X| and the term
variable |x| for the typing judgement of the body |t2|.

%if False
\begin{figure}[t]
\fbox{
\begin{minipage}{0.95\columnwidth}
\begin{code}
relation Value Tm :=
  | V_abs    : Value (abs x T t)
  | V_tabs   : Value (tabs X t)
  | V_pack   : Value t -> Value (pack T1 t T2)

relation Eval Tm Tm :=
  | E_absbeta   :  Value t2 →
                   Eval (app (abs x T11 t12) t2) (subst x t2 t12)
  | E_tabsbeta  :  Eval (tapp (tabs X t11) T2) (subst X T2 t11)
  | E_packbeta  :
      Value v12 →
      Eval (unpack (pack T11 v12 T13) X x t2)
      (subst X T11 (subst x (weaken v12 X) t2))
  | E_app1 :    Eval t1 t1' ->
                Eval (app t1 t2) (app t1' t2)
  | E_app2 :    Eval t2 t2' ->
                Eval (app t1 t2) (app t1 t2')
  | E_tapp :    Eval t t' ->
                Eval (tapp t T) (tapp t' T)
  | E_pack :    Eval t t' ->
                Eval (pack T1 t T2) (pack T1 t' T2)
  | E_unpack :  Eval t1 t1' ->
                Eval (unpack t1 X x t2) (unpack t1' X x t2)
\end{code}
\end{minipage}
}
\caption{Evaluation relation for $\fexistsprod$}
\label{fig:systemfexiststyping}
\end{figure}
%endif


%-------------------------------------------------------------------------------

\subsection{Relation Well-formedness}\label{ssec:relationwf}

\begin{figure}[t]
  \begin{center}
\small
\fbox{
  \begin{minipage}{0.99\columnwidth}
  \[\begin{array}{l@@{\hspace{.4cm}}l@@{\hspace{1.2cm}}l@@{\hspace{.4cm}}l}
      E_{?}  ::= E \mid \bullet & \text{Optional Env.} &
      \RENV ::= \ov{R : E_{?} \times \ov{S}} & \text{Relation meta-env.} \\
    \end{array}
  \]
  \vspace{-7mm}
  \framebox{\mbox{$\vdash \reldecl$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{WfRelEnv}]
       {\ov{\wfruledecl{E}{R}{\ov{S}}{\ruledecl}}
       }
       {\vdash \relation~[E]~R~\ov{S} := \ov{\ruledecl}
       } \\ \\
     \inferrule* [right=\textsc{WfRelNoEnv}]
       {\ov{\wfruledecl{\bullet}{R}{\ov{S}}{\ruledecl}}
       }
       {\vdash \relation~R~\ov{S} := \ov{\ruledecl}
       }
    \end{array}
  \]

  \framebox{\mbox{$\wfruledecl{E_{?}}{R}{\ov{S}}{\ruledecl}$}} \\
  \[ \quad
     \begin{array}{c}
       \inferrule* [right=\textsc{RuleVar}]
         {%% \LENV = (x@@\alpha), \ov{[\epsilon]t : T} \\
           K : \alpha \to S \and
          (K' : \alpha \cto \ov{T} : R) \in E
         }
         { \wfruledecl{E}{R}{(S,\ov{T})}{\texttt{+} r : \{g \mapsto \ov{t}\} \to R~(K~g)~\ov{t}}
         } \\ \\
       \inferrule* [right=\textsc{RuleReg}]
         { \ov{\wfformula{E_{?}}{\formula}} \and
           \ov{\wfsym{\epsilon}{\symbolicterm}{S}}
%if showFun
           \\
           \ov{\LENV \vdash_{E_{?}} \rulebindspec \Downarrow \bindspec}
%endif
         }
         { \wfruledecl{E_{?}}{R}{\ov{S}}{\texttt{||} r : \ov{\formula} \to R~\ov{\symbolicterm}} %% ; \ov{f = \rulebindspec}
         }
     \end{array}
  \]

  \framebox{\mbox{$\wfformula{E_{?}}{\formula}$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{FmlJmt}]
        { (R : E_{?} \times \ov{T}) \in \RENV \vee (R : \bullet \times \ov{T}) \in \RENV \and
          \LENV \vdash_{E_{?}} \rulebindspec \Downarrow \bindspec \\\\
          ([\bindspec]\jmv:R~\ov{\symbolicterm}) \in \LENV \and
          \ov{\wfsym{\bindspec}{\symbolicterm}{T}}
        }
        { \wfformula{E_{?}}{[\rulebindspec] \jmv: R~\ov{\symbolicterm}}
        } \\\\
     \inferrule* [right=\textsc{FmlLookup}]
        { (K' : \alpha \cto \ov{T}) \in E  \and
          (g@@\alpha) \in \LENV \and
          \ov{\wfsym{\epsilon}{\symbolicterm}{T}}
        }
        { \wfformula{E}{\{g \mapsto \ov{\symbolicterm}\}}
        }
    \end{array}
  \]

  \framebox{\mbox{$\LENV \vdash_{E_{?}} \rulebindspec \Downarrow \bindspec$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{RbsNil}]
       {\,}
       {\LENV \vdash_{E_{?}} \epsilon \Downarrow \epsilon
       } \\\\
     \inferrule* [right=\textsc{RbsSng}]
       {\LENV \vdash_{E} \rulebindspec \Downarrow \bindspec \\
        ([\bindspec]b : \beta) \in \LENV \\
        (K' : \beta \cto \ov{T}) \in E  \\
        \ov{\wfsym{\bindspec}{\symbolicterm}{T}}
       }
       {\LENV \vdash_{E} \rulebindspec, b \cto \ov{\symbolicterm} \Downarrow \bindspec,b
       }
%if showFun
       \\\\
     \inferrule* [right=\textsc{RbsCall}]
       {\LENV \vdash_{E} \rulebindspec \Downarrow \bindspec \\
        R : E \times (S,\ov{T}) \in \RENV \\
        ([\bindspec]~\jmv:R~\symbolicterm~\ov{\symbolicterm'}) \in \LENV \\
         f : S \to [\ov{\beta}] \in \Phi \\
        \evalbigf{f}{\symbolicterm}{\bindspec'}
       }
       {\LENV \vdash_{E} \rulebindspec, f~\jmv \Downarrow \bindspec,\bindspec'
       }
%endif
     \end{array}
  \]

  \end{minipage}
}
\end{center}
\caption{Well-formed relations}
\label{fig:wellformedrelspec}
\end{figure}

Finally, we define the well-formedness of relation
specifications. We make use of a global meta-environment $\RENV$ that contains
the environment and sort types of relations. The meta-relation $\vdash \reldecl$
delegates the well-formedness checking of relation declarations
to $\wfruledecl{E_{?}}{R}{\ov{S}}{\ruledecl}$ which checks the individual rules
with respect to the given names $E_{?},R,\ov{S}$. In case of a variable
rule $\textsc{RuleVar}$, the relation needs to have an environment $E$ and the
clause for the namespace $\alpha$ of the free variable $g$ needs to be
substitutable by the relation $R$. The relation of the conclusion is $R$ and the
first index is the variable constructor for namespace $\alpha$ with the lookup
variable. The remaining indices are sort meta-variables and the arity and order
is exactly the data of the lookup. This form ensures that we can always wrap a
lookup of the clause in the variable rule.
%% i.e. it defines a proper unit of the relative monad.

Regular rules are handled by $\textsc{RuleReg}$. Again, the relation of the
judgement in the conclusion is $R$. Each regular rule has a local-environment
$\LENV$ that is inferred. We check the well-formedness of the symbolic
expression in the conclusion against the empty local scope $\epsilon$. This
encodes the assumption that all indices are in the same scope and there is no
binding between them. The definitions of the functions are checked by the
``flattening'' relation
$\LENV \vdash_{E_{?}} \rulebindspec \Downarrow \bindspec$. The output
$\bindspec$ is ignored. An additional (implicit) requirement is that $r$ has a
function definition for each function that is declared on the $R$'s first index
sort.

The well-formedness of the formulas of the premise is delegated to the relation
$\wfformula{E_{?}}{\formula}$. For lookups, the rule \textsc{FmlLookup} checks
that an environment $E$ is given and that the data of the lookup is well-formed
with the sorts of the corresponding clause of $E$. In case of a judgement, we
get the environment and sort types of the judgement's relation $R$ from
$\RENV$. $R$'s environment is either the same as that of the
enclosing relation or $R$ does not have an environment. The rule binding
specification $\rulebindspec$ is flattened to a local scope $\bindspec$ which
has to match the scope declared in $\LENV$. The indices $\ov{\symbolicterm}$ are
checked against $\bindspec$.

Finally, the flattening relation
$\LENV \vdash_{E_{?}} \rulebindspec \Downarrow \bindspec$ calculates the local
scope $\bindspec$ that is induced by a rule binding specification
$\rulebindspec$. The nil case is straightforward. In cases of a non-empty
$\rulebindspec$ we need to have an implicit environment $E$. Rule
\textsc{RbsSng} flattens a singleton rule binding $b \cto \ov{\symbolicterm}$ to
$b$ and checks the symbolic expressions against the prefix $\bindspec$ and the
sort types $\ov{T}$ of the environment clause. A function call $f~j$ is handled
by rule $\textsc{RbsCall}$. Its flattening is symbolic evaluation of $f$ on the
first index $\symbolicterm$.  Also, the local scope $\bindspec$ of $j$ is
checked to be identical to the flattening of the prefix $\rulebindspec$.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
