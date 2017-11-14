%include lhs2TeX.fmt
%include forall.fmt
%include Formatting.fmt

%format namespace = "{\namespace}"
%format sort = "{\sort}"
%format fun = "{\function}"
%format @ = "{\texttt{@}}"
%format case = "\Varid{case}"
%format env = "{\env}"
%format relation = "{\relation}"

%format spec     = "\spec"
%format condecl  = "\condecl"
%format vdashS = "\vdash_{" S "}"

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
\chapter{The \Knot Specification Language}\label{ch:knotsyntax}

This chapter presents \Knot, a language for specifying programming languages.
The language semantics, elaboration of boilerplate and the implementation are
discussed in later chapters. We introduce \Knot by example first in Section
\ref{sec:knotbyexample} and formally in Sections \ref{sec:knotsyntax},
\ref{sec:knot:expressions} and \ref{sec:knot:relations}.
% This makes the \Knot language easier to understand and
% allows us to make our terminology clear.

% We will reiterate through the different parts of a language specification.
Section \ref{sec:knotsyntax} deals with the specification of \emph{abstract
  syntax} of programmning languages and their scoping rules. In Section
\ref{sec:knot:expressions} we look at \emph{symbolic expressions} that are used
in the specification of \emph{inductive relations}. The latter are presented in
Section~\ref{sec:knot:relations}.


%-------------------------------------------------------------------------------
\section{\Knot by Example}\label{sec:knotbyexample}

In this section we showcase \Knot by porting the semi-formal specification of
their \fexistsprod calculus from Chapter \ref{ch:gen:background}. Section \ref{sec:knotbyexample:syntax} discusses the \Knot specification
of the abstract syntax of \fexistsprod and Section
\ref{sec:knotbyexample:semantics} its typing relation.


%-------------------------------------------------------------------------------
\subsection{Abstract Syntax Specifications}\label{sec:knotbyexample:syntax}
%
\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{tabular}{@@{}l@@{\hspace{1.5mm}}c@@{\hspace{0.5mm}}l@@{\hspace{0.5mm}}l@@{\hspace{1.5mm}}c@@{\hspace{0.5mm}}l}
        \multicolumn{3}{@@{}l}{|namespace Tyv : Ty|}              & & &                                                            \\
        \multicolumn{3}{@@{}l}{|namespace Tmv : Tm|}              & & &                                                            \\
         &             &                                     & & &                                                                 \\
        \multicolumn{3}{@@{}l}{\sort~|Ty|~\cass}             & \multicolumn{3}{@@{}l}{|sort Pat|~\cass}                        \\
         & \texttt{+}  & |tvar (X@Tyv)|                      & & \texttt{||} & |pvar (x:Tmv)|                                 \\
         & \texttt{||} & |tarr (T1: Ty) (T2: Ty)|            & & \texttt{||} & |ppair (p1: Pat) (bindspec (bind p1) p2:Pat)|  \\
         & \texttt{||} & |tall (X:Tyv) (bindspec X T: Ty)|   & \multicolumn{3}{@@{}l}{|fun bind : Pat -> [Tmv]|~\cass}        \\
         & \texttt{||} & |tprod (T1: Ty) (T2: Ty)|           & & \texttt{||} & |pvar x      -> x|                             \\
         & \texttt{||} & |texist (X:Tyv) (bindspec X T: Ty)| & & \texttt{||} & |pprod p1 p2 -> bind p1 , bind p2|             \\
        \multicolumn{3}{@@{}l}{|sort Tm|~\cass}                                         & & &                                      \\
         & \texttt{+}  & |var (x@Tmv)|                                                  & & &                                      \\
         & \texttt{||} & |abs (x:Tmv) (T: Ty) (bindspec x t: Tm)|                       & & &                                      \\
         & \texttt{||} & |app (t1: Tm) (t2: Tm)|                                        & & &                                      \\
         & \texttt{||} & |tabs (X:Tyv) (bindspec X t: Tm)|                              & & &                                      \\
         & \texttt{||} & |tapp (t: Tm) (T: Ty)|                                         & & &                                      \\
         & \texttt{||} & \multicolumn{4}{@@{}l}{|pair (t1:Tm) (t2:Tm)|}                                      \\
         & \texttt{||} & \multicolumn{4}{@@{}l}{|case (t1:Tm) (p:Pat) (bindspec (bind p) t2:Tm)|}            \\
         & \texttt{||} & \multicolumn{4}{@@{}l}{|pack (T1: Ty) (t: Tm) (T2: Ty)|}                            \\
         & \texttt{||} & \multicolumn{4}{@@{}l}{|unpack (t1: Tm) (X: Tyv) (x: Tmv) (bindspec (X,x) t2: Tm)|} \\
         &             &                                     & & &                        \\
        \multicolumn{3}{@@{}l}{|env Env|~\cass}                   & & &                   \\
         & \texttt{+}  & |empty|                                  & & &                   \\
         & \texttt{||} & |evar  : Tmv| \cto |Ty : Typing|         & & &                   \\
         & \texttt{||} & |etvar : Tyv| \cto                       & & &                   \\
      \end{tabular}
    \end{minipage}
  }
  \caption{\Knot specification of $\fexistsprod$ (part 1)}
  \label{fig:knot:fexistsprodsyntax}
\end{figure}

Figure \ref{fig:knot:fexistsprodsyntax} contains the \Knot specification of
\fexistsprod's abstract syntax, which corresponds to EBNF grammar
specification in Figure \ref{fig:systemfexistssyntax}.

While it is not apparent in the EBNF grammar in Figure \ref{fig:systemfexistssyntax},
the two sorts for variables and the one for typing contexts have a special
purpose that is related to variable binding. \Knot makes the distinction
between these and the other sorts explicit and uses different declarations
forms to introduce them. Specifically, \Knot distinguishes between
\emph{namespaces}, \emph{(regular syntactic) sorts} and \emph{environments} which
we discuss in turn.


\paragraph{Namespaces}
Figure \ref{fig:knot:fexistsprodsyntax} starts with the declaration of two
namespaces. The line |namespace Tyv : Ty| introduces the namespace |Tyv| (short
for type variables) and declares that it is a namespace for the sort |Ty|, which
represents \fexistsprod types and which is defined elsewhere in the figure. Similarly, we declare
|Tmv| to be a namespace for terms |Tm|.

%% \begin{itemize}
%% \item Most languages are defined using sorts that have either zero or one kind
%%   of variables.
%% \item In \Knot it is possible to associate multiple namespaces with a single sort.
%% \item Therefore it is common practice to not explicitly separate the namespace
%%   from the sort.
%% \end{itemize}


\paragraph{Regular Syntactic Sorts}
Three sorts are introduced next: types |Ty|, terms |Tm| and patterns |Pat| using
an established notation in functional programming for algebraic datatype
declarations. Each sort is defined by a list of constructors of which there are
two kinds: \emph{variable constructors} and \emph{regular constructors}.

Variable constructors are introduced with a plus sign. In the
example, the line \[ \texttt{+} \hspace{0.5mm} |tvar (X@Tyv)| \] declares the
variable constructor |tvar| for types. It holds a single \emph{variable
  reference} of the namespace |Tyv| for type variables.

Regular constructors are declared using the vertical bar and can
have an arbitrary number of fields. The line
\[ \texttt{||} \hspace{0.5mm} |tall (X : Tyv) ([X]T : Ty)| \] declares the
regular constructor |tall|, which represents universally quantified types. All
fields are explicitly named. The first field declaration |(X : Tyv)| introduces
the field (named) |X|, which is a binding for a variable of namespace |Tyv|. The
second field declaration |([X]T : Ty)| introduces the field |T| for a subterm of
sort |Ty|.  It is prefixed by the \emph{binding specification} |[X]| which
stipulates that |X| is brought into scope in the subterm |T|. This is exactly
the essential scoping information that we highlighted in Figure
\ref{fig:systemfexistsscoping}. In contrast to Figure
\ref{fig:systemfexistsscoping} we do not explicitly model (the domain of) the
typing context; all variables that are in scope at the point of the |tall|
constructor are implicitly also in scope in all subterms.

Multiple variables can be brought into scope together. For example, the binding
specification for the body |t2| of the |unpack| constructor brings both the
type variable |X| and the term variable |x| into scope.

\paragraph{Binders}
{ % FEXISTSPROD SCOPE
  \input{src/MacrosFExists}

  The sort |Pat| for patterns is special in the sense that it represents a sort
  of binders. The function |bind| specifies which variables are bound by a
  pattern, similar to the $\bindp{\cdot}$ function in Figure
  \ref{fig:systemfexists:textbook:freevariables}. The function declaration for
  |bind| in Figure \ref{fig:knot:fexistsprodsyntax} consists of a signature and
  a body.  The signature specifies that patterns bind variables of namespace
  |Tmv|, and the body defines |bind| by means of an exhaustive one-level pattern
  match. Functions can be used in binding specifications. The term constructor
  |case| for nested pattern matching uses |bind| to specify that the variables
  bound by the pattern |p| are simultaneously brought into scope in the body
  |t2|.

  The constructor |ppair| also uses |bind| in a binding specification of the
  right component, even though patterns themselves do not contain terms or term
  variable references. However, since |bind| \emph{concatenates} the bound
  variables of |p1| and |p2|, the binding specification denotes that the
  variables of |p2| are considered bound after the variables of |p1|. This is
  used in the scope checking of \Knot specifications which is explained in
  Section \ref{sec:wellformedspec}.
}


\paragraph{Environments}
The last declaration defines typing environments. The plus sign indicates the
base case with constructor |empty|. All other cases associate
information with variables of a namespace. The constructor |evar| declares that
it represents a mapping of term variables |Tmv| to types |Ty|.  It also
states that the term variable clause is substitutable for judgements of the
typing relation |Typing|. We discuss this below where we define |Typing|. The
constructor |etvar| is not associating any information with type variables.


%-------------------------------------------------------------------------------
\subsection{Inductive Relation Specifications}\label{sec:knotbyexample:semantics}
%
%format wtp1
%format wtp2

\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{tabular}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
        \multicolumn{3}{@@{}l}{|relation [Env] Typing Tm Ty|~\cass}                                                        \\
         & \texttt{+}  & |Tvar :  {x -> T} -> Typing (var x) T|                                                        \\
         & \texttt{||} & |Tabs :  [x -> T1] Typing t (weaken T2 x) -> | \\
         &             & \quad |Typing (abs x T1 t) (tarr T1 T2)|                \\
         & \texttt{||} & |Tapp :  Typing t1 (tarr T11 T12) -> Typing t2 T11 -> Typing (app t1 t2) T12|                 \\
         & \texttt{||} & |Ttabs : [X -> ] Typing t T -> Typing (tabs X t) (tall X T)|                                  \\
         & \texttt{||} & |Ttapp : Typing t1 (tall X T12) -> Typing (tapp t1 T2) (subst X T2 T12)|                      \\
         & \texttt{||} & |Tpack : Typing t2 (subst X U T2) -> |                                                        \\
         &             & \quad |Typing (pack U t2 (texist X T2)) (texist X T2)|                                        \\
         & \texttt{||} & |Tunpack : Typing t1 (texist X T12) ->|                                                       \\
         &             & \quad |[X -> , x -> T12] Typing t2 (weaken T2 [X,x]) -> | \\
         &             & \quad |Typing (unpack t1 X x t2) T2|         \\
         & \texttt{||} & |Tpair : Typing t1 T1 -> Typing t2 T2 -> Typing (prod t1 t2) (tprod T1 T2)|                   \\
         & \texttt{||} & |Tcase : Typing t1 T1 -> (wtp: PTyping p T1) ->|                                              \\
         &             & \quad |[bind wtp] Typing t2 (weaken T2 (bind p)) -> Typing (case t1 p t2) T2|                 \\
        \multicolumn{3}{l}{|relation [Env] PTyping Pat Ty|~\cass}                                                      \\
         & \texttt{||} & |Pvar : PTyping (pvar x) T ; bind = x -> T|                                                   \\
         & \texttt{||} & |Pprod : (wtp1: PTyping (pvar x) T1) ->|                                                      \\
         &             & \quad  |(wtp2: [bind wtp1] PTyping p2 (weaken T2 (bind p1))) ->|                              \\
         &             & \quad |PTyping (ppair p1 p2) (tprod T1 T2) ;|                                                 \\
         &             & \qquad |bind = bind wtp1, bind wtp2|                                                          \\
      \end{tabular}
    \end{minipage}
  }
  \caption{Typing relation for $\fexistsprod$}
  \label{fig:knot:fexistsprodtyping}
\end{figure}

Figure \ref{fig:knot:fexistsprodtyping} contains the second part of
\Knot~specification for \fexistsprod: the typing relations |Typing| for terms
and |PTyping| for patterns.

The first line of a \emph{relation declaration} fixes the signature of a
relation. For |Typing|, the declaration stipulates that it makes use of the
typing environment |Env| and has two indices: terms |Tm| and types |Ty|. The
remainder of a relation declaration consists of rules. Like for sorts,
the are two kinds of rules for relations: \emph{variable rules} and,
\emph{regular rules}. Both kinds use notation commonly found for generalized
algebraic data-types.

\paragraph{Variable rules}
Similarly to the abstract syntax, the \emph{variable rules} are introduced with
a plus sign. Parameters in braces define lookups, e.g. the parameter |{x -> T}|
of |Tvar| represents a lookup of the term variable |x| in the \emph{implicit
  typing environment}. We require that each variable rule consists of exactly
one lookup which corresponds exactly to the signature of the relation that is
being defined and is consistent with the declaration of the environment.

\paragraph{Regular rules}
The \emph{regular rule} |Tabs| specifies the typing of term abstractions. In
square brackets before a field, we can add \emph{rule binding specifications}
that allow us to change the implicit environment for this field. In this case,
we extend the implicit typing context with a binding for the \textlambda-bound
variable |x|.

{ % FEXISTSPROD SCOPE
  \input{src/MacrosFExists}

  In this rule, the domain type |T2| changes scope. In the semi-formal typing
  relation in Figure \ref{fig:systemfexiststyping:textbook}, the meta-variable
  $\tau$, that corresponds to |T2|, appears in the context $\Gamma, y : \sigma$
  in the premise and in $\Gamma$ in the conclusion. The scope change in the
  semi-formal development is implicit and is only possible because of language
  specific (non-)subordination information, i.e. the term variable $y$ cannot
  appear in the type $\tau$. In \Knot the scope change has to be explicitly
  indicated by weakening |T2| in the premise.  Similarly, in the semi-formal
  development, the subordination information is insufficient for $\sigma$ in the
  \textsc{TUnpack} rule. The rule uses the additional side-condition
  $\alpha \notin \fv{\sigma}$ to allow $\sigma$ to be well-scoped in both
  $\Gamma, \alpha, x : \tau$ and $\Gamma$. In the \Knot specification, the |T2|
  is explicitly weakened by the type variable |X|, which corresponding to
  $\alpha$, and the term variable |x|.  In contrast, in the rule |Ttabs| the
  body of the universal quantification is under a binder in the conclusion and
  it does not change its scope so no weakening is performed.
}

The rule for type applications |Ttapp| shows the use of symbolic substitution
|(subst X T2 T12)| in the conclusion and the rule |Tpack| for packing
existentials shows symbolic substitution in the premise. Finally, in the rule
|Tunpack| we need to weaken the type |T2| explicitly with the type variable |X|
and the term variable |x| for the typing judgement of the body |t2|.

\paragraph{Relation outputs}
The typing of patterns can be similarly translated from the semi-formal
specification in Section \ref{sec:gen:semiformal:semantics}. The additional
concern is the definition of the relation output that defines the typing context
extension for the variables bound by the pattern, or more precisely defined to
be bound by the |bind| function on patterns.  In Figure
\ref{fig:knot:fexistsprodtyping} this output is explicitly referred to by
reusing the function name |bind|. After each rule, we include a clause that
defines |bind| for this rule. For this purpose, we also allow naming the fields
of rules. Calling |bind| on a field gives access to its output.





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
\section{Key Design Choices}\label{sec:knotdesign}

This section discusses concepts, that influenced the design of \Knot, which
makes it easier to understand the specification of \Knot in the next section and
motivate some of the made choices. \Knot has two different kinds of
meta-variables. The intuition behind them and their treatment are discussed in
Section \ref{ssec:knotdesign:localglobal}. Sections
\ref{ssec:knotdesign:contextparametricity} and \ref{ssec:knotdesign:freemonad}
explain restrictions that \Knot puts on rules of relations to guarantee that
boilerplate lemmas for them can be automatically generated.

%-------------------------------------------------------------------------------
\subsection{Local and Global Variables}\label{ssec:knotdesign:localglobal}

In the variable rule of \fexistsprod{}
\[ \inferrule* [right=\textsc{TVar}]
      {x : \tau \in \Gamma}
      {\typing{\Gamma}{x}{\tau}} \\\\
\]
the variable $x$ is used as a reference and is bound in the context $\Gamma$.

On the other hand, in the judgement
\[ \typing{\Gamma}{(\lambda y : \tau. y)}{\tau \to \tau}. \] the variable $y$
appears in both, a binding position and a reference position.  The reference use
of $y$ has to refer to the enclosing binding and not to a binding in the context
$\Gamma$.

Following the literature on \emph{locally nameless}~\cite{locallynameless} and
\emph{locally named}~\cite{externalinternalsyntax} representations we call $y$ a
\emph{locally bound} variable (aka locally scoped variables \cite{pitts2015}),
or more concisely a \emph{local variable}, and $x$ a \emph{global} or \emph{free
  variable}.

The distinction between local and global variables goes back to at least
Frege~\cite{begriffsschrift} and representations such as locally nameless and
locally named have internalized this distinction. These concepts do not commit
us to a particular representation of variable binding, such as a locally
nameless representation. Rather, these notions arise naturally in
meta-languages.

Frege characterizes global variables as variables that can possibly stand for
anything while local variables stand for something very specific. Indeed, the
variable rule is parameterized over the global (meta-)variable which can refer
to any variable in the typing context. As previously mentioned, $y$ can only
possibly refer to the enclosing binder. This distinction is also visible in the
de Bruijn representation: The variable rule is parameterized over an index for
variable $x$. A local reference, however, is always statically determined. For
instance, the index for $y$ in the judgement above is necessarily 0.

The type-substitutions in the rules \textsc{TTApp} for type-application and
\textsc{TPack} for packing existential types operate on local variables
only.
%%\stevennote{TODO}{This is not really a coincidence. Locally substituting a
%%  global variable is not unthinkable but is very particular.  Can this be
%%  expressed in a good way?}
For reasons, that are explained in Section
\ref{ssec:knotdesign:contextparametricity} below, we enforce substitutions in
the definition of relations to only operate on local variables.

We adopt the Barendregt variable convention in \Knot at the meta-level. Two
locally bound meta-variables that have distinct names are considered to
represent distinct object-variables, or, put differently, distinct local
variables cannot be aliased. However, global meta-variables with distinct names
can be aliased, i.e. represent the same object-variable.


%-------------------------------------------------------------------------------
\subsection{Context Parametricity}\label{ssec:knotdesign:contextparametricity}

The variable rule is special in the sense that it is the only rule where a
global variable is used. The variable rule performs a lookup of the type in the
implicit typing context. More generally, \Knot implicitly assumes that any
global variable, independent of an explicit lookup, is bound in the context.  As
a consequence, the use of a global variable inspects the context.

We call a rule \emph{not context parametric}, iff it makes any assumptions about
the context, e.g. through inspection with a global variable. The variable rule
of \fexistsprod's typing relation is the only not context parametric rule. The
other rules either pass the context through unchanged to the premises, or pass
an extended context to the premises without inspecting the prefix. We call these
rules \emph{context parametric}.

Context parametricity is important for the automatic derivation of boilerplate.
For instance, for the semi-formal substitution lemma of \fexistsprod's typing
relation in Section \ref{sec:gen:semiformal:metatheory}, the inductive step of
each regular rule consists of applying the same rule again modulo commutation of
substitutions. Independent of the language at hand, this is automatically
possible for any context parametric rule.

To understand this, not that in the proof, the substitution is in fact a
substitution of a global variable. Hence, it represents a context change. Since
context parametric rules do not make assumptions about the context, they are
naturally compatible with any changes to the context as long as the change can
be properly reflected in the indices. For this we needed the commutation of two
type substitutions. However, this will always be a substitution of a global
variable which comes from the lemma we are proving, and a local variable from
the definition of the relation. Intuitively, such a commutation is always
possible.


%-------------------------------------------------------------------------------
\subsection{Free Monadic Constructions}\label{ssec:knotdesign:freemonad}

A key principle is the distinction between \emph{locally bound} and \emph{free}
variables at the meta-level. This allows us to recognize \emph{context
parametric} rules which in turn enables us to extend the \emph{free-monadic
view} on syntax \cite{monadic,knotneedle} of \Knot to relations. At the
syntax-level this view requires one distinguished \emph{variable constructor}
per namespace which has a \emph{reference occurrence} as its only argument and
all other constructors only contain \emph{binding occurrences} and subterms.

At the level of relations this translates to one distinguished \emph{variable
  rule} per namespace (or more specifically per environment clause). This
variable rule has a single lookup as its only premise and the sorts of the
environment data match the sorts of the indices of the relation. The variable
rule uses exactly one \emph{free meta-variable}; all other rules only contain
\emph{locally bound} meta-variables and do not feature lookup premises.  In
other words, the variable rule is the only not context parametric rule.

These restrictions allow us to generically establish the substitution lemmas
for relations. Consider the small proof tree on the left:
% , where $A$ is the subtree for the typing judgement of $e_1$.

The distinction between variable and regular constructors follows
straightforwardly from \Knot's free-monad-like view on syntax.  This rules out
languages for normal forms, but as they require custom behavior
(renormalization) during substitution \cite{anormalform,clf} their substitution
boilerplate cannot be defined generically anyway.

%-------------------------------------------------------------------------------
\section{\Knot~Syntax}\label{sec:knotsyntax}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \textbf{Labels}\vspace{-1mm}
      \[ \begin{array}{l@@{\hspace{3mm}}r@@{\hspace{15mm}}l@@{\hspace{3mm}}r}
           \alpha, \beta, \gamma & \textit{Namespace label}       & s, t                  & \textit{Sort meta-variable}\\
           b                     & \textit{Binding meta-variable} & f                     & \textit{Function label}    \\
           g                     & \textit{Global meta-variable}  & E                     & \textit{Env label}         \\
           S, T                  & \textit{Sort label}            & R                     & \textit{Relation label}    \\
           K                     & \textit{Constructor label}     & r                     & \textit{Rule label}        \\
         \end{array}
      \]
      \textbf{Declarations and definitions}
      \[ \begin{array}{@@{}l@@{\hspace{2mm}}c@@{\hspace{3mm}}l@@{\hspace{5mm}}r}
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
           %            & ::=  & \alpha \cto \ov{S}                                                               &                          \\
         \end{array}
    \]
    \end{minipage}
  }
  \caption{The Syntax of \Knot}
  \label{fig:SpecificationLanguage}
\end{figure}

Figure \ref{fig:SpecificationLanguage} shows the grammar of \Knot.  A \Knot
language specification $\spec$ consists of variable namespace declarations
$\namedecl$, syntactic sort declarations $\sortdecl$, function declarations
$\fundecl$, environment declarations $\envdecl$ and relation declarations
$\reldecl$. We defer explaining relation declarations until Section
\ref{sec:knot:relations}.

A namespace declaration $\namespace~\alpha : S$ introduces the namespace
$\alpha$ and associates it with the syntactic sort $S$. This expresses that
variables of namespace $\alpha$ can be substituted for terms of sort $S$. While
most languages feature at most one namespace per sort, it is nevertheless
possible to associate multiple namespaces with a single sort. This can be used,
e.g., in languages with linear type systems to distinguish linearly bound from
unrestricted variables.

A declaration of sort $S$ comes with two kinds of constructor declarations
$\condecl$. Variable constructors $\texttt{+} K\,\fieldref{|g|}{\alpha}$ hold a
variable reference $g$ in the namespace $\alpha$. These are the only
constructors where variables are used as references. The global variable
reference $g$ signifies that the reference is free when considering a variable
constructor in isolation. In larger symbolic expressions, also binding variables
may appear in variable constructors.

Regular constructors $K\,\ov{(b : \alpha)}\,\ov{(s : S)}$ contain named variable
bindings $\ov{(b : \alpha)}$ and named subterms $\ov{(s : S)}$. For the sake of
presentation we assume that the variable bindings precede subterms.

Every subterm $s$ is preceded by a binding specification $\bindspec$ that
stipulates which variable bindings are brought in scope of $s$. The binding
specification consists of a list of items $\bsi$. An item is either a singleton
variable binding $b$ of the constructor or the invocation of a function $f$,
that computes which variables in siblings or the same subterm are brought in
scope of $s$. Functions serve in particular to specify multi-binders in binding
specifications. In regular programming languages the binding specifications of
most subterms are empty; to avoid clutter we omit empty binding specifications
$\cbrk{}$ in the concrete syntax of \Knot.

Functions are defined by function declarations $\fundecl$. The type signature
$f : S \rightarrow [\ov{\alpha}]$ denotes that function $f$ operates on terms of
sort $S$ and yields variables in namespaces $\ov{\alpha}$. The function itself
is defined by exhaustive case analysis on a term of sort $S$.  A crucial
requirement is that functions cannot be defined for sorts that have variables.
Otherwise it would be possible to change the set of variables that a pattern
binds with a substitution. The specification of the output type $\ov{\alpha}$ is
used by \Needle to derive \emph{subordination-based strengthening}
lemmas~\cite{knotneedle}. For simplicity we ignore the output type of functions
and any other subordination related information in the remainder of this thesis.
% However, these lemmas are not necessary to derive the semantics boilerplate.

Environments $E$ represent a mapping from variables in scope to additional data
such as typing information. To this end, an environment declaration $\envdecl$
consists of named clauses $K : (\alpha \cto \ov{S} : R)$ that stipulate that
variables in namespace $\alpha$ are mapped to terms of sorts
$\ov{S}$. Additionally, we specify that this clause can be substituted for
judgement of relation $R$. If the relation $R$ is omitted, then it defaults to
well-scopedness of the data. We elaborate on this, together with the syntax of
inductive relations, in Section \ref{sec:knot:relations}.


%-------------------------------------------------------------------------------
\subsection{Well-Formed \Knot~Specifications}\label{sec:wellformedspec}
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
technical appendix for the extended formalization.

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
\ref{appendix:specification}. In short: For calling a function
$(f : T \to \ov{\alpha})$ on a field $([\bindspec]t : T)$, we require
$\wfbindspec{\bindspec}{f~t}{\ov{\alpha}}$, i.e. the local scope of the function
call is the binding specification of $s$. However, this is very restrictive in
general since it rules out scoping constructs such as recursive scoping.  We
come back to this issue in the concluding discussion of this chapter in Section
\ref{sec:gen:spec:discussion}.




%if False
\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.96\columnwidth}
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

\section{Symbolic Expressions}\label{sec:knot:expressions}

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
last expression former is a reified weakening
$(\symbolicweaken~\symbolicterm~\bindspec)$ that makes context changes
explicit. For example consider $\eta$-reduction for $\fexistsprod$:
$$|abs x T (app (weaken t x) (var x))| \longrightarrow_\eta |t|.$$
Here the term $t$ is assumed to be in the outer context of the whole expression
and is explicitly weakened under the abstraction. The symbolic weakening implies
and replaces freshness conditions. We discuss larger examples of symbolic
expressions after introducing inductive relations in Section
\ref{sec:knot:relations}.


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


%% \paragraph{Symbolic Evaluation} Figure \ref{fig:symbolicevaluation} (middle)
%% contains definitions for the symbolic evaluation as a big-step operational
%% semantics. The relation $\evalbig{\symbolicenv}{\bindspec_1}{\bindspec_2}$
%% defines the evaluation of the binding specification $\bindspec_1$ with respect
%% to environment $\symbolicenv$.
%%
%% Rule \textsc{EvalNil} handles the empty case and rule \textsc{EvalSng} the
%% singleton case in which we simply use the new name of the binding variable and
%% evaluate recursively.
%%
%% The case of a function call is delegated to the relation
%% $\evalbigf{f}{\symbolicterm}{\bindspec}$ that explains the evaluation of the
%% function $f$ on the expression $\symbolicterm$. The straightforward case of a
%% meta-variable is handled by \textsc{EvalCallVar}. Rule \textsc{EvalCallCon}
%% handles expressions built by a regular constructor. It builds up an environment
%% $\symbolicenv$ that maps the left-hand side |(overline x) (overline s)| of the
%% function clause to the fields of the symbolic construction and evaluates the
%% right-hand side of the clause.
%%
%% Notably absent from the symbolic evaluation are rules for reified
%% substitutions and reified weakenings. The de Bruijn representation admits for
%% example the rule
%% $$
%% \inferrule* []
%%  { \evalbigf{f}{\symbolicterm_2}{\bindspec'}
%%  }
%%  { \evalbigf{f}{\symbolicsubst~x~\symbolicterm_1~\symbolicterm_2}{\bindspec'}
%%  }.
%% $$
%% Yet, adding this rule would break subject reduction of symbolic evaluation. The
%% reason is that the typing of $\bindspec$ in Figure \ref{fig:symbolicevaluation}
%% (bottom) is not strong enough to keep track of the scope when performing
%% substitutions or weakenings. In essence, the result cannot be $\bindspec'$ but
%% has to be ``$\bindspec'$ without $x$''. Tracking scopes during substitutions or
%% other user-defined functions is the focus of research on \emph{binding safe
%%   programming}~\cite{freshlook,romeo}. In the framework of \cite{freshlook},
%% $\bindspec'$ in the premise and conclusion of the above rule are two distinct
%% (chains of) weak links with distinct types, which are in a commutative
%% relationship with the world inclusion induced by the substitution.
%%
%% We side-step the issue by sticking to the simple scope checking of Figure
%% \ref{fig:symbolicevaluation} (bottom) and effectively disallow symbolic
%% substitutions and weakenings to appear in positions that are accessed by
%% functions. Another consequence is that substitution and weakening are only
%% allowed ``at the end of the context''. These restrictions are usually met by
%% relations for typing and operational semantics, and thus do not get in the
%% way of type-safety proofs. However, it may be too restrictive for other kinds
%% of meta-theoretical formalizations.


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

\section{Inductive Relations}\label{sec:knot:relations}

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


\section{Discussion}\label{sec:gen:spec:discussion}

\paragraph{Recursive Scoping}
{ \input{src/MacrosFExists}

  The first version of the framework, as presented in the first article above,
  uses a more lenient well-formedness relation for binding specifications than the
  one presented in Figure \ref{fig:wellformedspec}. This alternative version also
  allowed for recursive scoping to be specified. Recursive scoping as implemented
  in the article, uses cyclic binding specifications which
  Figure~\ref{fig:wellformedspec} rules out. This is a trade-off between
  expressivity and simplicity.

  To illustrate this, consider a hypothetical typing judgement for a mutual
  recursive declarations list $ds$ that binds $\Delta$ variables with their
  types. The well-scopedness lemma for terms of such a language require us to
  proof the following derivation:

  \[ \inferrule* []
       {\decltyping{\Gamma,\Delta}{ds}{\Delta}}
       {\wellscoped{\Gamma,\Delta}{ds} \wedge
        \wellscoped{\Gamma}{\Delta}
       }
   \]

   \noindent However, the well-scopedness hypothesis only gives us
   $\wellscoped{\Gamma,\Delta}{\Delta}$. The usual step is to argue that
   $\Delta$ only has term variable bindings and terms do not appear in typing
   contexts or in types. Therefore, we can use subordination based strengthening
   to get $\wellscoped{\Gamma,\Delta}{\Delta}$. \Knot provides enough information to
   allow \Needle to derive such lemmas. However, the cyclicity of such
   specifications adds unnecessary complexity to the checking and elaboration of
   symbolic expressions. Furthermore, this approach does not scale to richer
   type theories that allow inductive-recursive or inductive-inductive
   declarations, for which the subordination used above is not valid.

   Instead of pushing the shortcut over subordination information, we plan to
   solve the problem in a more principled manner in future work by allowing
   multiple (potentially circular, but not cyclic) input scopes. Recursive
   constructs can then be checked with two scopes: one for declaration heads and
   one for declaration bodies.
}


% -------------------------------------------------------------------------------
\paragraph{Symbolic Substitution}

Checking the scopes of expressions for language that define scoping functions,
requires such functions to be symbolically evaluated on expressions. These
definitions can be found in the technical appendix \ref{appendix:specification}.

Notably absent from the symbolic evaluation are rules for symbolic substitutions
and weakenings. The de Bruijn representation admits for example the rule
$$
\inferrule* []
 { \evalbigf{f}{\symbolicterm_2}{\bindspec'}
 }
 { \evalbigf{f}{\symbolicsubst~x~\symbolicterm_1~\symbolicterm_2}{\bindspec'}
 }.
$$
Yet, adding this rule would break subject reduction of symbolic evaluation. The
reason is that the typing of $\bindspec$ in Figure \ref{fig:symbolicevaluation}
(bottom) is not strong enough to keep track of the scope when performing
substitutions or weakenings. In essence, the result cannot be $\bindspec'$ but
has to be ``$\bindspec'$ without $x$''. Tracking scopes during substitutions or
other user-defined functions is the focus of research on \emph{binding safe
  programming}~\cite{freshlook,romeo}. In the framework of \cite{freshlook},
$\bindspec'$ in the premise and conclusion of the above rule are two distinct
(chains of) weak links with distinct types, which are in a commutative
relationship with the world inclusion induced by the substitution.

We side-step the issue by sticking to the simple scope checking of Figure
\ref{fig:symbolicevaluation} (bottom) and effectively disallow symbolic
substitutions and weakenings to appear in positions that are accessed by
functions. Another consequence is that substitution and weakening are only
allowed ``at the end of the context''. These restrictions are usually met by
relations for typing and operational semantics, and thus do not get in the way
of type-safety proofs. However, in general this too restrictive. In future work
we would like to extend the scope checking to correctly handle substitutions in
the middle of the context and also introduce first-class substitutions and
develop the scope checking for them.

%%\stevennote{TODO}{Find and reference
%%  Belugas equational theory for (fist-class) substitutions.}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
