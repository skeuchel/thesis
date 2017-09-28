%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt
%include exists.fmt

{ % FEXISTSPROD SCOPE

\newcommand{\pack}[3]{\{{#1},{#2}\}~\text{as}~{#3}}
\newcommand{\unpack}[4]{\text{let}~\{{#1},{#2}\}={#3}~\text{in}~{#4}}
\newcommand{\casep}[3]{\text{case}~{#1}~\text{of}~{#2}\to{#3}}
%\newcommand{\typing}[3]{{#1} \vdash_\text{tm} {#2} : {#3}}
\newcommand{\wellscoped}[2]{{#1} \vdash {#2}}
\newcommand{\wellscopedterm}[2]{{#1} \vdash_\text{tm} {#2}}
\newcommand{\kinding}[2]{{#1} \vdash_\text{ty} {#2}}
\newcommand{\ptyping}[4]{{#1} \vdash_\text{p} {#2} : {#3} ; {#4}}
\newcommand{\pmatch}[4]{\text{Match}~{#1}~{#2}~{#3}~{#4}}
\newcommand{\step}[2]{{#1} \longrightarrow {#2}}
\newcommand{\osubst}[3]{{[{#1}\mapsto{#2}]~{#3}}}
\newcommand{\fv}[1]{{\text{fv}({#1})}}
\newcommand{\bindp}[1]{{\text{bnd}({#1})}}
\newcommand{\tapp}[2]{{#1}!{#2}}

%% \section{Overview}\label{sec:overview}

This chapter illustrates the boilerplate that arises when mechanizing
type-safety proofs, outlines our specific approach and defines necessary
terminology. Our running example is \fexistsprod{}, i.e. \SystemF with universal
and existential quantification, and products. In the following, we elaborate on
the development and point out which definitions and proofs can be considered
\emph{variable binding boilerplate} and which are \emph{essential}. The kind of
boilerplate that arises, is coarsely determined by the semantics, the
meta-theoretic property that is being proved and the approach to proving it. We
use the syntactic approach of \citet{progresspreservation} to prove type-safety
via progress and preservation of small-step operational semantics and
specifically focus on the boilerplate of such proofs.

For the illustration in this chapter, we proceed in three steps. First, we
present a textbook-like definition of \fexistsprod{}. This definition is not
completely formal, and hence cannot be used directly in mechanizations. It is,
however, formal enough to be accepted in scientific publications. We call it
\emph{semi-formal}. Using this semi-formal definition we discuss arising
boilerplate independent of later choices, e.g. syntax representations. Second,
we formalize the previous semi-formal definition by bringing it into a shape
that is suitable for mechanization. Third, we discuss the mechanization itself.



\section{Semi-formal Development}\label{sec:gen:spec}

This section presents the semi-formal development of the language \fexistsprod{},
with an emphasis on variable
binding related concerns. Section
\ref{sec:gen:semiformal:syntax} presents the syntax of \fexistsprod{} and
elaborates on needed variable binding boilerplate. Subsequently, Section
\ref{sec:gen:semiformal:semantics} presents the typing and evaluation relations
and illustrates the boilerplate lemmas they determine. Finally, Section \ref{sec:gen:semiformal:metatheory} shows
where boilerplate is used in the type-safety proof of \fexistsprod{}.

%-------------------------------------------------------------------------------
\subsection{Syntax}\label{sec:gen:semiformal:syntax}
%
\paragraph{Grammar}
\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{tabular}{lcll@@{\hspace{8mm}}lcll}
        $\alpha,\beta$  & ::=    &                                & type variable     \\
        $\tau,\sigma$   & ::=    &                                & type              \\
                        & $\mid$ & $\alpha$                       & type variable     \\
                        & $\mid$ & $\sigma \to \tau$              & function type     \\
                        & $\mid$ & $\forall\alpha.\tau$           & universal type    \\
                        & $\mid$ & $\exists\alpha.\tau$           & existential type  \\
                        & $\mid$ & $\sigma \times \tau$           & product type      \\
        $x,y$           & ::=    &                                & term variable     \\
        $p$             & ::=    &                                & pattern           \\
                        & $\mid$ & $x$                            & variable pattern  \\
                        & $\mid$ & $p_1 , p_2$                    & pair pattern      \\
        $e$             & ::=    &                                & term              \\
                        & $\mid$ & $x$                            & term variable     \\
                        & $\mid$ & $\lambda x:\tau.e$             & term abstraction  \\
                        & $\mid$ & $e_1~e_2$                      & application       \\
                        & $\mid$ & $\Lambda\alpha.e$              & type abstraction  \\
                        & $\mid$ & $\tapp{e}{\tau}$               & type application  \\
                        & $\mid$ & $\pack{\sigma}{e}{\tau}$       & packing           \\
                        & $\mid$ & $\unpack{\alpha}{x}{e_1}{e_2}$ & unpacking         \\
                        & $\mid$ & $e_1,e_2$                      & pair              \\
                        & $\mid$ & $\casep{e_1}{p}{e_2}$          & pattern binding   \\
        %% $v$             & ::=    &                                & value             \\
        %%                 & $\mid$ & $\lambda x:\tau.e$             & term abstraction  \\
        %%                 & $\mid$ & $\Lambda\alpha.e$              & type abstraction  \\
        %%                 & $\mid$ & $\pack{\sigma}{v}{\tau}$       & existential value \\
        %%                 & $\mid$ & $v_1,v_2$                      & pair value        \\
        $\Gamma,\Delta$ & ::=    &                                & type context      \\
                        & $\mid$ & $\epsilon$                     & empty context     \\
                        & $\mid$ & $\Gamma, \alpha$               & type binding      \\
                        & $\mid$ & $\Gamma, x:\tau$               & term binding      \\
      \end{tabular}
    \end{minipage}
  }
  \caption{\fexistsprod syntax}
  \label{fig:systemfexistssyntax}
\end{figure}
%
Figure \ref{fig:systemfexistssyntax} shows the first part of the language
specification: the definition of the syntax of \fexistsprod, in a textbook-like
manner.

The three main syntactic sorts of \fexistsprod are types, terms and patterns,
and there are auxiliary sorts for values, variables and typing
contexts. Patterns describe \emph{pattern matching} for product types only and
can be arbitrarily nested. A pattern can therefore bind an arbitrary number of
variables at once. For simplicity we keep matching on existentials separate from
products. One level of existentials can be packed via $(\pack{\tau}{e}{\tau})$
and unpacked via $(\unpack{\alpha}{x}{e_1}{e_2})$.

In this grammar the scoping rules are left implicit as is common practice. The
intended rules are that in a universal $(\forall\alpha.\tau)$ and existential
quantification $(\exists\alpha.\tau)$ the type variable $\alpha$ scopes over the
body $\tau$, in a type abstraction $(\Lambda\alpha.e)$ and term abstraction
$(\lambda x:\tau.e)$ the variable $\alpha$ respectively $x$ scopes over the body
$e$. In a pattern binding $(\casep{e_1}{p}{e_2})$ the variables bound by the
pattern $p$ scope over $e_2$ but not $e_1$, and in the unpacking of an
existential $(\unpack{\alpha}{x}{e_1}{e_2})$ the variables $\alpha$ and $x$
scope over $e_2$.


\paragraph{Scoping}
%
\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\kinding{\Gamma}{\tau}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
           \inferrule* [right=\textsc{WsVar}]
             {\alpha \in \Gamma
             }
             {\kinding{\Gamma}{\alpha}} \qquad
           \inferrule* [right=\textsc{WsFun}]
             {\kinding{\Gamma}{\sigma} \\
              \kinding{\Gamma}{\tau}
             }
             {\kinding{\Gamma}{\sigma \to \tau}} \\\\
           \inferrule* [right=\textsc{WsAll}]
             {\kinding{\Gamma\gray{, \alpha}}{\tau}
             }
             {\kinding{\Gamma}{\forall\alpha.\tau}} \quad
           \inferrule* [right=\textsc{WsEx}]
             {\kinding{\Gamma\gray{, \alpha}}{\tau}
             }
             {\kinding{\Gamma}{\exists\alpha.\tau}} \quad
           \inferrule* [right=\textsc{WsProd}]
             {\kinding{\Gamma}{\sigma} \\
              \kinding{\Gamma}{\tau}
             }
             {\kinding{\Gamma}{\sigma \times \tau}}
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Well-scoping of types}
  \label{fig:systemfexistsscoping}
\end{figure}
%
The well-scopedness relation for types $\kinding{\Gamma}{\tau}$ is defined in
Figure \ref{fig:systemfexistsscoping}.  This relation takes a typing context
$\Gamma$ as an index to represent the set of variables that are in scope and an
index $\tau$ for types. It denotes that all type variables in $\tau$ are bound
either in $\tau$ itself or appear in $\Gamma$. The definition is completely
syntax-directed. The interesting rules are the ones for variables and for the
quantifiers. In the variable case, rule \textsc{WsVar} checks that a type
variable indeed appears in the typing context $\Gamma$. In the rules
\textsc{WsAll} for universal and \textsc{WsEx} for existential quantification,
the bound variable is added to the typing context in the premise for the bodies.
Hence, the relation formally and explicitly defines the scoping rules that we
defined in Section \ref{sec:gen:overview:syntax} in prose.

The definition of the well-scoping relation follows a standard recipe and
usually its definition is left out in pen-and-paper specifications. In
mechanizations, however, such a relation usually needs to be defined (unless it
is not used in the meta-theory) by the human prover. Therefore, this relation is
an example of syntax-related boilerplate that we want to derive generically. The
structure of the relation only depends on the syntax of types and their scoping
rules. The EBNF syntax of Figure \ref{fig:systemfexistssyntax} is insufficient
since it does not contain information about scoping. One option is to make the
scoping relation part of the specification and derive other boilerplate from it,
but this relation already repeats a lot of information that is already given in
the EBNF grammar. If possible we want to avoid that repetition in our
specifications. The only new detail that the well-scopedness relation adds
explicitly, is that the type variables in the quantifications scope over the
bodies, which is highlighted in \textgray{gray} in Figure
\ref{fig:systemfexistsscoping}.

These issues ask to develop a new formal and concise way to specify scoping
rules. We come back to this in Section \ref{sec:specification} which presents
our solution to the problem: we develop a language of (abstract) syntax
specifications that include \emph{binding specifications} for scoping.

\paragraph{Free Variables}

\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\fv{\tau}$}} \\
      $\begin{array}{lcl}
        \fv{\alpha}               & = & \{ \alpha \}                    \\
        \fv{\tau_1 \to \tau_2}    & = & \fv{\tau_1} \cup \fv{\tau_2}    \\
        \fv{\forall\beta.\tau}    & = & \fv{\tau} \setminus \{ \beta \} \\
        \fv{\exists\beta.\tau}    & = & \fv{\tau} \setminus \{ \beta \} \\
        \fv{\tau_1 \times \tau_2} & = & \fv{\tau_1} \cup \fv{\tau_2}    \\
      \end{array}$

      \framebox{\mbox{$\bindp{p}$}} \\
      $\begin{array}{lcl}
        \bindp{x}         & = & \{ x \}                      \\
        \bindp{p_1 , p_2} & = & \bindp{p_1} \cup \bindp{p_2} \\
      \end{array}$

      \framebox{\mbox{$\fv{e}$}} \\
      $\begin{array}{lcl}
         \fv{x}                            & = & \{ x \}                                             \\
         \fv{\lambda x:\tau.e}             & = & \fv{e} \setminus \{ x \}                            \\
         \fv{e_1~e_2}                      & = & \fv{e_1} \cup \fv{e_2}                              \\
         \fv{\Lambda\alpha.e}              & = & \fv{e} \setminus \{ \alpha \}                       \\
         \fv{\tapp{e}{\tau}}               & = & \fv{e} \cup \fv{\tau}                               \\
         \fv{\pack{\sigma}{e}{\tau}}       & = & \fv{\sigma} \cup \fv{e} \cup \fv{\tau}              \\
         \fv{\unpack{\alpha}{x}{e_1}{e_2}} & = & \fv{e_1} \cup (\fv{e_2} \setminus  \{ \alpha, x \}) \\
         \fv{e_1,e_2}                      & = & \fv{e_1} \cup \fv{e_2}                              \\
         \fv{\casep{e_1}{p}{e_2}}          & = & \fv{e_1} \cup (\fv{e_2} \setminus \bindp{p})        \\
      \end{array}$
    \end{minipage}
  }
  \caption{Free variables}
  \label{fig:systemfexists:textbook:freevariables}
\end{figure}

Figure \ref{fig:systemfexists:textbook:freevariables} shows the definition
  of the calculations of free variables of types and terms, i.e., reference
  occurrences of variables that are not bound in the type or term itself.
% \item This operation is specific to a nameful syntax representation.
The implementation is a recursive traversal that accumulates free
  variables from variable references upward and removes binding
  occurrences of variables.
For sorts like patterns that represent binders we define an auxiliary
  function $\bindp{\cdot}$ that calculates the set of bound variables.
The definition of the free variable function follows a standard
  recipe, which only depends on the grammar and the scoping rules of the
  syntactic sorts, and is therefore boilerplate.
Free variables are used for the definition of capture-avoiding substitution below.
% and will not be used in the remainder of this thesis.


\paragraph{Substitution}

\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\osubst{\alpha}{\sigma}{\tau}$}} \\
      $\begin{array}{lcll}
           \osubst{\alpha}{\sigma}{\alpha}                 & = & \sigma                                                                     &                                                            \\
           \osubst{\alpha}{\sigma}{\beta}                  & = & \beta                                                                      & (\alpha \neq \beta)                                        \\
           \osubst{\alpha}{\sigma}{(\tau_1 \to \tau_2)}    & = & (\osubst{\alpha}{\sigma}{\tau_1}) \to (\osubst{\alpha}{\sigma}{\tau_2})    &                                                            \\
           \osubst{\alpha}{\sigma}{(\forall\beta.\tau)}    & = & \forall\beta.\osubst{\alpha}{\sigma}{\tau}                                 & (\alpha \neq \beta \wedge \beta \not\in \fv{\sigma}) \\
           \osubst{\alpha}{\sigma}{(\exists\beta.\tau)}    & = & \exists\beta.\osubst{\alpha}{\sigma}{\tau}                                 & (\alpha \neq \beta \wedge \beta \not\in \fv{\sigma}) \\
           \osubst{\alpha}{\sigma}{(\tau_1 \times \tau_2)} & = & (\osubst{\alpha}{\sigma}{\tau_1}) \times (\osubst{\alpha}{\sigma}{\tau_2}) &                                                            \\
      \end{array}$
    \end{minipage}
  }
  \caption{Type in type substitutions}
  \label{fig:systemfexists:textbook:substitution}
\end{figure}

A correct definition of substitution is subtle when it comes to specific
  names of variables. A mere textual replacement is not sufficient. The
  following two examples illustrate situations where we expect a different result than a
  textual replacement:

  \[ \begin{array}{lcl}
       \osubst{\alpha}{\sigma}{(\Lambda\alpha.\alpha)}          & \neq & \Lambda\alpha.\sigma          \\
       \osubst{\alpha}{(\sigma\to\beta)}{(\Lambda\beta.\alpha)} & \neq & \Lambda\beta.(\sigma\to\beta) \\
     \end{array}
   \]

   In the first case, the type variable $\alpha$ is bound in the type we operate
   on and should not have been substituted. In the second case, the type variable $\beta$
   that appears free in the substitute $\sigma \to \beta$ wrongly points to
   the $\beta$ binder after replacement. This is commonly called a
   \emph{variable capture}.

Figure \ref{fig:systemfexists:textbook:substitution} contains a
  definition of a (capture-avoiding) substitution operator that uses
  side-conditions to rule out the two problematic cases above. However, it
  rules out certain inputs and therefore makes the operations partial. This is
  widely accepted in semi-formal pen-and-paper proofs, but a stumbling
  block for mechanization.

The partiality can be addressed by taking into account the intuition that
  the names of bound variables do not matter. For example, for our intended
  semantics the terms $\lambda (x:\tau). x$ and
  $\lambda (y:\tau). y$ are essentially equivalent, i.e. we consider terms that
  are \emph{equal up to consistent renaming of bound variables}. We can apply
  this in the definition of the substitution operators to
  replace bound variables with \emph{fresh} ones, i.e. variables that are not
  used elsewhere.

% \item Terms that are equal up to consistent renaming form an equivalence relation
%   which is called $\alpha$-equivalence. Put differently, we really want to
%   define terms as being the quotient set of $\alpha$-equivalent (raw) terms.
% 
%   This step is easy in a semi-formal setting, but in the proof assistant setting
%   this results in a abundance of proof obligations of preservation of
%   $\alpha$-equivalence.

% \item \sout{It is also called Barendregt's variable convention for its pervasive use
%   in Barendregt's monograph on the lambda calculus \cite{}.}

%-------------------------------------------------------------------------------
\subsection{Semantics}\label{sec:gen:semiformal:semantics}

The next step in the formalization is to develop the typical semantic relations
for the language of study. In the case of \fexistsprod, these comprise a typing
relation for terms, a typing relation for patterns, and a small-step
call-by-value operational semantics.


\paragraph{Typing}

\begin{figure}[t!]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\typing{\Gamma}{e}{\tau}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
         \inferrule* [right=\textsc{TVar}]
           {x : \tau \in \Gamma}
           {\typing{\Gamma}{x}{\tau}} \\\\
         \inferrule* [right=\textsc{TAbs}]
           {\typing{\Gamma,y:\sigma}{e}{\tau}}
           {\typing{\Gamma}{(\lambda y:\sigma. e)}{(\sigma\to\tau)}} \qquad
         \inferrule* [right=\textsc{TTAbs}]
           {\typing{\Gamma,\alpha}{e}{\tau}}
           {\typing{\Gamma}{(\Lambda \alpha. e)}{(\forall\alpha.\tau)}} \\\\
         \inferrule* [right=\textsc{TApp}]
           {\typing{\Gamma}{e_1}{\sigma \to \tau} \\\\
            \typing{\Gamma}{e_2}{\sigma}}
           {\typing{\Gamma}{(e_1~e_2)}{\tau}} \qquad
         \inferrule* [right=\textsc{TTApp}]
           {\typing{\Gamma}{e}{\forall\alpha.\tau}
            %%\gray{\kinding{\Gamma}{\sigma}}
           }
           {\typing{\Gamma}{(\tapp{e}{\sigma})}{([\alpha\mapsto\sigma]\tau)}} \\\\
         \inferrule* [right=\textsc{TPack}]
           {\typing{\Gamma}{e}{([\alpha\mapsto\sigma]\tau)}}
           {\typing{\Gamma}{(\pack{\sigma}{e}{\exists\alpha.\tau})}{(\exists\alpha.\tau)}} \\\\
         \inferrule* [right=\textsc{TPair}]
           {\typing{\Gamma}{e_1}{\tau_1} \\
            \typing{\Gamma}{e_2}{\tau_2}}
           {\typing{\Gamma}{(e_1,e_2)}{(\tau_1 \times \tau_2)}} \\\\
         \inferrule* [right=\textsc{TUnpack}]
           {\typing{\Gamma}{e_1}{\exists\alpha.\tau} \\
            \typing{\Gamma, \alpha, x:\tau}{e_2}{\sigma} \\
            %% \gray{\kinding{\Gamma}{\sigma}}
            \alpha \notin \fv{\sigma}
           }
           {\typing{\Gamma}{(\unpack{\alpha}{x}{e_1}{e_2})}{\sigma}} \\\\
         \inferrule* [right=\textsc{TCase}]
           {\typing{\Gamma}{e_1}{\sigma} \\
            \ptyping{\Gamma}{p}{\sigma}{\Delta} \\
            \typing{\Gamma,\Delta}{e_2}{\tau}}
           {\typing{\Gamma}{(\casep{e_1}{p}{e_2})}{\tau}} \\
         \end{array}
      \]

      \framebox{\mbox{$\ptyping{\Gamma}{p}{\tau}{\Delta}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
         \inferrule* [right=\textsc{PVar}]
           { \; %%\gray{\kinding{\Gamma}{\tau}}
           }
           {\ptyping{\Gamma}{x}{\tau}{(\epsilon, x:\tau)}} \\\\
         \inferrule* [right=\textsc{PPair}]
           {\ptyping{\Gamma}{p_1}{\tau_1}{\Delta_1} \\
            \ptyping{\Gamma,\Delta_1}{p_2}{\tau_2}{\Delta_2}}
           {\ptyping{\Gamma}{(p_1,p_2)}{(\tau_1 \times \tau_2)}{(\Delta_1,\Delta_2)}}
         \end{array}
      \]
    \end{minipage}
  }
  \caption{\fexistsprod typing rules}
  \label{fig:systemfexiststyping:textbook}
\end{figure}

Figure \ref{fig:systemfexiststyping:textbook} contains the rules for the term
and pattern typing relations. The variable rule \textsc{TVar} of the term typing
looks up a term variable $x$ with its associated type $\tau$ in the typing
context $\Gamma$ and rule \textsc{TAbs} deals with abstractions over terms in
terms which adds a binding to the typing context for the premise of the body
$e$. The rules \textsc{TTApp} for type-application and \textsc{TPack} for
packing existential types use a type-substitution operation
$[\alpha\mapsto\sigma]\tau$ that substitutes $\sigma$ for $\alpha$ in
$\tau$. \textsc{TTApp} performs the substitution in the conclusion while
\textsc{TPack} does so in the premise. The remaining two rules, \textsc{TPair}
and \textsc{TCase}, of the term typing relation deal with products. In a case
expression the pattern $p$ needs to have the same type $\sigma$ as the scrutinee
$e_1$ and the variables $\Delta$ bound by $p$ are brought into scope in the body
$e_2$. This environment $\Delta$ is the output of the pattern typing relation
$\ptyping{\Gamma}{p}{\tau}{\Delta}$, which contains the typing information for
all variables bound by $p$. This information is concatenated in the rule
\textsc{PPair} for pair patterns.



\paragraph{Evaluation}

\begin{figure}[t]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\step{e}{e}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
           \inferrule*[]
             {\,}
             {(\lambda x.e_1)~e_2 \longrightarrow [x \mapsto e_2] e_1} \qquad
           \inferrule*[]
             {\,}
             {\tapp{(\Lambda \alpha.e)}{\tau} \longrightarrow [\alpha \mapsto \tau] e} \\\\
           \inferrule*[]
             {\,}
             {\unpack{\alpha}{x}{\pack{\sigma}{e_1}{\tau}}{e_2} \longrightarrow [\alpha\mapsto\sigma][x\mapsto e_1]e_2} \\\\
           \inferrule*[]
             {\pmatch{v}{p}{e_1}{e_2}}
             {\step{(\casep{v}{p}{e_1})}{e_2}}
         \end{array}
       \]

      \framebox{\mbox{$\pmatch{v}{p}{e_1}{e_2}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
           \inferrule*[]
             {\,}
             {\pmatch{v}{x}{e}{([x \mapsto v] e)}
             } \\\\
           \inferrule*[]
             {\pmatch{v_1}{p_1}{e_1}{e_2} \\
              \pmatch{v_2}{p_2}{e_2}{e_3}
             }
             {\pmatch{(v_1,v_2)}{(p_1,p_2)}{e_1}{e_3}
             }
         \end{array}
      \]
    \end{minipage}
  }
  \caption{\fexistsprod evaluation - selected rules}
  \label{fig:systemfexistevaluation:textbook}
\end{figure}

The operational semantics is defined with 4 reduction rules shown in Figure
\ref{fig:systemfexistevaluation:textbook}. We omitted Further congruence rules
that determine the evaluation order. The reduction of the case construct uses an
auxiliary pattern-matching relation $\pmatch{v}{p}{e_1}{e_2}$ which denotes that
when matching the value $v$ against the pattern $p$ and applying the resulting
variable substitution to $e_1$ we get $e_2$ as a result. All of the reduction
rules directly or indirectly use substitutions.



%-------------------------------------------------------------------------------
\subsection{Meta-Theory}\label{sec:gen:semiformal:metatheory}

\paragraph{Substitution}
The interesting steps in the type preservation proof are the preservations under the 4
reduction rules of the operational semantics. These essentially boil down down
to two substitution lemmas:

%% TODO: numbering and references
\[ \begin{array}{c}
     \inferrule*[right=\textsc{SubstTmTm}]
       { %\TODO{$\wellscoped{}{\Gamma}$} \\
         \typing{\Gamma}{e_1}{\sigma} \\
         \typing{\Gamma,x : \sigma,\Delta}{e_2}{\tau}
       }
       { \typing{\Gamma,\Delta}{[x\mapsto e_1]e_2}{\tau}
       } \\\\
     \inferrule*[right=\textsc{SubstTyTm}]
       { %\TODO{$\wellscoped{}{\Gamma}$} \\
         %\kinding{\Gamma}{\sigma} \\
         \typing{\Gamma,\beta,\Delta}{e}{\tau}
       }
       { \typing{\Gamma,[\beta\mapsto\sigma]\Delta}{[\beta\mapsto\sigma]e}{[\beta\mapsto\sigma]\tau}
       } \\
   \end{array}
\]


% \begin{align}
%     \label{lem:substtm}
%     \inferrule*[]
%       {\typing{\Gamma}{e_1}{\sigma} \\
%        \typing{\Gamma,x : \sigma,\Delta}{e_2}{\tau}}
%       {\typing{\Gamma,\Delta}{[x\mapsto e_1]e_2}{\tau}} \\
%     \label{lem:substty}
%     \inferrule*[]
%       {\kinding{\Gamma}{\sigma} \\
%        \typing{\Gamma,\beta,\Delta}{e}{\tau}}
%       {\typing{\Gamma,[\beta\mapsto\sigma]\Delta}{[\beta\mapsto\sigma]e}{[\beta\mapsto\sigma]\tau}}
% \end{align}


For the proofs by induction of these lemmas to go through, we need to prove
them for all suffixes $\Delta$, but only use the special case where
$\Delta = \epsilon$ in the preservation proof. For the inductive step for rule
\textsc{TTApp} of the second substitution lemma we have to prove the following
\[
\inferrule*[]
  {%\kinding{\Gamma}{\sigma} \\
   \Gamma' =  \Gamma,[\beta\mapsto\sigma]\Delta \\
   \typing
    {\Gamma'}
    {[\beta\mapsto\sigma]e}
    {\forall\alpha.[\beta\mapsto\sigma]\tau}
  }
  {\typing
    {\Gamma'}
    {\tapp{([\beta\mapsto\sigma]e)}{([\beta\mapsto\sigma]\sigma')}}
    {\gray{[\beta\mapsto\sigma][\alpha\mapsto\sigma']\tau}}
  }
\]

As the term in the conclusion remains a type application, we want to apply rule
\textsc{TTApp} again. However, the \colorbox{light-gray}{type} in the conclusion
does not have the appropriate form. We first need to commute the two substitutions
with one of the common interaction lemmas
\begin{align*}
  [\beta\mapsto \sigma][\alpha \mapsto \sigma'] =
  [\alpha \mapsto [\beta\mapsto\sigma]\sigma'][\beta\mapsto\sigma] \qquad (\alpha \neq \beta)
  \label{lem:substcomm}
\end{align*}


\paragraph{Progress}
The proof of progress proceeds similarly to that in Section
\ref{sec:intro:typesafety}. 
The main difference, due to the presence of pattern
matching, is that we need to prove an auxiliary lemma stating
that well-typed pattern matching $\pmatch{v}{p}{e_1}{e_2}$ is always defined:
  \[ \inferrule*[]
    {\typing{\epsilon}{v}{\sigma} \\
      \ptyping{\epsilon}{p}{\sigma}{\Delta} \\
      \typing{\Delta}{e_1}{\tau} \\
      \typing{\epsilon}{e_2}{\tau} \\
    }
    {\pmatch{v}{p}{e_1}{e_2}
    }
  \]
On the whole progress does not involve a lot of semantic variable binding
boilerplate.

\paragraph{Preservation}
The proof of preservation proceeds by induction on the typing derivation
$\typing{\Gamma}{e}{\sigma}$ and inversion of the evaluation relation
$\step{e}{e'}$. There are two kinds of cases.
Firstly, for evaluation steps that are congruence rules, the
proof follows immediately by applying the same rule again.
Secondly, for the reduction rules, which all involve substitution, the
proof involves boilerplate substitution lemmas.
Consider the case of reducing a term abstraction
\[ \step{(\lambda (x:\sigma). e_1)~e_2}{\osubst{x}{e_2}{e_1}}. \]

The proof obligation is
\[ \inferrule*[]
     { \typing{\Gamma}{\lambda (x:\sigma).e_1}{\sigma\to\tau} \\
       \typing{\Gamma}{e_2}{\sigma}
     }
     { \typing{\Gamma}{[x\mapsto e_2]e_1}{\tau}
     }
\]
After inverting the first premise
$\typing{\Gamma}{\lambda (x:\sigma).e_1}{\tau}$ to get the typing derivation of $e_1$ we
can apply the boilerplate lemma for well-typed substitutions
\textsc{SubstTmTm}, with $\Delta = \epsilon$, to finish the proof of this
case.

Similarly, the cases of universal and existential quantification follow
directly from the typing substitution lemmas. The case of a pattern match
additionally requires an induction over the matching relation
$\pmatch{v}{p}{e_1}{e_2}$. The boilerplate lemma \textsc{SubstTmTm} is used in
the variable case.



%-------------------------------------------------------------------------------
\section{Formalization}\label{sec:formalization}

The next step is to rework the textbook-like specification from Section
\ref{sec:gen:spec} into a formal one, which can be mechanized in a proof
assistant. In the following, we will replace the syntax representation and
discuss changes to the semantics definitions.


\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \setlength\tabcolsep{2.0mm}
      \begin{tabular}{lclcl lcl}
        $T$ & ::=    & $n$              & $\mid$ & $\forall\bullet.T$ & $E$ & ::=    & $\epsilon$          \\
            & $\mid$ & $T_1 \to T_2$    & $\mid$ & $\exists\bullet.T$ &     & $\mid$ & $\Gamma, \bullet$   \\
            & $\mid$ & $T_1 \times T_2$ & $\mid$ &                    &     & $\mid$ & $\Gamma, \bullet:T$ \\
      \end{tabular}
      \vspace{1mm}
      \hrule
      \vspace{1mm}
      \setlength\tabcolsep{1.5mm}
      \begin{tabular}{lcl lclclcl}
  $q$ & ::=    & $\bullet$ & $t$ & ::=    & $n$                   & $\mid$ & $\Lambda\bullet.t$   & $\mid$ & $t_1,t_2$                             \\
      & $\mid$ & $q_1,q_2$ &     & $\mid$ & $\lambda \bullet:T.t$ & $\mid$ & $\tapp{t}{T}$        & $\mid$ & $\casep{t_1}{q}{t_2}$                  \\
      &        &           &     & $\mid$ & $t_1~t_2$             & $\mid$ & $\pack{T_1}{t}{T_2}$ & $\mid$ & $\unpack{\bullet}{\bullet}{t_1}{t_2}$ \\
       \end{tabular}
    \end{minipage}
  }
  \caption{\fexistsprod de Bruijn representation}
  \label{fig:systemfdebruijn}
\end{figure}

\subsection{Syntax Representation}
The first step in the mechanization is to choose how to concretely represent
variables. Traditionally, one would represent variables using identifiers, but
this requires a massive amount of reasoning modulo $\alpha$-equivalence,
i.e. consistent renaming, which makes it inevitable to choose a different
representation.

Our goal is not to develop a new approach to variable binding nor to compare
existing ones, but rather to scale the generic treatment of a single
approach. For this purpose, we choose de Bruijn representations
\cite{namelessdummies}, motivated by two main reasons. First, reasoning with de
Bruijn representations is well-understood and, in particular, the representation
of pattern binding and scoping rules is also well-understood
\cite{deBruijn,genconv}.  Second, the functions related to variable binding, the
statements of properties of these functions and their proofs have highly regular
structures with respect to the abstract syntax and the scoping rules of the
language. This helps us in treating boilerplate generically and automating
proofs.

Figure \ref{fig:systemfdebruijn} shows a term grammar for a de Bruijn
representation of \fexistsprod.
A property of this representation is that binding occurrences of variables
  still mark the binding but
  do not explictly name the bound variable anymore. For this reason, we replace the variable names
  in binders
  uniformly with a bullet $\bullet$ in the new grammar.

Also, variables do no refer to their binding site by
  name but by using positional information: A variable is represented by a
  natural number $n$ that denotes that the variable is bound by the $n$th
  enclosing binder starting from 0.

  Here are several examples of terms in both the named and the de Bruijn representation:
  \[ \begin{array}{lcl}
       \lambda(x:\tau). x                                                          & \Rightarrow & (\lambda(\bullet:T). 0)                                                              \\
       \lambda(x:\tau). \lambda(y:\sigma). x                                       & \Rightarrow & (\lambda(\bullet:T). \lambda(\bullet:S). 1)                                          \\
       \lambda(x:\tau_1). \lambda(y:\tau_1 \to \tau_2). (\lambda(z:\tau_1). y~x)~x & \Rightarrow \\
         \multicolumn{3}{c}{\lambda(\bullet:T_1). \lambda(\bullet:T_1 \to T_2). (\lambda(\bullet:T_1). 2~0)~1} \\
     \end{array}
  \]

  In the first example, $\lambda(x:\tau). x$, the variable $x$ refers to the immediately enclosing binding
  and can therefore be represented with the index $0$. Next, in
  $\lambda(x:\tau). \lambda(y:\sigma). x$, we need to skip the $y$ binding and therefore
  represent the occurrence of $x$ with 1. In the third example, the variable $x$
  is once represented using the index $1$ and once using the index $2$. This shows that the indices of a variable are not constant but depend
  on the context the variable appears in. 

Finally, we use different namespaces for term and type variables and treat indices
  for variables from distinct namespaces independently, as illustrated by the following examples:

  \[ \begin{array}{lcl}
       \lambda(x:\tau). \Lambda\alpha.  \tapp{x}{\alpha}                  & \Rightarrow & \lambda(\bullet:\tau).\Lambda\bullet. \tapp{0}{0}                     \\
       \Lambda\alpha.   \lambda(x:\tau). \tapp{x}{\alpha}                 & \Rightarrow & \Lambda\bullet.\lambda(\bullet:\tau). \tapp{0}{0}                     \\
       \Lambda\alpha. \Lambda\beta. \lambda(x:\alpha). \lambda(y:\beta).x & \Rightarrow & \Lambda\bullet.\Lambda\bullet.\lambda(\bullet:1).\lambda(\bullet:0).1 \\
     \end{array}
  \]

  As a consequence, when resolving a term variable index we do not take type variable
  binders into account and vice versa.


\subsection{Well-scopedness}
The well-scopedness of de Bruijn terms is a syntactic concern. It is common
practice to define well-scopedness with respect to a \emph{type} context: a term
is well-scoped iff all its free variables are bound in the context. The
context is extended when going under binders. For example, when going under
the binder of a type-annotated lambda abstraction the conventional rule
is:
\[
  \begin{array}{c}
    \inferrule[]
      {|Γ, x : τ ⊢ e|
      }
      {\hsforall |Γ ⊢ λ(x:τ).e|
      } \\
  \end{array}
\]
The rule follows the intention that the term variable should be of the given
type. In this style, well-scopedness comprises a lightweight type system.
However, in general it is impossible to come up with the intended typing or,
more generally, establish what the associated data in the extended context
should be. Furthermore, we allow the user to define different contexts with
potentially incompatible associated data. Hence, instead we define
well-scopedness by using \emph{domains} of contexts. In fact, this is all we
need to establish well-scopedness.

\newcommand{\onetm}{1_{\text{tm}}}
\newcommand{\onety}{1_{\text{ty}}}
\newcommand{\Stm}{S_{\text{tm}}}
\newcommand{\Sty}{S_{\text{ty}}}
%format Itm = "\onetm"
%format Ity = "\onety"
%format Stm = "\Stm"
%format Sty = "\Sty"

In a de Bruijn approach the domain is traditionally represented by a natural number
that denotes the number of bound variables. Instead,
we use \emph{heterogeneous numbers} $h$ -- a refinement of natural numbers --
defined in Figure \ref{fig:wellscopedness:overview} to deal with heterogeneous contexts:
each successor is tagged with a namespace to keep track of the number and order
of variables of different namespaces. This also allows us to model languages
with heterogeneous binders, i.e. that bind variables of different namespaces at
the same time, for which reordering the bindings is undesirable. In the
following, we abbreviate units such as $\onety := \text{S}_{\text{ty}}~0$, use
the obvious extension of addition from natural numbers to heterogeneous numbers and
implicitly use its associativity property. In contrast to naturals, addition is
not commutative. We mirror the convention of extending contexts to the right
at the level of $h$ and will always add new variables on the right-hand side.

Figure \ref{fig:wellscopedness:overview} also defines the calculation $\dom$ of
domains of typing contexts, a well-scopedness predicate $h \vdash_{\text{tm}} n$
for term indices, which corresponds to $n < h$ when only term successors are
counted, and a selection of rules for well-scopedness of terms
$h \vdash_{\text{tm}} t$ and well-scopedness of typing environments
$h \vdash E$.


%format epsilon = "\epsilon"
%format bullet = "\bullet"

\begin{figure}[t]
\begin{center}
  \small
\fbox{
  \begin{minipage}{0.96\columnwidth}
  \begin{tabular}{lcl}
    $h$ & ::= & $0 \mid \Sty~h \mid \Stm~h$
  \end{tabular}

  \begin{tabular}{@@{}ll}
  \begin{minipage}[t]{0.3\columnwidth}
  \begin{code}
  box (dom : E → h)
  \end{code}
  \end{minipage}
  &
  \begin{minipage}[t]{0.3\columnwidth}
  \begin{code}
  dom epsilon         =  0
  dom (E, bullet)     =  dom E + Ity
  dom (E, bullet :T)  =  dom E + Itm
  \end{code}
  \end{minipage}
  \end{tabular}

  \framebox{\mbox{$h \vdash_{\text{tm}} n$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{WsnTmZero}]
                 {\,}
                 {S_{\text{tm}}~h \vdash_{\text{tm}} 0} \\\\
     \inferrule* [right=\textsc{WsnTmTm}]
                 {h \vdash_{\text{tm}} n}
                 {S_{\text{tm}}~h \vdash_{\text{tm}} S~n} \\\\
     \inferrule* [right=\textsc{WsnTmTy}]
                 {h \vdash_{\text{tm}} n
                 }
                 {S_{\text{ty}}~h \vdash_{\text{tm}} n}
     \end{array}
  \]
  \framebox{\mbox{$h \vdash_{\text{tm}} t$}} \\
  \vspace{-7mm}
  \[\begin{array}{c}
      \inferrule*
        [right=\textsc{WsVar}]
        {h \vdash_\text{tm} n
        }
        {h \vdash_\text{tm} n} \\\\
      \inferrule*
        [right=\textsc{WsUnpack}]
        {h \vdash_\text{tm}~t_1 \\
         h + 1_{\text{ty}} + 1_{\text{tm}} \vdash_\text{tm}~t_2
        }
        {h \vdash_\text{tm} (\unpack{\bullet}{\bullet}{t_1}{t_2})} \\
     \end{array}
  \]
  \framebox{\mbox{$h \vdash E$}} \\
  \vspace{-8mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{WseTm}]
                 {h \vdash E \\
                  h + \text{dom}~E \vdash T
                 }
                 {h \vdash E,\bullet:T
                 }
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Well-scopedness of terms (selected rules)}
\label{fig:wellscopedness:overview}
\end{figure}



\subsection{Substitutions}

\newcommand{\shtm}{{\text{sh}_{\text{tm}}}}
\newcommand{\sutm}{{\text{su}_{\text{tm}}}}
\newcommand{\shty}{{\text{sh}_{\text{ty}}}}
\newcommand{\suty}{{\text{su}_{\text{ty}}}}
\newcommand{\SH}{{\text{sh}_{*}}}
\newcommand{\SU}{{\text{su}_{*}}}

%format shtm = "\shtm"
%format sutm = "\sutm"
%format shty = "\shty"
%format suty = "\suty"
%format sh   = "\SH"
%format su   = "\SU"

The operational semantics and typing relations of \fexistsprod require
boilerplate definitions for the de Bruijn representation: substitution of type
variables in types, terms and type contexts, and of term variables in terms. We
also need to define four auxiliary boilerplate \emph{shifting} functions that
adapt indices of free variables when going under binders, or, put differently,
when inserting new variables in the context. We need to generalize shiftings so
that variables can be inserted in the middle of the context, i.e. operations
that corresponds to the weakenings $|Γ,Δ ⊢ e| \leadsto |Γ,x,Δ ⊢ e|$ and
$|Γ,Δ ⊢ e| \leadsto |Γ,α,Δ ⊢ e|$.

Only indices for variables in $\Gamma$ need to be adapted. For this purpose the
shifting functions take a \emph{cutoff} parameter that represents the domain of
$\Delta$. Only indices ``above'' the cutoff are adapted. We overload the name of
type variable shifting and hence use the following four single-place shift
functions:
$$
\begin{array}{c@@{\hspace{1cm}}c}
  |box (shtm : h → t → t)|  &  |box (shty : h → E → E)| \\
  |box (shty : h → t → t)|  &  |box (shty : h → T → T)|
\end{array}
$$

% These can be iterated to get multiplace shiftings that represent the weakenings
% $$
% \Gamma\vdash e       \leadsto \Gamma,\Delta\vdash e        \quad
% \Gamma\vdash \tau    \leadsto \Gamma,\Delta\vdash \tau     \quad
% \Gamma\vdash \Delta' \leadsto \Gamma,\Delta\vdash \Delta'
% $$
% $$
% \begin{array}{c@@{\hspace{5mm}}c@@{\hspace{5mm}}c}
%   |box (sh : t → h → t)| & |box (sh : T → h → T)| & |box (sh : E → h → E)|
% \end{array}
% $$

We use substitution functions which keep the substitute in its original context
and perform (multi-place) shifting when reaching the variable positions. This
behaviour corresponds to the structure of the substitution lemmas
\textsc{SubstTmTm} and \textsc{SubstTyTm}. Hence, the index to be substituted is
represented by the domain of the suffix $\Delta$ to have enough information for
the shifting.
$$
\begin{array}{c@@{\hspace{5mm}}c}
  |box (sutm : h → t → t → t)| &
  |box (suty : h → T → T → T)| \\
  |box (suty : h → T → t → t)| &
  |box (suty : h → T → E → E)|
\end{array}
$$

%% The generic derivation of shifting and substitution and lemmas for the closure
%% of well-scopedness under shifting and substitution are tackled in
%% \cite{knotneedle}.


%if False
\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.95\columnwidth}
  \begin{code}
  box (shtm : h → n → n)

  shtm 0        n      =  S n
  shtm (Stm h)  0      =  0
  shtm (Stm h)  (S n)  =  S (shtm h n)
  shtm (Sty h)  n      =  shtm h n

  box (shtm : h → t → T → n)

  shtm h (tvar n) =  tvar n

  box (shtm : h → t → t → n)

  shtm h (var n)         =  var (shtm h n)
  shtm h (abs T t)       =  abs (shtm h T) (shtm (h + Itm) t)
  shtm h (unpack t1 t2)  =  unpack (shtm h t1) (shtm (h + Ity + Itm) t2)

  box (sutm : h → t → n → n)

  sutm 0        t  0      =  t
  sutm 0        t  0      =  0
  sutm (Stm h)  t  (S n)  =  S (sutm h n)
  sutm (Sty h)  t  n      =  sutm h n

  \end{code}
  \end{minipage}
}
\end{center}
\caption{Well-scopedness of terms}
\label{fig:wellscopedness:overview}
\end{figure}
%endif


\subsection{Semantic Representation}

\begin{figure}[t!]
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\typing{\Gamma}{e}{\tau}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
         \inferrule* [right=\textsc{TVar}]
           {x : \tau \in \Gamma}
           {\typing{\Gamma}{x}{\tau}} \\\\
         \inferrule* [right=\textsc{TAbs}]
           {\gray{\kinding{\Gamma}{\sigma}} \\
            \typing{\Gamma,y:\sigma}{e}{\tau}
           }
           {\typing{\Gamma}{(\lambda y:\sigma. e)}{(\sigma\to\tau)}} \qquad
         \inferrule* [right=\textsc{TTAbs}]
           {\typing{\Gamma,\alpha}{e}{\tau}}
           {\typing{\Gamma}{(\Lambda \alpha. e)}{(\forall\alpha.\tau)}} \\\\
         \inferrule* [right=\textsc{TApp}]
           {\typing{\Gamma}{e_1}{\sigma \to \tau} \\\\
            \typing{\Gamma}{e_2}{\sigma}}
           {\typing{\Gamma}{(e_1~e_2)}{\tau}} \qquad
         \inferrule* [right=\textsc{TTApp}]
           {\typing{\Gamma}{e}{\forall\alpha.\tau} \\
            \gray{\kinding{\Gamma}{\sigma}}
           }
           {\typing{\Gamma}{(\tapp{e}{\sigma})}{([\alpha\mapsto\sigma]\tau)}} \\\\
         \inferrule* [right=\textsc{TPack}]
           {\typing{\Gamma}{e}{([\alpha\mapsto\sigma]\tau)}}
           {\typing{\Gamma}{(\pack{\sigma}{e}{\exists\alpha.\tau})}{(\exists\alpha.\tau)}} \\\\
         \inferrule* [right=\textsc{TPair}]
           {\typing{\Gamma}{e_1}{\tau_1} \\
            \typing{\Gamma}{e_2}{\tau_2}}
           {\typing{\Gamma}{(e_1,e_2)}{(\tau_1 \times \tau_2)}} \\\\
         \inferrule* [right=\textsc{TUnpack}]
           {\typing{\Gamma}{e_1}{\exists\alpha.\tau} \\
            \typing{\Gamma, \alpha, x:\tau}{e_2}{\sigma} \\
            \gray{\kinding{\Gamma}{\sigma}}
           }
           {\typing{\Gamma}{(\unpack{\alpha}{x}{e_1}{e_2})}{\sigma}} \\\\
         \inferrule* [right=\textsc{TCase}]
           {\typing{\Gamma}{e_1}{\sigma} \\
            \ptyping{\Gamma}{p}{\sigma}{\Delta} \\
            \typing{\Gamma,\Delta}{e_2}{\tau}}
           {\typing{\Gamma}{(\casep{e_1}{p}{e_2})}{\tau}} \\
         \end{array}
      \]

      \framebox{\mbox{$\ptyping{\Gamma}{p}{\tau}{\Delta}$}} \\
      \vspace{-6mm}
      \[ \begin{array}{c}
         \inferrule* [right=\textsc{PVar}]
           { \gray{\kinding{\Gamma}{\tau}}
           }
           {\ptyping{\Gamma}{x}{\tau}{(\epsilon, x:\tau)}} \\\\
         \inferrule* [right=\textsc{PPair}]
           {\ptyping{\Gamma}{p_1}{\tau_1}{\Delta_1} \\
            \ptyping{\Gamma,\Delta_1}{p_2}{\tau_2}{\Delta_2}}
           {\ptyping{\Gamma}{(p_1,p_2)}{(\tau_1 \times \tau_2)}{(\Delta_1,\Delta_2)}}
         \end{array}
      \]
    \end{minipage}
  }
  \caption{\fexistsprod typing rules (de Bruijn)}
  \label{fig:gen:overview:formalization:typing}
\end{figure}

The semantic typing relation from Figure \ref{fig:systemfexistssyntax}
translates almost directly to a relation on the de Bruijn representation. One
important aspect that is ignored in Figure~\ref{fig:systemfexistssyntax} is to
ensure that all rule components are well-scoped.  This requires including
additional well-scopedness premises in the rules. For example, the lambda
abstraction rule \textsc{TAbs} needs a well-scopedness premise for the argument
type:
$$
\inferrule*
  [right=\textsc{TAbs}]
  {\typing
    {(E, \bullet:T_1)}
    {t}
    {T_2} \\
   \dom~E \vdash T_1
  }
  {\typing
    {E}
    {(\lambda\bullet:T_1.t)}
    {(T_1 \to T_2)}
  }
$$


\subsection{Meta-Theory}\label{sec:gen:formalization:metatheory}

\paragraph{Scoping}
A concern in the formalisation is that only well-scoped expressions are
considered. This generates many boilerplate obligations to show that all syntactic operations,
like substitution, preserve well-scopedness.
Furthermore, we need to show that all semantic relations imply well-scoping,
  e.g., well-typed terms are also well-scoped:
  \[ \begin{array}{c}
       \inferrule*[right=\textsc{TypingScopeTm}]
         { %\TODO{$\wellscoped{}{\Gamma}$} \\
           \typing{\Gamma}{e}{\tau}
         }
         { \wellscopedterm{\Gamma}{e}
         } \\\\
       \inferrule*[right=\textsc{TypingScopeTy}]
         { %\TODO{$\wellscoped{}{\Gamma}$} \\
           \typing{\Gamma}{e}{\tau}
         }
         { \kinding{\Gamma}{\tau}
         } \\
     \end{array}
   \]



The type-safety proof of \fexistsprod requires additional canonical forms,
typing inversion and boilerplate lemmas.  This paper focuses on the boilerplate
lemmas related to semantic relations. The principal boilerplate lemmas are a
well-scopedness lemma

$$
\inferrule*
  []
  {0 \vdash E \\ \typing{E}{t}{T}
  }
  {\domain{E} \vdash t \wedge \domain{E} \vdash T
  }
$$

\noindent two shifting lemmas
$$
\begin{array}{c}
\inferrule*
  []
  {\typing{E}{t}{T}
  }
  {\typing{E,\bullet:T'}{(\shtm~0~t)}{T}
  }
\quad\quad
\inferrule*
  []
  {\typing{E}{t}{T}
  }
  {\typing{E, \bullet}{(\shty~0~t)}{(\shty~0~T)}
  }
\end{array}
$$

\noindent and two substitution lemmas
$$
\begin{array}{c}
\inferrule*
  []
  {0 \vdash E \\
   \typing{E}{t_1}{T_1} \\
   \typing{E,\bullet:T_1}{t_2}{T_2} \\
  }
  {\typing{E}{(\sutm~0~t_1~t_2)}{T_2} \\
  }
\\\\
\inferrule*
  []
  {0 \vdash E \\
   \domain{E} \vdash T_1 \\
   \typing{E, \bullet}{t_2}{T_2} \\
  }
  {\typing{E}{(\suty~0~T_1~t_2)}{(\suty~0~T_1~T_2)} \\
  }
\end{array}
$$


\section{Mechanization}

\begin{table}[t]\centering
\ra{1.3}
\begin{tabular}{@@{}r r@@{\,}rcr@@{\,}r@@{}}
\toprule
        & \multicolumn{2}{c}{\textbf{Useful}}  &   \phantom{abc}
        & \multicolumn{2}{c}{\textbf{Boilerplate}} \\
\midrule
\textbf{Specification}    & 123 & (13.3\%) &  & 164 & (17.8\%) \\
\textbf{Syntax Theory}    & 0   & (0.0\%)  &  & 365 & (39.6\%) \\
\textbf{Semantics Theory} & 101 & (11.0\%) &  & 187 & (20.3\%) \\ \midrule
\textbf{Total}            & 224 & (24.3\%) &  & 716 & (77.7\%) \\
\bottomrule
\end{tabular}
\vspace{1mm}
\caption{Lines of \Coq code for the \fexistsprod~meta-theory mechanization.}
\vspace{-4mm}
\label{fig:fexistscasestudy}
\end{table}

Table \ref{fig:fexistscasestudy} summarizes the effort required to mechanize
\fexistsprod in the \Coq proof assistant in terms of the de Bruijn
representation.  It lists the lines of \Coq code for different parts divided in
binder-related \emph{boilerplate} and other \emph{useful} code.  The
\emph{specification} row shows the code necessary to fully specify the syntax
and semantics. The boilerplate that arises in this part are the shifting and
substitution functions, context lookups and well-scopedness predicates that are
necessary to define typing and operational semantics. The \emph{syntax-related
  theory} consists of boilerplate lemmas like the commutation lemma
(\ref{lem:substcomm}) for type-substitutions. The useful \emph{semantics-related
  theory} are canonical forms, typing inversion, progress and preservation
lemmas. The boilerplate in this part are the well-scopedness, shifting and
substitution lemmas for the typing relation of Section \ref{sec:formalization}.


\paragraph{Summary}

Table \ref{fig:fexistscasestudy} clearly shows that the boilerplate constitutes
the major part of the effort. Similar boilerplate arises in the formalization of
other languages where it constitutes a similar large part of the whole
formalization. Fortunately, there is much regularity to the boilerplate: it
follows the structure of the language's syntax and scoping rules.

% This fact has already been exploited by many earlier works to derive
% \emph{syntax-related} boilerplate functions and lemmas. The aim of this work is
% to extend the support for binder boilerplate in mechanization to cover
% \emph{semantics-related} boilerplate.

\subsection{Our Approach: Key Ideas}

Our approach consists of extending the \Knot specification language to cover
specifications of relations and also extending \Knot's code generator \Needle to
generate code for semantics-related boilerplate.

\emph{free-monadic view} on syntax \cite{monadic,knotneedle}. At the
syntax-level this view requires one distinguished \emph{variable constructor}
per namespace which has a \emph{reference occurrence} as its only argument and
all other constructors only contain \emph{binding occurrences} and subterms.
At the level of relations this translates to one distinguished \emph{variable
  rule} per namespace (or more specifically per environment clause). This
variable rule has a single lookup as its only premise and the sorts of the
environment data match the sorts of the indices of the relation.

These restrictions allow us to generically establish the substitution lemmas
for relations. Consider the small proof tree on the left:
% , where $A$ is the subtree for the typing judgement of $e_1$.

\[ \begin{array}{ccc}
     \inferrule*[]
       { \highlight{
         \inferrule*[]
           {x:\sigma \in \Gamma,x:\sigma,\Delta,y:\tau}
           {\typing{\Gamma,x:\sigma,\Delta,y:\tau}{x}{\sigma}}
         }
       }
       {\typing{\Gamma,x:\sigma,\Delta}{\lambda y\!\!:\!\!\tau.x}{\tau\to\sigma}}
    &
      \quad\quad\Rightarrow\quad\quad
    &
     \inferrule*[]
       { \highlight{
         \inferrule*[]
           {B'}
           {\typing{\Gamma,\Delta,y:\tau}{e'}{\sigma}}
         }
       }
       {\typing{\Gamma,\Delta}{\lambda y\!\!:\!\!\tau.e'}{\tau\to\sigma}}
   \end{array}
\]

% \[ \begin{array}{c}
%      \inferrule*[]
%        { \inferrule*[]
%            {A}
%            {\typing{\Gamma,x:\sigma,\Delta}{e_1}{\sigma\to\tau}} \and
%          \highlight{
%          \inferrule*[]
%            {x:\sigma \in \Gamma,x:\sigma,\Delta}
%            {\typing{\Gamma,x:\sigma,\Delta}{x}{\sigma}}
%          }
%        }
%        {\typing{\Gamma,x:\sigma,\Delta}{e_1~x}{\tau}} \\\\
%    \end{array}
% \]

From the proof tree on the left we can systematically derive the proof tree on
the right for $(\lambda y\!\!:\!\!\tau.x)[x \mapsto e]$. We do this by
substituting the leaf that uses the variable rule to lookup $x$ in the
environment with the proof tree $B$ for the judgement
$\typing{\Gamma}{e}{\sigma}$. Note that $B$ and $e$ have to be weakened in the
process (to $B'$ and $e'$) to account for $y$ and the variables in $\Delta$.

%% SK: MOVE
%% The term abstraction node in the proof tree can still go through because it is
%% not affected by changes to the free variables the context; it is
%% context-parametric.
%%
%% % \[ \begin{array}{c}
%% %      \inferrule*[]
%% %        { \inferrule*[]
%% %            {A'}
%% %            {\typing{\Gamma,\Delta}{e'_1}{\sigma\to\tau}} \and
%% %          \highlight{
%% %          \inferrule*[]
%% %            {B'}
%% %            {\typing{\Gamma,\Delta}{e'_2}{\sigma}}
%% %          }
%% %        }
%% %        {\typing{\Gamma,\Delta}{e'_1~e'_2}{\tau}} \\\\
%% %    \end{array}
%% % \]
%%
%% In practice, it is too restrictive to require that all non-variable rules are
%% context parametric. Hence, we allow non-parametric regular rules, but rely on
%% the user to fill in the gaps via proof obligations.

} % FEXISTSPROD SCOPE

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% TeX-command-default: "Make"
%%% End:
