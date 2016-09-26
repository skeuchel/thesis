%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\section{Overview}\label{sec:overview}

\newcommand{\pack}[3]{\{{#1},{#2}\}~\text{as}~{#3}}
\newcommand{\unpack}[4]{\text{let}~\{{#1},{#2}\}={#3}~\text{in}~{#4}}
\newcommand{\typing}[3]{{#1} \vdash_\text{tm} {#2} : {#3}}
\newcommand{\kinding}[2]{{#1} \vdash_\text{ty} {#2}}

\begin{figure}[t]
\begin{center}
\fbox{
\begin{minipage}{0.98\columnwidth}
\begin{tabular}{lcll}
  $\alpha,\beta$  & ::=    &                            & type variable    \\
  $x,y$           & ::=    &                            & term variable    \\
  $\Gamma,\Delta$ & ::=    &                            & type context     \\
                  & $\mid$ & $\epsilon$                 & empty context    \\
                  & $\mid$ & $\Gamma, \alpha$           & type binding     \\
                  & $\mid$ & $\Gamma, x:\tau$           & term binding     \\
  $\tau,\sigma$   & ::=    &                            & type             \\
                  & $\mid$ & $\alpha$                   & type variable    \\
                  & $\mid$ & $\tau \to \tau$            & function type    \\
                  & $\mid$ & $\forall\alpha.\tau$       & universal type   \\
                  & $\mid$ & $\exists\alpha.\tau$       & existential type \\
  $e$             & ::=    &                            & term             \\
                  & $\mid$ & $x$                        & term variable    \\
                  & $\mid$ & $\lambda x:\tau.e$         & term abstraction \\
                  & $\mid$ & $e~e$                      & application      \\
                  & $\mid$ & $\Lambda\alpha.e$          & type abstraction \\
                  & $\mid$ & $e~\tau$                   & type application \\
                  & $\mid$ & $\pack{\tau}{e}{\tau}$     & packing          \\
                  & $\mid$ & $\unpack{\alpha}{e}{e}{e}$ & unpacking        \\
\end{tabular}
\end{minipage}
}
\end{center}
\caption{\fexists syntax}
\label{fig:systemfexists:syntax}
\end{figure}

This section gives an overview of the boilerplate that arises when mechanizing
type-safety proofs, outlines our specific approach and defines necessary
terminology. Our running example is \fexists, i.e. \SystemF with universal and
existential quantification. Figure \ref{fig:systemfexists:syntax} defines the
syntax of \fexists in a textbook-like manner.


\subsection{Relational Semantics}

\begin{figure}[t]
\begin{center}
\fbox{
\begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$\typing{\Gamma}{e}{\tau}$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{TAbs}]
                 {\typing{\Gamma,y:\sigma}{e}{\tau}
                 }
                 {\typing{\Gamma}{(\lambda y:\sigma. e)}{\sigma\to\tau}} \\\\
     \inferrule* [right=\textsc{TVar}]
                 {x : \tau \in \Gamma
                 }
                 {\typing{\Gamma}{x}{\tau}} \quad\quad
     \inferrule* [right=\textsc{TTApp}]
                 {\typing{\Gamma}{e}{\forall\alpha.\tau}
                 }
                 {\typing{\Gamma}{e~\sigma}{[\alpha\mapsto\sigma]\tau}} \\\\
     \inferrule* [right=\textsc{TPack}]
                 {\typing{\Gamma}{e}{[\alpha\mapsto\sigma]\tau}
                 }
                 {\typing{\Gamma}{\pack{\sigma}{e}{\exists\alpha.\tau}}{\exists\alpha.\tau}}
     \end{array}
   \]
\end{minipage}
}
\end{center}
\caption{\fexists selected typing rules}
\label{fig:systemfexists:typing}
\end{figure}


Figure \ref{fig:systemfexists:typing} contains selected rules for the typing
relation of \fexists. The variable rule \textsc{TVar} looks up a term variable
$x$ with its associated type $\tau$ in the type context $\Gamma$. Because this
rule inspects the context $\Gamma$ we call it \emph{not context parametric}. The
other rules either pass the context through unchanged or pass an extended
context to the premises. We call these rules \emph{context parametric}.

Rule \textsc{TAbs} deals with abstractions over terms in terms. The
meta-variable $y$ appears in a different mode in the conclusion than the
meta-variable $x$ in the variable rule. The $\lambda$-abstraction binds the
variable $y$ and we call it a \emph{binding occurrence} whereas the $x$ in the
variable rule is a \emph{reference} or \emph{use occurrence}.

Following the literature on \emph{locally nameless}~\cite{locallynameless} and
\emph{locally named}~\cite{externalinternalsyntax} representations we call $y$ a
\emph{locally bound} variable (aka locally scoped variables
\cite{pitts2015}), or more concisely a \emph{binding variable}, and $x$ a
\emph{global} or \emph{free variable}. Another example is the
judgement $$\typing{\Gamma}{(\lambda y. y)~x}{\tau}$$

Here $y$ is again locally bound and $x$ has to be bound in $\Gamma$ for the
judgement to be well-scoped. In this example, the meta-variable $y$ appears in
both binding and referencing positions. The distinction between locally bound
and free variables goes back to at least Frege \cite{begriffsschrift} and
representations such as locally nameless and locally named have
internalized this distinction. Frege characterizes free variables as variables
that can possibly stand for anything while locally bound variables stand for
something very specific. Indeed, in the above judgement, the use of $y$ can only
denote a reference to the directly enclosing abstraction. These
concepts do not commit us to a particular representation
of variable binding. Rather, these notions arise naturally in meta-languages.

The remaining two rules, \textsc{TTApp} for type-application and
\textsc{TPack} for packing existential types, use a type-substitution
operation $[\alpha\mapsto\sigma]\tau$ that substitutes $\sigma$ for $\alpha$ in
$\tau$. \textsc{TTApp} performs the substitution in the conclusion while \textsc{TPack}
does so in the premise. The substituted type-variable $\alpha$ is locally bound
in both rules.

%-------------------------------------------------------------------------------

\subsection{Meta-Theory}

\newcommand{\sfeeval}[2]{{#1} \longrightarrow {#2}}

\begin{figure}[t]
\begin{center}
\fbox{
\begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$\sfeeval{e}{e}$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
       \inferrule*[]{\,}
         {\sfeeval{(\lambda x.e_1)~e_2}{[x \mapsto e_2] e_1}} \\
       \inferrule*[]{\,}
         {\sfeeval{(\Lambda \alpha.e) \tau}{[\alpha \mapsto \tau] e}} \\
       \inferrule*[]{\,}
         {\sfeeval{\unpack{\alpha}{x}{\pack{\sigma}{e_1}{\tau}}{e_2}}{[\alpha\mapsto\sigma][x\mapsto e_1]e_2}}
     \end{array}
   \]
\end{minipage}
}
\end{center}
\caption{\fexists reduction rules}
\label{fig:systemfexists:reduction}
\end{figure}

The operational semantics is defined with the three $\beta$-rules shown in
Figure \ref{fig:systemfexists:reduction} and further congruence rules that
define the evaluation order. A key step in the type preservation proof is the
preservation under these $\beta$-reductions, which boils down to two
substitution lemmas:

\begin{align}
    \label{lem:substtm}
    \inferrule*[]
      {\typing{\Gamma}{e_1}{\sigma} \\
       \typing{\Gamma,x : \sigma,\Delta}{e_2}{\tau}}
      {\typing{\Gamma,\Delta}{[x\mapsto e_1]e_2}{\tau}} \\
    \label{lem:substty}
    \inferrule*[]
      {\kinding{\Gamma}{\sigma} \\
       \typing{\Gamma,\beta,\Delta}{e}{\tau}}
      {\typing{\Gamma,[\beta\mapsto\sigma]\Delta}{[\beta\mapsto\sigma]e}{[\beta\mapsto\sigma]\tau}}
\end{align}

For the induction to go through, we need to prove these lemmas for all suffixes
$\Delta$, but only use the special case where $\Delta = \epsilon$
in the preservation proof. For the inductive step for rule \textsc{TTApp} of
the second substitution lemma we have to prove the following
\[
\inferrule*[]
  {\kinding
    {\Gamma}
    {\sigma} \\
   \Gamma' =  \Gamma,[\beta\mapsto\sigma]\Delta \\\\
   \typing
    {\Gamma'}
    {[\beta\mapsto\sigma]e}
    {\forall\alpha.[\beta\mapsto\sigma]\tau}
  }
  {\typing
    {\Gamma'}
    {([\beta\mapsto\sigma]e)~([\beta\mapsto\sigma]\sigma')}
    {\gray{[\beta\mapsto\sigma][\alpha\mapsto\sigma']\tau}}
  }
\]

The term in the conclusion remains a type application, so we want to apply rule
\textsc{TTApp} again. However, the \colorbox{light-gray}{type} in the conclusion
does not have the necessary form. We first need to commute the two substitutions
with one of the common interaction lemmas
\begin{align}
  [\beta\mapsto \sigma][\alpha \mapsto \sigma'] =
  [\alpha \mapsto [\beta\mapsto\sigma]\sigma'][\beta\mapsto\sigma] \label{lem:substcomm}
\end{align}

Intuitively this commutation is possible because $\beta$ is a free variable
while $\alpha$ is locally bound and because context parametric rules are
naturally compatible with any changes to the context. \steven{Discuss freshness
constraints for a nominal representation.}

%-------------------------------------------------------------------------------

\subsection{Formalization}\label{sec:formalization}
\paragraph{Syntax Representation} The first step in the formalization is to
choose how to concretely represent variables.
% Traditionally, one would represent
% variables using identifiers, but this requires a massive amount of reasoning
% modulo $\alpha$-equivalence which makes it inevitable to choose a different
% representation.
% Our goal here is not to develop a new approach to variable binding,
% but to scale an existing one.
We choose de Bruijn representations
\cite{namelessdummies} because reasoning with de Bruijn representations is
well-understood, representation of pattern binding and scoping rules are
well-understood and the regular structure of proofs with respect to the abstract
syntax is well-understood which helps us in treating boilerplate generically.

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
    \setlength\tabcolsep{1.5mm}
    \begin{tabular}{lcl@@{\hspace{5mm}}lclcl}
      $E$ & ::=    & $\text{enil}$     & $T$ & ::=    & $\text{tvar}~n$        & $\mid$ & $\text{tforall}~T$ \\
          & $\mid$ & $\text{etvar}~E$  &     & $\mid$ & $\text{tarr}~T_1~T_2$  & $\mid$ & $\text{texist}~T$  \\
          & $\mid$ & $\text{evar}~E~T$ &     & $\mid$ & $\text{tprod}~T_1~T_2$ &        &                    \\
    \end{tabular}
    \vspace{1mm}
    \hrule
    \vspace{1mm}
    \begin{tabular}{lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}l}
      $t$ & ::=    & $\text{var}~n$       & $\mid$ & $\text{abs}~T~t$    & $\mid$ & $\text{tyabs}~t$   & $\mid$ & $\text{pack}~T_1~t~T_2$ \\
          &        &                      & $\mid$ & $\text{app}~t_1~t_2$& $\mid$ & $\text{tyapp}~t~T$ & $\mid$ & $\text{unpack}~t_1~t_2$ \\
     \end{tabular}
  \end{minipage}
}
\end{center}
\caption{\fexists syntax and de Bruijn representation}
\label{fig:systemf:debruijn}
\end{figure}


Figure \ref{fig:systemf:debruijn} shows a term grammar for a de Bruijn
representation of \fexists. We use different namespaces for term and type
variables and treat indices for variables from distinct namespaces
independently. For example the polymorphic const function
$(\Lambda\alpha.\Lambda\beta.\lambda x\!\!\!:\!\!\!\alpha.\lambda
y\!\!\!:\!\!\!\beta.x)$ is represented by the de Bruijn term
$(\text{tyabs}~ (\text{tyabs}~ (\text{abs}~ (\text{tvar}~ 1)~ (\text{abs}~
(\text{tvar}~ 0)~ (\text{var}~ 1))))$. The index for the type variable $\beta$
that is used in the inner $\text{abs}$ is $0$ and not $1$, because we only count
the number of bindings of type variables.

\paragraph{Well-scopedness}
The well-scopedness of de Bruijn terms is a syntactic concern. It is current
practice to define well-scopedness with respect to a type context: a term
is well-scoped iff all its free variables are bound in the context. The
context is extended when going under binders. For example, when going under
the binder of a type-annotated lambda abstraction the conventional rule
is:
$$
\begin{array}{c}
\inferrule[]{|Γ, x : τ ⊢ e|}{\hsforall |Γ ⊢ λ(x:τ).e|} \\
\end{array}
$$
The rule follows the intention that the term variable should be of the given
type. In this style, well-scopedness is already a lightweight type system.
However, it is problematic for \Knot to establish this intention or in general
establish what the associated data in the extended context should be. Furthermore, we
allow the user to define different contexts with potentially incompatible
associated data. Hence, instead we define well-scopedness by using domains of
contexts. In fact, this is all we need to establish well-scopedness.

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

Figure \ref{fig:wellscopedness:overview} also defines the calculation $\dom$ of domains
of typing contexts, a well-scopedness predicate $h \vdash_{\text{tm}} n$ for
term indices, which corresponds to $n < h$ where only term successors are
counted, and a selection of rules for well-scopedness of terms
$h \vdash_{\text{tm}} t$ and well-scopedness of typing environments
$h \vdash E$.



\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
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
  dom enil        =  0
  dom (etvar E)   =  dom E + Ity
  dom (evar E T)  =  dom E + Itm
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
                 {S_{\text{tm}}~h \vdash_{\text{tm}} S~n} \quad\quad
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
        {h \vdash_\text{tm} \text{tvar}~n} \\ \\
      \inferrule*
        [right=\textsc{WsUnpack}]
        {h \vdash_\text{tm}~t_1 \\
         h + 1_{\text{ty}} + 1_{\text{tm}} \vdash_\text{tm}~t_2
        }
        {h \vdash_\text{tm} \text{unpack}~t_1~t_2} \\
     \end{array}
  \]
  \framebox{\mbox{$h \vdash E$}} \\
  \vspace{-8mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{WseTm}]
                 {h \vdash E \\
                  h + \text{dom}~E \vdash T
                 }
                 {h \vdash \text{evar}~E~T
                 }
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Well-scopedness of terms}
\label{fig:wellscopedness:overview}
\end{figure}



\paragraph{Syntax Operations}

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

The operational semantics and typing relations of \fexists require boilerplate
definitions for the de Bruijn representation: substitution of type variables in
types, terms and type contexts, and of term variables in terms. We also
need to define four auxiliary boilerplate \emph{shifting} functions that adapt
indices of free variables when going under binders, or, put differently, when
inserting new variables in the context. We need to generalize shiftings so that
variables can be inserted in the middle of the context, i.e. operations that
correspond to the following weakenings:
$$
|Γ,Δ ⊢ e| \leadsto |Γ,x,Δ ⊢ e| \qquad |Γ,Δ ⊢ e| \leadsto |Γ,α,Δ ⊢ e|
$$

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
(\ref{lem:substtm}) and (\ref{lem:substty}). Hence, the index to be substituted
is represented by the domain of the suffix $\Delta$ to have enough information
for the shifting.
$$
\begin{array}{c@@{\hspace{5mm}}c}
  |box (sutm : h → t → t → t)| &
  |box (suty : h → T → T → T)| \\
  |box (suty : h → T → t → t)| &
  |box (suty : h → T → E → E)|
\end{array}
$$

The generic derivation of shifting and substitution and lemmas for the closure
of well-scopedness under shifting and substitution are tackled in
\cite{knotneedle}.


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


\paragraph{Semantic Representation}

The semantic typing relation from Figure \ref{fig:systemfexists:syntax}
translates almost directly to a relation on the de Bruijn representation. One
important aspect that is ignored in Figure~\ref{fig:systemfexists:syntax} is
to ensure that all rule components are well-scoped.  This requires including
additional well-scopedness premises in the rules. For example, the lambda
abstraction rule \textsc{TAbs} needs a well-scopedness premise for the argument
type:
$$
\inferrule*
  [right=\textsc{TAbs}]
  {\typing
    {\text{evar}~E~T_1}
    {t}
    {T_2} \\
   \dom~E \vdash T_1
  }
  {\typing
    {E}
    {(\text{abs}~T_1~t)}
    {\text{tarr}~T_1~T_2}
  }
$$


\paragraph{Meta-Theory}

We use Wright and Felleisen's \cite{progresspreservation} syntactic approach
of proving type-safety via progress and preservation. The type-safety proof of
\fexists requires additional canonical forms, typing inversion and boilerplate
lemmas.  This paper focuses on the boilerplate lemmas related to semantic relations.\footnote{
Term-related boilerplate has been addressed in earlier work~\cite{knotneedle}.}
The principal boilerplate lemmas are a
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
  {\typing{\text{evar}~E~T'}{\shtm~0~t}{T}
  }
\quad\quad
\inferrule*
  []
  {\typing{E}{t}{T}
  }
  {\typing{\text{etvar}~E}{\shty~0~t}{\shty~0~T}
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
   \typing{\text{evar}~E~T_1}{t_2}{T_2} \\
  }
  {\typing{E}{\sutm~0~t_1~t_2}{T_2} \\
  }
\\\\
\inferrule*
  []
  {0 \vdash E \\
   \domain{E} \vdash T_1 \\
   \typing{\text{etvar}~E}{t_2}{T_2} \\
  }
  {\typing{E}{\suty~0~T_1~t_2}{\suty~0~T_1~T_2} \\
  }
\end{array}
$$


\subsection{Mechanization}

\begin{table}[t]\centering
\ra{1.3}
\begin{tabular}{@@{}r r@@{\,}rcr@@{\,}r@@{}}
\toprule
        & \multicolumn{2}{c}{\textbf{Useful}}  &   \phantom{abc}
        & \multicolumn{2}{c}{\textbf{Boilerplate}} \\
\midrule
\textbf{Specification}    & 71  & (12.2\%) &  & 114 & (19.7\%) \\
\textbf{Syntax Theory}    & 0   & (0.0\%)  &  & 266 & (45.9\%) \\
\textbf{Semantics Theory} & 43  & (7.4\%)  &  & 86  & (14.8\%) \\ \midrule
\textbf{Total}            & 114 & (19.7\%) &  & 466 & (80.3\%) \\
\bottomrule
\end{tabular}
\vspace{1mm}
\caption{Lines of \Coq code for the \fexists~meta-theory mechanization.}
\vspace{-4mm}
\label{fig:systemfexists:casestudy}
\end{table}

Table \ref{fig:systemfexists:casestudy} summarizes the effort required to
mechanize \fexists in the \Coq proof assistant in terms of the de Bruijn
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


\subsection{Summary}

Table \ref{fig:systemfexists:casestudy} clearly shows that the boilerplate
constitutes the major part of the effort. Similar boilerplate arises in the
formalization of other languages where it constitutes a similar large part of
the whole formalization. Fortunately, there is much regularity to the
boilerplate: it follows the structure of the language's syntax and scoping
rules. This fact has already been exploited by many earlier works to derive
\emph{syntax-related} boilerplate functions and lemmas. The aim of this work is
extend the support for binder boilerplate in mechanization to cover
\emph{semantics-related} boilerplate.

Our approach consists of extending the \Knot specification language to cover
specifications of relations and also extend \Knot's code generator \Needle to
generate code for semantics-related boilerplate. A key principle that we employ
is the distinction between \emph{locally bound} and \emph{free} variables at the
meta-level. This allows us to recognize \emph{context parametric} rules and
extend \Knot's free relative monad view on syntax
\cite{relativemonads,knotneedle} to relations: Relations, for which a variable
rule is the only non-parametric rule, have the structure of a free relative
monad and the substitution lemma is fully generically derivable. In practice
this is however too restrictive and we also allow non-parametric regular rules
and rely on the user to fill in the gaps via proof
obligations.



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% TeX-command-default: "Make"
%%% End:
