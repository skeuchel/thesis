%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\section{Overview}\label{sec:overview}

This section illustrates the boilerplate that arises when mechanizing
type-safety proofs, outlines our specific approach and defines necessary
terminology. Our running example is \fexistsprod{}, i.e. \SystemF with universal
and existential quantification and products. Figure
\ref{fig:systemfexistssyntax} defines the syntax of \fexistsprod{}, in a
textbook manner.

\newcommand{\pack}[3]{\{{#1},{#2}\}~\text{as}~{#3}}
\newcommand{\unpack}[4]{\text{let}~\{{#1},{#2}\}={#3}~\text{in}~{#4}}
\newcommand{\casep}[3]{\text{case}~{#1}~\text{of}~{#2}\to{#3}}
\newcommand{\typing}[3]{{#1} \vdash_\text{tm} {#2} : {#3}}
\newcommand{\kinding}[2]{{#1} \vdash_\text{ty} {#2}}
\newcommand{\ptyping}[4]{{#1} \vdash_\text{p} {#2} : {#3} ; {#4}}

\begin{figure}[t]
\begin{center}
\fbox{
\begin{minipage}{0.98\columnwidth}
\begin{tabular}{lcll@@{\hspace{8mm}}lcll}
  $\alpha,\beta$ & ::=    &                                & type variable    & $\Gamma,\Delta$ & ::=    &                        & type context     \\
  $x,y$          & ::=    &                                & term variable    &                 & $\mid$ & $\epsilon$             & empty context    \\
  $e$            & ::=    &                                & term             &                 & $\mid$ & $\Gamma, \alpha$       & type binding     \\
                 & $\mid$ & $x$                            & term variable    &                 & $\mid$ & $\Gamma, x:\tau$       & term binding     \\
                 & $\mid$ & $\lambda x:\tau.e$             & term abstraction & $\tau,\sigma$   & ::=    &                        & type             \\
                 & $\mid$ & $e_1~e_2$                      & application      &                 & $\mid$ & $\alpha$               & type variable    \\
                 & $\mid$ & $\Lambda\alpha.e$              & type abstraction &                 & $\mid$ & $\tau \to \tau$        & function type    \\
                 & $\mid$ & $e~\tau$                       & type application &                 & $\mid$ & $\forall\alpha.\tau$   & universal type   \\
                 & $\mid$ & $\pack{\tau}{e}{\tau}$         & packing          &                 & $\mid$ & $\exists\alpha.\tau$   & existential type \\
                 & $\mid$ & $\unpack{\alpha}{x}{e_1}{e_2}$ & unpacking        &                 & $\mid$ & $\tau_1 \times \tau_2$ & product type     \\
                 & $\mid$ & $e_1,e_2$                      & pair             & $p$             & ::=    &                        & pattern          \\
                 & $\mid$ & $\casep{e_1}{p}{e_2}$          & pattern binding  &                 & $\mid$ & $x$                    & variable pattern \\
                 &        &                                &                  &                 & $\mid$ & $p_1 , p_2$            & pair pattern     \\
\end{tabular}
\vspace{2mm}
\hrule
\vspace{2mm}
  {\small
  \framebox{\mbox{$\typing{\Gamma}{e}{\tau}$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{TAbs}]
       {\typing{\Gamma,y:\sigma}{e}{\tau}
       }
       {\typing{\Gamma}{(\lambda y:\sigma. e)}{\sigma\to\tau}} \quad\quad
     \inferrule* [right=\textsc{TVar}]
       {x : \tau \in \Gamma
       }
       {\typing{\Gamma}{x}{\tau}} \\\\
     \inferrule* [right=\textsc{TTApp}]
       {\typing{\Gamma}{e}{\forall\alpha.\tau}
       }
       {\typing{\Gamma}{e~\sigma}{[\alpha\mapsto\sigma]\tau}} \quad\quad
     \inferrule* [right=\textsc{TPack}]
       {\typing{\Gamma}{e}{[\alpha\mapsto\sigma]\tau}
       }
       {\typing{\Gamma}{\pack{\sigma}{e}{\exists\alpha.\tau}}{\exists\alpha.\tau}} \\\\
     \inferrule* [right=\textsc{TPair}]
       {\typing{\Gamma}{e_1}{\tau_1} \\\\
        \typing{\Gamma}{e_2}{\tau_2}
       }
       {\typing{\Gamma}{e_1,e_2}{\tau_1 \times \tau_2}} \qquad
     \inferrule* [right=\textsc{TCase}]
       {\typing{\Gamma}{e_1}{\sigma} \\
        \ptyping{\Gamma}{p}{\sigma}{\Delta} \\\\
        \typing{\Gamma,\Delta}{e_2}{\tau} \\
       }
       {\typing{\Gamma}{\casep{e_1}{p}{e_2}}{\tau}} \\
     \end{array}
   \]
  \framebox{\mbox{$\ptyping{\Gamma}{p}{\tau}{\Delta}$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{PPair}]
       {\ptyping{\Gamma}{p_1}{\tau_1}{\Delta_1} \\
        \ptyping{\Gamma,\Delta_1}{p_2}{\tau_2}{\Delta_2} \\
       }
       {\ptyping{\Gamma}{p_1,p_2}{\tau_1 \times \tau_2}{\Delta_1,\Delta_2}} \qquad
     \end{array}
   \]
   }
\end{minipage}
}
\end{center}
\caption{\fexistsprod syntax and selected typing rules}
\label{fig:systemfexistssyntax}
\end{figure}


\subsection{Relational Semantics}

% \begin{figure}[t]
% \begin{center}
% \fbox{
%   \begin{minipage}{0.95\columnwidth}
%   \framebox{\mbox{$\typing{\Gamma}{e}{\tau}$}} \\
%   \vspace{-7mm}
%   \[ \begin{array}{c}
%      \inferrule* [right=\textsc{TVar}]
%                  {x : \tau \in \Gamma
%                  }
%                  {\typing{\Gamma}{x}{\tau}} \\\\
%      \inferrule* [right=\textsc{TAbs}]
%                  {\typing{\Gamma,y:\sigma}{e}{\tau}
%                  }
%                  {\typing{\Gamma}{(\lambda y:\sigma. e)}{\sigma\to\tau}} \\\\
%      \inferrule* [right=\textsc{TTApp}]
%                  {\typing{\Gamma}{e}{\forall\alpha.\tau}
%                  }
%                  {\typing{\Gamma}{e~\sigma}{[\alpha\mapsto\sigma]\tau}} \\\\
%      \inferrule* [right=\textsc{TPack}]
%                  {\typing{\Gamma}{e}{[\alpha\mapsto\sigma]\tau}
%                  }
%                  {\typing{\Gamma}{\pack{\sigma}{e}{\exists\alpha.\tau}}{\exists\alpha.\tau}}
%      \end{array}
%   \]
%
%   \end{minipage}
% }
% \end{center}
% \caption{\fexists typing - selected rules}
% \label{fig:systemfexiststyping:textbook}
% \end{figure}

Figure \ref{fig:systemfexistssyntax} also contains selected rules for the
term and pattern typing relations. The variable rule \textsc{TVar} of the
term typing looks up a term variable $x$ with its associated type $\tau$
in the type context $\Gamma$. Because this rule inspects the context $\Gamma$ we
call it \emph{not context parametric}. The other rules either pass the context
through unchanged or pass an extended context to the premises. We call these
rules \emph{context parametric}.

Rule \textsc{TAbs} deals with abstractions over terms in terms. The
meta-variable $y$ appears in a different mode in the conclusion than the
meta-variable $x$ in the variable rule. The $\lambda$-abstraction binds the
variable $y$ and we call it a \emph{binding occurrence} whereas the $x$ in the
variable rule is a \emph{reference} or \emph{use occurrence}.

Following the literature on \emph{locally nameless}~\cite{locallynameless} and
\emph{locally named}~\cite{externalinternalsyntax} representations we call $y$ a
\emph{locally bound} variable (aka locally scoped variables \cite{pitts2015}),
or more concisely a \emph{binding variable}, and $x$ a \emph{global} or
\emph{free variable}. Another example is the judgement
$\typing{\Gamma}{(\lambda y. y)~x}{\tau}$. Here $y$ is again locally bound and
$x$ has to be bound in $\Gamma$ for the judgement to be well-scoped. In this
example, the meta-variable $y$ appears in both binding and referencing
positions. The distinction between locally bound and free variables goes back to
at least Frege \cite{begriffsschrift} and representations such as locally
nameless and locally named have internalized this distinction. Frege
characterizes free variables as variables that can possibly stand for anything
while locally bound variables stand for something very specific. Indeed, in the
above judgement, the use of $y$ can only denote a reference to the directly
enclosing abstraction. These concepts do not commit us to a particular
representation of variable binding. Rather, these notions arise naturally in
meta-languages.

The rules \textsc{TTApp} for type-application and \textsc{TPack} for packing
existential types use a type-substitution operation $[\alpha\mapsto\sigma]\tau$
that substitutes $\sigma$ for $\alpha$ in $\tau$. \textsc{TTApp} performs the
substitution in the conclusion while \textsc{TPack} does so in the premise. The
substituted type-variable $\alpha$ is locally bound in both rules.  The
remaining two rules, \textsc{TPair} and \textsc{TCase}, of the term typing
relation deal with products. In a case expression the pattern $p$ needs to have
the same type $\sigma$ as the scrutinee $e_1$ and the variables $\Delta$
bound by $p$ are brought into scope in the body $e_2$. This environment
$\Delta$ is the output of the
pattern typing relation $\ptyping{\Gamma}{p}{\tau}{\Delta}$, which contains the typing information for all
variables bound by $p$. This information is concatenated in the rule
\textsc{PPair} for pair patterns.



%-------------------------------------------------------------------------------

\subsection{Meta-Theory}

\newcommand{\pmatch}[4]{\text{Match}~{#1}~{#2}~{#3}~{#4}}

The operational semantics is defined with 4 reduction rules
\[\begin{array}{c}
  (\lambda x.e_1)~e_2 \longrightarrow [x \mapsto e_2] e_1 \quad\quad\quad (\Lambda \alpha.e) \tau \longrightarrow [\alpha \mapsto \tau] e \\
  \unpack{\alpha}{x}{\pack{\sigma}{e_1}{\tau}}{e_2} \longrightarrow [\alpha\mapsto\sigma][x\mapsto e_1]e_2 \\
     \inferrule*[]
       {\pmatch{v}{p}{e_1}{e_2}}
       {\casep{v}{p}{e_1} \longrightarrow e_2}
   \end{array}
\]

and further congruence rules that determine the evaluation order. A key step in the
type preservation proof is the preservation under these reductions, which boils
down to two substitution lemmas:
%
\begin{align}
    \label{lem:substtm}
      \typing{\Gamma}{e_1}{\sigma} \;\Rightarrow\;
      \typing{\Gamma,x : \sigma,\Delta}{e_2}{\tau} \;\Rightarrow\;
      \typing{\Gamma,\Delta}{[x\mapsto e_1]e_2}{\tau} \\
    \label{lem:substty}
      \kinding{\Gamma}{\sigma} \;\Rightarrow\;
      \typing{\Gamma,\beta,\Delta}{e}{\tau} \;\Rightarrow\;
      \typing{\Gamma,[\beta\mapsto\sigma]\Delta}{[\beta\mapsto\sigma]e}{[\beta\mapsto\sigma]\tau}
\end{align}

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
  {\kinding
    {\Gamma}
    {\sigma} \\
   \Gamma' =  \Gamma,[\beta\mapsto\sigma]\Delta \\
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

As the term in the conclusion remains a type application, we want to apply rule
\textsc{TTApp} again. However, the \colorbox{light-gray}{type} in the conclusion
does not have the appropriate form. We first need to commute the two substitutions
with one of the common interaction lemmas
\begin{align}
  [\beta\mapsto \sigma][\alpha \mapsto \sigma'] =
  [\alpha \mapsto [\beta\mapsto\sigma]\sigma'][\beta\mapsto\sigma] \label{lem:substcomm}
\end{align}

Intuitively this commutation is possible because $\beta$ is a free
variable while $\alpha$ is locally bound and because context parametric rules are naturally
compatible with any changes to the context.

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
    \begin{tabular}{lcllclcllcl}
      $E$ & ::=    & $\text{enil}$     & $T$ & ::=    & $\text{tvar}~n$        & $\mid$ & $\text{tforall}~T$     & $q$ & ::=    & $\text{pvar}$          \\
          & $\mid$ & $\text{etvar}~E$  &     & $\mid$ & $\text{tarr}~T_1~T_2$  & $\mid$ & $\text{texist}~T$      &     & $\mid$ & $\text{ppair}~q_1~q_2$ \\
          & $\mid$ & $\text{evar}~E~T$ &     & $\mid$ & $\text{tprod}~T_1~T_2$ & $\mid$ & $\text{tprod}~T_1~T_2$ &     &        &                        \\
    \end{tabular}
    \vspace{1mm}
    \hrule
    \vspace{1mm}
    \begin{tabular}{lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}lc@@{\hspace{2mm}}l}
      $t$ & ::= & $\text{var}~n$ & $\mid$ & $\text{abs}~T~t$     & $\mid$ & $\text{tyabs}~t$   & $\mid$ & $\text{pack}~T_1~t~T_2$ & $\mid$ & $\text{pair}~t_1~t_2$ \\
          &     &                & $\mid$ & $\text{app}~t_1~t_2$ & $\mid$ & $\text{tyapp}~t~T$ & $\mid$ & $\text{unpack}~t_1~t_2$ & $\mid$ & $\text{case}~t_1~q~t_2$ \\
     \end{tabular}
  \end{minipage}
}
\end{center}
\caption{\fexists syntax and de Bruijn representation}
\label{fig:systemfdebruijn}
\end{figure}


Figure \ref{fig:systemfdebruijn} shows a term grammar for a de Bruijn
representation of \fexistsprod. We use different namespaces for term and type
variables and treat indices for variables from distinct namespaces
independently. For example the polymorphic const function
$(\Lambda\alpha.\Lambda\beta.\lambda x\!\!:\!\!\alpha.\lambda y\!\!:\!\!\beta.x)$ is represented
by the de Bruijn term
$(\text{tyabs}~ (\text{tyabs}~ (\text{abs}~ (\text{tvar}~ 1)~ (\text{abs}~
(\text{tvar}~ 0)~ (\text{var}~ 1))))$. The index for the type variable $\beta$
that is used in the inner $\text{abs}$ is $0$ and not $1$, because we only count
the number of bindings of type variables.

\paragraph{Well-scopedness}
The well-scopedness of de Bruijn terms is a syntactic concern. It is common
practice to define well-scopedness with respect to a \emph{type} context: a term
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
type. In this style, well-scopedness comprises a lightweight type system.
However, it is problematic for \Knot to come up with the intended typing or, in general,
establish what the associated data in the extended context should be. Furthermore, we
allow the user to define different contexts with potentially incompatible
associated data. Hence, instead we define well-scopedness by using \emph{domains} of
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

Figure \ref{fig:wellscopedness:overview} also defines the calculation $\dom$ of
domains of typing contexts, a well-scopedness predicate $h \vdash_{\text{tm}} n$
for term indices, which corresponds to $n < h$ when only term successors are
counted, and a selection of rules for well-scopedness of terms
$h \vdash_{\text{tm}} t$ and well-scopedness of typing environments
$h \vdash E$.



\begin{figure}[t]
\begin{center}
  \small
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
     \inferrule* []
                 {\,}
                 {S_{\text{tm}}~h \vdash_{\text{tm}} 0} \qquad
     \inferrule* []
                 {h \vdash_{\text{tm}} n}
                 {S_{\text{tm}}~h \vdash_{\text{tm}} S~n} \qquad
     \inferrule* []
                 {h \vdash_{\text{tm}} n
                 }
                 {S_{\text{ty}}~h \vdash_{\text{tm}} n}
     \end{array}
  \]
  \framebox{\mbox{$h \vdash_{\text{tm}} t$}} \\
  \vspace{-7mm}
  \[\begin{array}{c}
      \inferrule*[]
        {h \vdash_\text{tm} n
        }
        {h \vdash_\text{tm} \text{tvar}~n} \qquad
      \inferrule*[]
        {h \vdash_\text{tm}~t_1 \\
         h + 1_{\text{ty}} + 1_{\text{tm}} \vdash_\text{tm}~t_2
        }
        {h \vdash_\text{tm} \text{unpack}~t_1~t_2} \\
     \end{array}
  \]
  \framebox{\mbox{$h \vdash E$}} \\
  \vspace{-8mm}
  \[ \begin{array}{c}
       \inferrule*
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

The semantic typing relation from Figure \ref{fig:systemfexistssyntax}
translates almost directly to a relation on the de Bruijn representation. One
important aspect that is ignored in Figure~\ref{fig:systemfexistssyntax} is
to ensure that all rule components are well-scoped.  This requires including
additional well-scopedness premises in the rules. For example, rule \textsc{TAbs} needs a well-scopedness premise for the argument
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

We use Wright and Felleisen's \cite{progresspreservation} syntactic approach of
proving type-safety via progress and preservation. The type-safety proof of
\fexistsprod requires additional canonical forms, typing inversion and
boilerplate lemmas.  This paper focuses on the boilerplate lemmas related to
semantic relations.\footnote{ Term-related boilerplate has been addressed in
  our previous work~\cite{knotneedle}.}  The principal boilerplate lemmas are a
well-scopedness lemma
$$
  0 \vdash E \wedge \typing{E}{t}{T} \;\Rightarrow\; \domain{E} \vdash t \wedge \domain{E} \vdash T
$$

\noindent two shifting lemmas
$$
\begin{array}{c}
  \typing{E}{t}{T} \;\Rightarrow\; \typing{\text{evar}~E~T'}{\shtm~0~t}{T} \\
  \typing{E}{t}{T} \;\Rightarrow\; \typing{\text{etvar}~E}{\shty~0~t}{\shty~0~T}
\end{array}
$$

\noindent and two substitution lemmas
$$
\begin{array}{c}
  0 \vdash E \wedge
    \typing{E}{t_1}{T_1} \wedge
    \typing{\text{evar}~E~T_1}{t_2}{T_2} \;\Rightarrow\;
    \typing{E}{\sutm~0~t_1~t_2}{T_2} \\

  0 \vdash E \wedge
    \domain{E} \vdash T_1 \wedge
    \typing{\text{etvar}~E}{t_2}{T_2} \;\Rightarrow\;
    \typing{E}{\suty~0~T_1~t_2}{\suty~0~T_1~T_2}
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
The term abstraction node in the proof tree can still go through because
it is not affected by changes to the free variables the context; it is context-parametric.

% \[ \begin{array}{c}
%      \inferrule*[]
%        { \inferrule*[]
%            {A'}
%            {\typing{\Gamma,\Delta}{e'_1}{\sigma\to\tau}} \and
%          \highlight{
%          \inferrule*[]
%            {B'}
%            {\typing{\Gamma,\Delta}{e'_2}{\sigma}}
%          }
%        }
%        {\typing{\Gamma,\Delta}{e'_1~e'_2}{\tau}} \\\\
%    \end{array}
% \]

In practice, it is too restrictive to require that all non-variable rules are
context parametric. Hence, we allow non-parametric regular rules, but rely on
the user to fill in the gaps via proof obligations.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% TeX-command-default: "Make"
%%% End:
