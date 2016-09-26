%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%format (box (stuff)) = "\hspace{-1em}\framebox{\mbox{\ensuremath{" stuff "}}}"
%format (evalsym (bs) sym th) = "\llbracket\: {" bs "} \mid {" sym "} \:\rrbracket_{" th "}"
%format (evalbs (bs) th) = "{\llbracket\: {" bs "} \:\rrbracket_{" th "}}"

%format (mathit x)    = "\mathit{" x "}"
%format ci      = c  "_" i
%format ki      = k  "_" i
%format mi      = m  "_" i
%format si      = s  "_" i
%format ti      = t  "_" i
%format (sub (s)) = "_{" s "}"

%format h1
%format h2

%format shα = "{{" sh "}_{\alpha}}"
%format shstar = "{{" sh "}^{*}}"
%format sym1
%format sym2
%format (evalbig x y z) = "{\evalbig{" x "}{" y "}{" z "}}"

%-------------------------------------------------------------------------------
\section{Term Semantics}\label{sec:sem:terms}

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
  \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lcl@@{\hspace{5mm}}r}
      n,m       & ::= & 0                                  & \mid & S~n        & \text{de Bruijn index} \\
      u,v,w     & ::= & K~n                                & \mid & K~\ov{u}   & \text{de Bruijn term}  \\
      h, c      & ::= & 0                                  & \mid & S_\alpha~h & \text{Het. number}     \\
      \vartheta & ::= & \ov{g \mapsto n}, \ov{t \mapsto u} &      &            & \text{Value env.}      \\
    \end{array}
  \]

  \end{minipage}
}
\end{center}
\caption{\Knot semantics: term grammar}
\label{fig:knot:termgrammar}
\end{figure}

We assume that information about constructors is available in a global
environment. We use |(K : α → S)| for looking up the type of a variable
constructor and |(K : (overline α) → (overline T) → S)| for retrieving the
fields types of regular constructors.

\subsection{De Bruijn Terms}\label{ssec:sem:dbterms}
Figure \ref{fig:knot:termgrammar} contains a term grammar for raw terms $u$ of
sorts and environments. A de Bruijn term consists of either a term constructor
applied to a de Bruijn index or a term constructor applied to other terms.  The
well-sortedness judgements $\vdash u : S$ for sort terms and $\vdash u : E$ for
environment terms in Figure \ref{fig:sem:wellsortedness} make precise which
terms are valid with respect to the specification.

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$\vdash u : S$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{DbVar}]
                 {K : \alpha \rightarrow S
                 }
                 {\vdash K~n : S}  \quad\quad
     \inferrule* [right=\textsc{DbReg}]
                 {K : \overline{x : \alpha} \rightarrow \overline{[bs] t : T} \rightarrow S \\\\
                  \vdash u_i : T_i \quad (\forall i)}
                 {\vdash K~\overline{u} : S}
     \end{array}
  \]
  \framebox{\mbox{$\vdash \Gamma : E$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{DbNil}]
                 {\color{red} TODO}
                 {\vdash K : E} \quad\quad
     \inferrule* [right=\textsc{DbCons}]
                 {\color{red} TODO~~
                  K : \alpha \to \overline{T} \\
                  \vdash u : E \\
                  \ov{\vdash v : T}}
                 {\vdash K~u~\ov{v} : E}
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Well-sortedness of terms}
\label{fig:sem:wellsortedness}
\end{figure}

Like in Section \label{sec:overview}, we define \emph{heterogeneous numbers}
$h$, but generalized over the namespaces of the specification at hand, and also
use |Iα| as abbreviation for $S_\alpha~0$ and make use of addition.

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.98\columnwidth}
    \begin{tabular}{@@{}ll}
      \begin{minipage}{0.49\columnwidth}
        \begin{code}
          box ((evalbs _ _) : bs → ϑ → h)

          (evalbs ε ϑ)  =  0
          evalbs (bs , xα) ϑ  =  evalbs bs ϑ  +  Iα
          evalbs (bs , f t) ϑ  =  evalbs bs ϑ  +  ⟦ f ⟧ (ϑ t)
        \end{code}
      \end{minipage}
       &
      \begin{minipage}{0.49\columnwidth}
        \begin{code}
          box (⟦ _ ⟧ : f → u → h)
          ⟦ f ⟧ (K (overline u)) = evalbs bs (overline (t ↦ u))
            where  f (K (overline x) (overline t)) = bs
        \end{code}
      \end{minipage} \\
    \end{tabular}

    \begin{tabular}{@@{}ll}
      \begin{minipage}{0.49\columnwidth}
        \begin{code}
          box (dom :: u → h)

          dom [] =  0
          dom (K u (overline v))  =  dom u + Iα
        \end{code}
      \end{minipage}
       &
      \begin{minipage}{0.49\columnwidth}
        \begin{code}
          box (_ + _ :: h → h → h)

          h   +  0      =  h
          h1  +  Sα h2  =  Sα (h1 + h2)
        \end{code}
      \end{minipage} \\
    \end{tabular}
  \end{minipage}
}
\end{center}
\caption{\Knot semantics: Binding specification evaluation}
\label{fig:knot:bindspeceval}
\end{figure}

{\color{green}
\steven{Move this paragraph to overview.}
The binding specification |[bs] t| for a particular subterm |t| of a given term
constructor |K| defines the variables that are brought into scope in |t|. For
example, the binding specification of the pattern-matching case of \fprod in
Figure \ref{fig:systemfprodspec} states that the pattern variables are bound in
the body by means of a function |bind| that collects these variables. We need to
define an interpretation of binding specifications and functions that we can use
in the definitions of boilerplate functions.}

\subsection{Binding Specification Evaluation}\label{ssec:sem:bindspec:eval}
Figure \ref{fig:knot:bindspeceval} defines the interpretation
$\evalbs{\bindspec}{\vartheta}$ of a binding specification $\bindspec$ as a
meta-level evaluation. Interpretation is always performed in the context of a
particular constructor $K$. This is taken into account in the interpretation
function: the parameter $\vartheta$ is a mapping from field labels to concrete
subterms (and a mapping from global variables to de Bruijn indices that is
unused here, but will be used later). We assume well-sortedness of the terms in
$\vartheta$. The result of the evaluation is a heterogeneous number $h$.

In case the binding specification item is a single-variable binding, the result
is a one with the correct tag. In the interesting case of a function call
$|f ti|$, the evaluation pattern matches on the corresponding subterm |ϑ ti| and
interprets the right-hand side of the appropriate function clause with respect
to the new subterms. Note that we have ruled out function definitions for
variable constructors. Thus, we do not need to handle that case here.

The \emph{heterogeneous numbers} are term counterparts of \emph{heterogeneous
  environments} from which the associated information has been dropped. The
function $|dom|$ in Figure \ref{fig:eval} makes this precise by calculating the
underlying $h$ of an environment term.  In the following, we use the extension
of addition from natural numbers to addition |_+_| of $h$s -- defined in Figure
\ref{fig:eval} -- and implicitly use its associativity property. In contrast,
addition is not commutative. We mirror the convention of extending environments
to the right at the level of heterogeneous numbers and will always add new
variables on the right-hand side of addition.

%if False
{\color{red}
Using the interpretation of binding specification we can generically define
\cite{knotneedle} shifting and substitution on terms:
$$
\begin{array}{c@@{\hspace{5mm}}c}
  $\knotbox{\text{sh}_{\alpha,S} : h \to u \to u}$ &
  $\knotbox{\text{sh}_{\alpha,E} : h \to u \to u}$ \\
  $\knotbox{\text{su}_{\alpha,S} : h \to u \to u}$ &
  $\knotbox{\text{su}_{\alpha,E} : h \to u \to u}$ \\
\end{array}
$$

\noindent To simplify the presentation we also assume that these are defined
without any subordination in mind, i.e. for all possible namespace and sort
combinations even if these amount to being the identity function and we drop the
subscript in cases where these can be inferred from the type of the arguments.

Furthermore, we can generically define well-scopedness predicates on de Bruijn terms
which can be found in Appendix \ref{appendix:semantics}
$$
\begin{array}{c@@{\hspace{5mm}}c@@{\hspace{5mm}}c}
  \knotbox{h \vdash_\alpha n} & \knotbox{h \vdash_S u} & \knotbox{h \vdash_E u} \\
\end{array}
$$
and associated generic shifting and substitution lemmas
\cite{knotneedle}.
}
%endif


\subsection{Well-scopedness}\label{ssec:wellscopedness}

Part of the semantics is the well-scopedness of terms. It is current practice to
define well-scopedness with respect to a typing environment: a term is
well-scoped iff all of its free variables are bound in the environment. The
environment is extended when going under binders. For example, when going under
the binder of a lambda abstraction with a type-signature the conventional rule
is:
$$
\begin{array}{c}
\inferrule[]{|Γ, x : τ ⊢ e|}{\hsforall |Γ ⊢ λ(x:τ).e|} \\
\end{array}
$$
The rule follows the intention that the term variable should be of the given
type. In this regard, well-scopedness is already a lightweight type-system.
However, it is problematic for Knot to establish this intention or in general
establish what the associated data in the environment should be. Furthermore, we
allow the user to define different environments with potentially incompatible
associated data. Hence, instead we define well-scopedness by using domains of
environments. In fact, this is all we need to establish well-scopedness.

Figure \ref{fig:sem:wellscopedness} defines the well-scopedness predicates on de
Bruijn indices as well as sort and environment terms. The relation
$h \vdash_\alpha n$ denotes that $n$ is a well-scoped de Bruijn index for
namespace $\alpha$ with respect to the variables in $h$. This is a refinement of
$n < h$ in which only the successors for namespace $\alpha$ in $h$ are taken
into account. This is accomplished by rule \textsc{WsHom} which strips away one
successor in the homogeneous case and rule \textsc{WsHet} that simply skips
successors in the heterogeneous case. Rule \textsc{WsZero} forms the base case
for $n=0$ which requires that $h$ has a successor tagged with $\alpha$.

The well-scopedness relations $h \vdash u : S$ for sort terms and
$h \vdash u : E$ for environments terms are refinements of the well-sortedness
relations of Figure \ref{fig:sem:wellsortedness}. Rule \textsc{WsVar} delegates
well-scopedness of variable constructors to the well-scopedness of the index in
the appropriate namespace. In rule \textsc{WsReg}, the heterogeneous variable
list $h$ is extended for each subterm $u_i$ with the result of evaluating its
binding specification |bs_i|.

The relation |h ⊢ u : E| defines the well-scopedness of environment terms with
respect to previously existing variables |h|. We will also write |⊢ u : E| as
short-hand for |0 ⊢ u : E|. Note in particular that rule \textsc{WsCons} extends
$h$ with the |dom| of the existing bindings when checking the well-scopedness of
associated data.

\begin{figure}[t]
\begin{center}
\fbox{\small
  \begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$h \vdash_\alpha n$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule*
       [right=\textsc{WsZero}]
       {\,}
       {S_\alpha~h \vdash_\alpha 0} \\\\
     \inferrule*
       [right=\textsc{WsHom}]
       {h \vdash_\alpha n}
       {S_\alpha~h \vdash_\alpha S~n} \\\\
     \inferrule*
       [right=\textsc{WsHet}]
       {\alpha \neq \beta \\\\
        h \vdash_\alpha n
       }
       {S_\beta~h \vdash_\alpha n}
     \end{array}
  \]
  \framebox{\mbox{$h \vdash u : S$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule*
       [right=\textsc{WsVar}]
       {h \vdash_\alpha n \\ K : \alpha \rightarrow S}
       {K~n : S}  \\\\
     \inferrule*
       [right=\textsc{WsReg}]
       {K : \overline{x : \alpha} \rightarrow \overline{[bs] t : T} \rightarrow S \\\\
        |ϑ = overline (t ↦ u)| \\\\
        h + |⟦ bs_i ⟧ (sub ϑ) ⊢ u_i| : T_i \quad (\forall i)}
       {h \vdash K~\overline{u} : S}
     \end{array}
  \]
  \framebox{\mbox{$h \vdash u : E$}} \\
  {\textcolor{red}{TODO}
  \vspace{-8mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{WsNil}]
                 {\,}
                 {h \vdash [~] : E} \\\\
     \inferrule* [right=\textsc{WsCons}]
                 {E : \alpha \to \overline{T} \\
                  |h ⊢ Γ : E| \\\\
                  |h + dom u ⊢ v_i : T_i| \quad (\forall i)}
                 {|h ⊢ (Γ ► overline v) : E|}
     \end{array}
  \]}
  \end{minipage}
}
\end{center}
\caption{Well-scopedness of de Bruijn terms}
\label{fig:sem:wellscopedness}
\end{figure}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
