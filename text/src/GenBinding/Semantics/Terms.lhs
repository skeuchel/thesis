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
\section{Syntax terms}\label{sec:semantics}

This section generically defines the semantics of \Knot in terms of a de Bruijn
representation, declares the abstract syntax that is valid with respect to the
specification and defines the semantics of binding specifications.
\stevennote{TODO}{The goal is to fully define what well-scoped object language
  terms are. That includes all the dependencies like evaluation of binding
  specifications}

%We assume a given well-formed specification $\spec$ in the rest of this section.

%-------------------------------------------------------------------------------
\subsection{Raw Terms}\label{ssec:sem:rawterms}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \[ \begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lcl@@{\hspace{5mm}}r}
           n,m       & ::= & 0                  & \mid & S~n           & \text{de Bruijn index} \\
           u,v,w     & ::= & K~n                & \mid & K~\ov{u}      & \text{de Bruijn term}  \\
           h, c      & ::= & 0                  & \mid & S_\alpha~h     & \text{Het. number}     \\
           \vartheta & ::= & \multicolumn{3}{l}{\ov{g \mapsto n}, \ov{t \mapsto u}}    & \text{Value env.}      \\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{\Knot semantics: key definitions}
  \label{fig:sem:terms}
\end{figure}

Figure \ref{fig:sem:terms} contains a term grammar for raw terms $u$ of sorts
and environments. A de Bruijn term consists of either a term constructor applied
to a de Bruijn index or a term constructor applied to other terms. An
environment term is either and empty environment or the cons of an environment
and a list of associated sort terms. The cons is additionally tagged with a
namespace $\alpha$. Appendix \ref{appendix:semantics} defines a straightforward
well-sortedness judgement $\vdash u : S$ for raw sort terms and $\vdash u : E$
for raw environment terms.  See also the well-scopedness relation in Figure
\ref{fig:wellscopedness} that refines well-sortedness. \stevennote{TODO}{Better
  transition to the next paragraph.}

\subsection{Binding specification evaluation}\label{ssec:sem:bindspeceval}
\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      box ((evalbs _ _) : bs → ϑ → h)

      evalbs ε ϑ            =  0
      evalbs (bs , xα) ϑ    =  evalbs bs ϑ  +  Iα
      evalbs (bs , f t) ϑ   =  evalbs bs ϑ  +  ⟦ f ⟧ (ϑ t)
      \end{code}

      \begin{code}
      box (⟦ _ ⟧ : f → u → h)
      ⟦ f ⟧ (K (overline u))  = evalbs bs (overline (t ↦ u))
        where  f (K (overline x) (overline t)) = bs
      \end{code}
    \end{minipage}
  }
  \caption{Binding specification evaluation}
  \label{fig:sem:bindspec}
\end{figure}

The binding specification |[bs] t| for a particular subterm |t| of a given term
constructor |K| defines the variables that are brought into scope in |t|. For
example, the binding specification of the pattern-matching case of \fprod in
Figure \ref{fig:systemfprodspec} states that the pattern variables are bound in
the body by means of a function |bind| that collects these variables. We need to
define an interpretation of binding specifications and functions that we can use
in the definitions of boilerplate functions.

Figure \ref{fig:sem:bindspecs} defines the interpretation
$\evalbs{\bindspec}{\vartheta}$ of a binding specification $\bindspec$ as a
meta-level evaluation. Interpretation is always performed in the context of a
particular constructor $K$. \stevennote{LOCAL ENV. Also say that the global
  variable mapping is used in the semantics of relations}{This is taken into
  account in the interpretation function: the parameter $\vartheta$ is a mapping
  from field labels to concrete subterms (and an unused mapping from global
  variables to de Bruijn indices).} We assume well-sortedness of the terms in
$\vartheta$.
%% Traditionally, one would use a natural number to count the number of variables
%% that are being bound. Instead, we use heterogeneous variable lists $\hvl$ --
%% a refinement of natural numbers -- defined in Figure \ref{fig:eval} for dealing
%% with heterogeneous contexts: each successor |Sα| is tagged with a namespace |α|
%% to keep track of the number and order of variables of different namespaces. This
%% allows us to model languages with heterogeneous binders, i.e. that bind
%% variables of different namespaces at the same time, for which reordering the
%% bindings is undesirable.
The result of the evaluation is a heterogeneous number $h$. Like in
Section~\ref{sec:overview}, we use |Iα| as abbreviation for $S_\alpha~0$ and
make use of addition.

In case the binding specification item is a single-variable binding, the result
is a one with the correct tag. In the interesting case of a function call
$f~t_i$, the evaluation pattern matches on the corresponding subterm
$\vartheta~t_i$ and interprets the right-hand side of the appropriate function
clause with respect to the new subterms. Note that we have ruled out function
definitions for variable constructors. Thus, we do not need to handle that case
here.

%% The $\hvl$s are term counterparts of environments from which the associated
%% information has been dropped. The function $|domain|$ in Figure \ref{fig:eval}
%% makes this precise by calculating the underlying $\hvl$ of an environment term.
%% In the following, we use the extension of addition from natural numbers to
%% concatenation |_+_| of $\hvl$s -- defined in Figure \ref{fig:eval} -- and
%% implicitly use its associativity property. In contrast, concatenation is not
%% commutative. We mirror the convention of extending environments to the right at
%% the level of $\hvl$ and will always add new variables on the right-hand side of
%% concatenation.

%-------------------------------------------------------------------------------
\subsection{Well-scopedness}\label{ssec:sem:wellscopedness}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.95\columnwidth}
    \framebox{\mbox{$h \vdash_\alpha n$}} \\
    \vspace{-7mm}
    \[ \begin{array}{c}
       \inferrule* [right=\textsc{WsZero}]
                   {\,}
                   {S_\alpha~h \vdash_\alpha 0} \quad\quad
       \inferrule* [right=\textsc{WsHom}]
                   {h \vdash_\alpha n}
                   {S_\alpha~h \vdash_\alpha S~n} \quad\quad
       \inferrule* [right=\textsc{WsHet}]
                   {\alpha \neq \beta \\\\
                    h \vdash_\alpha n
                   }
                   {S_\beta~h \vdash_\alpha n}
       \end{array}
    \]
    \framebox{\mbox{$h \vdash u : S$}} \\
    \vspace{-7mm}
    \[ \begin{array}{c}
       \inferrule* [right=\textsc{WsVar}]
                   {h \vdash_\alpha n \\ K : \alpha \rightarrow S
                   }
                   {K~n : S}  \quad\quad
       \inferrule* [right=\textsc{WsCtor}]
                   {K : \overline{x : \alpha} \rightarrow \overline{[bs] t : T} \rightarrow S \\\\
                    |ϑ = overline (t ↦ u)| \\\\
                    h + |⟦ bs_i ⟧ (sub ϑ) ⊢ u_i| : T_i \quad (\forall i)}
                   {h \vdash K~\overline{u} : S}
       \end{array}
    \]
    \framebox{\mbox{$h \vdash \Gamma : E$}} \\
    \vspace{-8mm}
    \[ \begin{array}{c}
       \inferrule* [right=\textsc{WsNil}]
                   {\,}
                   {h \vdash [~] : E} \quad\quad
       \inferrule* [right=\textsc{WsCons}]
                   {E : \alpha \to \overline{T} \\
                    |h ⊢ Γ| \\\\
                    |h + domain Γ ⊢ u_i : T_i| \quad (\forall i)}
                   {|h ⊢ (Γ ► overline u) : E|}
       \end{array}
    \]
    \end{minipage}
  }
  \caption{Well-scopedness of terms}
  \label{fig:wellscopedness}
\end{figure}

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

Figure \ref{fig:wellscopedness} defines the well-scopedness relation on de
Bruijn indices as well as sort and environment terms. The relation
$h \vdash_\alpha n$ denotes that $n$ is a well-scoped de Bruijn index for
namespace $\alpha$ with respect to the variables in $h$. This is a refinement of
$n < h$ in which only the successors for namespace $\alpha$ in $h$ are taken
into account. This is accomplished by rule \textsc{WsHom} which strips away one
successor in the homogeneous case and rule \textsc{WsHet} that simply skips
successors in the heterogeneous case. Rule \textsc{WsZero} forms the base case
for $n=0$ which requires that $h$ has a successor tagged with $\alpha$.

Rule \textsc{WsVar} delegates well-scopedness of variable constructors to the
well-scopedness of the index in the appropriate namespace. In rule
\textsc{WsCtor}, the heterogeneous variable list $h$ is extended for each subterm
$u_i$ with the result of evaluating its binding specification |bs_i|.

The relation |h ⊢ Γ| defines the well-scopedness of environment terms with
respect to previously existing variables |h|. We will also write |⊢ Γ| as
short-hand for |0 ⊢ Γ|. Note in particular that rule \textsc{WsCons} extends $h$
with the |domain| of the existing bindings when checking the well-scopedness of
associated data.




%if False
\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}

      \begin{code}
      box (⟦ _ | _ ⟧ (sub _) : bs → sym → ϑ → u)

      ⟦ bs        | t                               ⟧ (sub ϑ) = ϑ t
      ⟦ bs        | K g                             ⟧ (sub ϑ) = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
      ⟦ bs,b,bs'  | K b                             ⟧ (sub ϑ) = K (0 + ⟦ bs' ⟧ (sub ϑ))
      ⟦ bs        | K (overline b) (overline sym)   ⟧ (sub ϑ) = K (overline (⟦ bs, {b' ↦ b}bs' | sym ⟧ (sub ϑ)))
        where  K : (overline ((b':α))) → (overline (([bs']s:S))) → T
      ⟦ bs,bs'    | weaken sym bs'                 ⟧ (sub ϑ)         =  shstar (evalsym bs sym ϑ) (evalbs bs' ϑ)
      ⟦ bs        | subst b sym1 sym2              ⟧ (sub ϑ)         =  su 0 (evalsym bs sym1 ϑ) (evalsym (bs,b) sym2 ϑ)
      \end{code}

      %% \begin{code}
      %% box (⟦ _ | _ ⟧ (sub _) : bs → sym → ϑ → u)
      %%
      %% ⟦ bs        | t                               ⟧ (sub ϑ) = ϑ t
      %% ⟦ bs        | K g                             ⟧ (sub ϑ) = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
      %% ⟦ bs,b,bs'  | K b                             ⟧ (sub ϑ) = K (0 + ⟦ bs' ⟧ (sub ϑ))
      %% ⟦ bs        | K (overline b) (overline sym)   ⟧ (sub ϑ) = K (overline (⟦ bs, bs'' | sym ⟧ (sub ϑ)))
      %%   where  K : (overline ((b':α))) → (overline (([bs']s:S))) → T
      %%          (overline (evalbig (overline (b' ↦ b),overline (s ↦ sym)) bs' bs''))
      %% ⟦ bs,bs'    | weaken sym bs'                 ⟧ (sub ϑ)         =
      %%   shstar (evalsym bs sym ϑ) (evalbs bs' ϑ)
      %% ⟦ bs        | subst b sym1 sym2              ⟧ (sub ϑ)         =
      %%   su 0 (evalsym bs sym1 ϑ) (evalsym (bs,b) sym2 ϑ)
      %% \end{code}
     \begin{tabular}{@@{}ll}
       \begin{minipage}[c]{0.25\columnwidth}
        \begin{code}
        box (shstar : u → h → u)
        \end{code}
        \end{minipage}
        &
       \begin{minipage}[c]{0.4\columnwidth}
       \begin{code}
        shstar u  0        = u
        shstar u  (Sα  h)  = shα 0 (shstar u h)
        \end{code}
        \end{minipage}
     \end{tabular}
    \end{minipage}
  }
  \caption{Term semantics: key definitions}
  \label{fig:sem:terms}
\end{figure}
%endif


% \begin{figure}[t]
% \begin{center}
% \fbox{
%   \begin{minipage}{0.98\columnwidth}
%    \begin{tabular}{@@{}ll}
%    \begin{minipage}[c]{0.3\columnwidth}
%     \begin{code}
%     box ((evalbs _ _) : bs → ϑ → h)
%     \end{code}
%     \end{minipage}
%      &
%    \begin{minipage}[c]{0.4\columnwidth}
%     \begin{code}
%     evalbs ε ϑ            =  0
%     evalbs (bs , xα) ϑ    =  evalbs bs ϑ  +  Iα
%     evalbs (bs , f ti) ϑ  =  evalbs bs ϑ  +  ⟦ f ⟧ (ϑ ti)
%     \end{code}
%     \end{minipage}
%     \end{tabular}
%
%    \begin{tabular}{@@{}ll}
%    \begin{minipage}[c]{0.3\columnwidth}
%     \begin{code}
%     box (⟦ _ ⟧ : f → u → h)
%    \end{code}
%    \end{minipage}
%    &
%    \begin{minipage}[c]{0.4\columnwidth}
%     \begin{code}
%     ⟦ f ⟧ (K (overline u))  = evalbs bs (overline (t ↦ u))
%       where  f (K (overline x) (overline t)) = bs
%     \end{code}
%    \end{minipage}
%    \end{tabular}
%
%   \end{minipage}
% }
% \end{center}
% \caption{Interpretation of binding specifications and functions}
% \label{fig:eval}
% \end{figure}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
