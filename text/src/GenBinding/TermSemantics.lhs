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

%We assume a given well-formed specification $\spec$ in the rest of this section.

%-------------------------------------------------------------------------------
%% \subsection{Term Semantics}\label{sec:sem:terms}

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

Figure \ref{fig:sem:terms} contains a term grammar for raw terms $u$ of sorts
and environments. A de Bruijn term consists of either a term constructor applied
to a de Bruijn index or a term constructor applied to other terms.  We omit the
straightforward well-sortedness judgement $\vdash u : S$ for sort terms and
$\vdash u : E$ for environment terms.

Figure \ref{fig:sem:bindspecs} defines the interpretation
$\evalbs{\bindspec}{\vartheta}$ of a binding specification $\bindspec$ as a
meta-level evaluation. Interpretation is always performed in the context of a
particular constructor $K$. This is taken into account in the interpretation
function: the parameter $\vartheta$ is a mapping from field labels to concrete
subterms (and an unused mapping from global variables to de Bruijn indices). We
assume well-sortedness of the terms in $\vartheta$. The result of the evaluation
is a heterogeneous number $h$. Like in Section~\ref{sec:overview}, we use |Iα|
as abbreviation for $S_\alpha~0$ and make use of addition. In case the binding
specification item is a single-variable binding, the result is a one with the
correct tag. In the interesting case of a function call $|f ti|$, the evaluation
pattern matches on the corresponding subterm |ϑ ti| and interprets the
right-hand side of the appropriate function clause with respect to the new
subterms. Note that we have ruled out function definitions for variable
constructors. Thus, we do not need to handle that case here.

Using the interpretation of binding specification we can generically define
\cite{knotneedle} shifting and substitution on terms:
$$
\begin{array}{c@@{\hspace{5mm}}c}
  $\knotbox{\text{sh}_{\alpha,S} : h \to u \to u}$ &
  $\knotbox{\text{su}_{\alpha,S} : h \to u \to u \to u}$ \\
  $\knotbox{\text{sh}_{\alpha,E} : h \to u \to u}$ &
  $\knotbox{\text{su}_{\alpha,E} : h \to u \to u \to u}$ \\
\end{array}
$$

\noindent To simplify the presentation we assume that these are defined
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


%-------------------------------------------------------------------------------

%if False
\subsection{Expression Semantics}
\label{sec:exprsemantics}

We now define the semantics of symbolic expressions as an evaluation to concrete
de Bruijn terms. Figure~\ref{fig:grammarast} (bottom) contains the definition. The
evaluation function takes as inputs a symbolic expression $\symbolicterm$, the
local scope $\bindspec$ of $\symbolicterm$ and an environment $\vartheta$ that
maps reference variables to concrete de Bruijn indices and sort variables to
concrete de Bruijn terms.

Sort variables $t$ are looked up in $\vartheta$. We assume that these terms are
in the same scope as $t$ and hence they do not need to be adjusted. Global
reference variables $g$ are also looked up in $\vartheta$ but need to be
adjusted by weakening with the interpretation of the current local scope
$\bindspec$. For variable constructors with locally bound variables $b$ we
determine the index by interpreting the difference $\bindspec'$ of the current
scope and the scope where $b$ was introduced. For regular constructors we
recursively evaluate each expression for the sort fields in the local scope
respectively extended with the symbolically evaluated binding specifications of
the fields. Bindings $\ov{b}$ of regular constructors are simply
dropped. Symbolic syntactic operations are replaced by applications of the
concrete versions. In case of symbolic weakening we need to evaluate the
expression argument in the smaller scope $\bindspec$ and weaken it with the
interpretation of $\bindspec'$ for which we use the multi-place shifting
function |shstar| that iterates one-place shiftings. We restricted symbolic
substitution to only allow substituting the last introduced variable and hence
always substitute the index $0$. The expression arguments of substitution need
to be evaluated in their respective local scopes.

% \begin{figure}[t]
% \begin{center}
%   \fbox{
%   \hspace{-2mm}
%   \begin{minipage}{0.98\columnwidth}
%     \begin{code}
%     box (⟦ _ | _ ⟧ (sub _) : bs → sym → ϑ → u)
%
%     ⟦ bs        | t                              ⟧ (sub ϑ) = ϑ t
%     ⟦ bs        | K g                            ⟧ (sub ϑ) = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
%     ⟦ bs,b,bs'  | K b                            ⟧ (sub ϑ) = K (0 + ⟦ bs' ⟧ (sub ϑ))
%     ⟦ bs        | K (overline b) (overline sym)  ⟧ (sub ϑ) = K (overline (⟦ bs, bs'' | sym ⟧ (sub ϑ)))
%       where  K : (overline ((b':α))) → (overline (([bs']s:S))) → T
%              (overline (evalbig (overline (b' ↦ b),overline (s ↦ sym)) bs' bs''))
%     ⟦ bs,bs'    | weaken sym bs'                 ⟧ (sub ϑ)         =
%       shstar (evalsym bs sym ϑ) (evalbs bs' ϑ)
%     ⟦ bs        | subst b sym1 sym2              ⟧ (sub ϑ)         =
%       su 0 (evalsym bs sym1 ϑ) (evalsym (bs,b) sym2 ϑ)
%     \end{code}
%
%    \begin{tabular}{@@{}ll}
%    \begin{minipage}[c]{0.3\columnwidth}
%     \begin{code}
%     box (shstar : u → h → u)
%     \end{code}
%     \end{minipage}
%     &
%    \begin{minipage}[c]{0.4\columnwidth}
%    \begin{code}
%     shstar u  0        = u
%     shstar u  (Sα  h)  = shα 0 (shstar u h)
%     \end{code}
%     \end{minipage}
%     \end{tabular}
%   \end{minipage}
% }
% \end{center}
% \caption{Interpretation of symbolic expressions}
% \label{fig:evalsymbolicterm}
% \end{figure}

%endif

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
