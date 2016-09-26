%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\section{Appendix A}\label{appendix:semantics}

\subsection{Term well-scopedness}

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
  %% \framebox{\mbox{$h \vdash \Gamma : E$}} \\
  %% \vspace{-8mm}
  %% \[ \begin{array}{c}
  %%    \inferrule* [right=\textsc{WsNil}]
  %%                {\,}
  %%                {h \vdash [~] : E} \\\\
  %%    \inferrule* [right=\textsc{WsCons}]
  %%                {E : \alpha \to \overline{T} \\
  %%                 |h ⊢ Γ| \\\\
  %%                 |h + domain Γ ⊢ u_i : T_i| \quad (\forall i)}
  %%                {|h ⊢ (Γ ► overline u) : E|}
  %%    \end{array}
  %% \]
  \end{minipage}
}
\end{center}
\caption{Well-scopedness of terms}
\label{fig:wellscopednesspred}
\end{figure}


Figure \ref{fig:wellscopednesspred} defines the well-scopedness predicates on de
Bruijn indices and on de Bruijn terms. The relation $h \vdash_\alpha n$ denotes
that $n$ is a well-scoped de Bruijn index for namespace $\alpha$ with respect to
the variables in $h$. This is a refinement of $n < h$ in which only the
successors for namespace $\alpha$ in $h$ are taken into account.

%% This is
%% accomplished by rule \textsc{DbHom} which strips away one successor in the
%% homogeneous case and rule \textsc{DbHet} that simply skips successors in the
%% heterogeneous case. Rule \textsc{DbZero} forms the base case for $n=0$ which
%% requires that $h$ has a successor tagged with $\alpha$.
%%
%% Rule \textsc{DbVar} delegates well-scopedness of variable constructors to the
%% well-scopedness of the index in the appropriate namespace. In rule
%% \textsc{DbReg}, the heterogeneous variable list $h$ is extended for each subterm
%% $u_i$ with the result of evaluating its binding specification |bs_i|.


\subsection{Derivation semantics}

\begin{figure}[t]
\begin{center}
\fbox{\small
  \begin{minipage}{0.98\columnwidth}

  \begin{code}
  box ((evalrbs _ _ _ _) : rbs → LENV → E → ϑ → u)

  evalrbs ε LENV E ϑ  =  0
  evalrbs (rbs , b → overline sym) LENV E ϑ  =
      K ((evalrbs rbs LENV E ϑ)) ((evalsym bs sym ϑ))
    where  (b : α) ∈ LENV
           (K : α → overline T) ∈ E
           (symflatten LENV rbs bs)
  evalrbs (rbs , f j) LENV E ϑ             =
    append ((evalrbs rbs LENV E ϑ)) (ϑ (f,j))
  \end{code}

  \framebox{\mbox{$\judg{u_E?}{R}{\ov{u_t}}{\ov{u_f}}$}} \\
  \[ \begin{array}{c}

     \inferrule* [right=\textsc{DerVar}]
       {{\texttt{+} r : \{g \mapsto \ov{t}\} \to R~(K~g)~\ov{t}} \\
        K : \alpha \to S \\
        (K' : \alpha \cto \ov{T} : R) \in E \\
        (n:\ov{v}) \in_{E,\alpha} u_E
       }
       {\judg{u_E}{R}{(K~n),\ov{v}}{\epsilon}} \\\\

     \inferrule*[right=\textsc{DerReg}]
       {\texttt{||} r : \ov{\formula} \to R~\ov{\symbolicterm} ; \ov{f = \rulebindspec} \\
        \LENV = \ov{(g @@ \alpha)},\ov{([bs]b : \alpha)},\ov{([bs]s : S)}, \ov{([\bindspec]~\jmv:R~\ov{\symbolicterm})} \\
        \ov{\wfformula{E_{?}}{\formula}} \\
        \ov{\wfsym{\epsilon}{\symbolicterm}{S}} \\
        \vartheta = \ov{g \mapsto n},\ov{s \mapsto u_s},\ov{(f,\jmv) \mapsto u_{f\jmv}} \\
        \ov{\domain{u_E?} \vdash n : \alpha} \\
        \ov{\domain{u_E?} \vdash u_s : S} \\
        \ov{\domain{u_E?} \vdash u_{f,\jmv} : E} \\
        \ov{\models_{\LENV,E,\vartheta} \formula} \\
       }
       {\judg{u_E?}{R}{\ov{\evalsym{\epsilon}{\symbolicterm}{\vartheta}}}{\evalbs{\rulebindspec}{E?,\vartheta}}
       }
     \end{array}
  \]

  \framebox{\mbox{$\models_{\LENV,E,\vartheta} \formula$}} \\
  \[ \begin{array}{c}
     \end{array}
  \]

  \framebox{\mbox{$(n:\ov{v}) \in_{E,\alpha} u$}} \\
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{InHere}]
                 {\ov{\vdash v : T} \\
                  (K : \alpha \cto \ov{T}) \in E
                 }
                 {(0 : \ov{\text{sh}_\alpha~0~v)} \in_{E,\alpha} (K~u_E~\ov{v})} \\\\
     \inferrule* [right=\textsc{InThereHom}]
                 {(n : \ov{v}) \in_{E,\alpha} u_E \\
                  (K : \alpha \cto \ov{T}) \in E \\
                  \ov{\vdash w : T} \\
                 }
                 {(S~n : \ov{\text{sh}_\alpha~0~v}) \in_{E,\alpha} {K~u_E~\ov{w}}} \\\\
     \inferrule* [right=\textsc{InThereHet}]
                 {(n : \ov{v}) \in_{E,\alpha} u_E \\ \alpha \neq \beta \\
                  (K : \beta \cto \ov{T}) \in E \\
                  \ov{\vdash w : T} \\
                 }
                 {(n : \ov{\text{sh}_\beta~0~v} \in_{E,\alpha} {K~u_E~\ov{w}}}
     \end{array}
  \]

  \end{minipage}
}
\end{center}
\caption{\Knot semantics: relation derivations}
\label{fig:derivations}
\end{figure}

Figure \ref{fig:derivations} defines semantics of relations as derivation trees.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
