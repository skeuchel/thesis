%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\section{Appendix C}\label{appendix:elaboration}

\subsection{Well-scoping proof terms}

\begin{figure}[t]
\begin{center}
\fbox{\small
  \begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$\wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}$}} \\
  \[ \begin{array}{c}
     \inferrule*[right=\textsc{WnHyp}]
                 {(g:\alpha) \in H}
                 {\wnindex
                    {H}{h_0}
                    {\textsc{WN}_H~g}
                    {h_0}
                    {\vartheta}{\vartheta~g}{\alpha}
                 } \\\\
     \inferrule*[right=\textsc{WnZero}]
                 {\,}
                 {\wnindex
                    {H}{h_0}
                    {\textsc{WN}_0~\alpha~\bindspec}
                    {S_\alpha(h_0 + \evalbs{bs}{\vartheta})}
                    {\vartheta}{0}{\alpha}
                 } \\\\
     \inferrule*[right=\textsc{WnWeak}]
                 {\wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}
                 }
                 {\wnindex
                    {H}{h_0}
                    {\textsc{WN}_W~wn~bs}{h + \evalbs{bs}{\vartheta}}{\vartheta}
                    {\text{wk}_\alpha~n~\evalbs{bs}{\vartheta}}
                    {\alpha}
                 } \\\\
     \inferrule*[right=\textsc{WnStr}]
                 {\wnindex
                    {H}{h_0}
                    {wn}{h + \evalbs{bs}{\vartheta}}
                    {\vartheta}{\text{wk}_\alpha~n~\evalbs{bs}{\vartheta}}
                    {\alpha}
                 }
                 {\wnindex{H}{h_0}{\textsc{WN}_S~wn~bs}{h}{\vartheta}{n}{\alpha}
                 } \\\\
     \inferrule*[right=\textsc{WnInvVar}]
                 {K : \alpha \rightarrow S \\\\
                  \wsterm{H}{h_0}{ws}{h}{\vartheta}{K~n}{S}
                 }
                 {\wnindex{H}{h_0}{\textsc{WN}_I~K~ws}{h}{\vartheta}{n}{\alpha}}
     \end{array}
  \]

  \framebox{\mbox{$\wsterm{H}{h_0}{ws}{h}{\vartheta}{u}{S}$}} \\
  \[ \begin{array}{c}
     \inferrule*[right=\textsc{WsHyp}]
                 {([\bindspec]\symbolicterm : S) \in H}
                 {\wsterm
                    {H}{h_0}
                    {\textsc{WS}_H~\bindspec~\symbolicterm~S}
                    {h_0 + \evalbs{\bindspec}{\vartheta}}
                    {\vartheta}{|evalsym bs sym ϑ|}{S}
                 } \\\\
     \inferrule*[right=\textsc{WsVar}]
       {K : \alpha \rightarrow S \\\\
        \wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}
       }
       {\wsterm{H}{h_0}{\textsc{WS}_V~K~wn}{h}{\vartheta}{K~n}{S}} \\\\

     \inferrule*[right=\textsc{WsReg}]
       {K : \ov{b : \alpha} \to \ov{[bs] t : T} \to S \\\\
        \vartheta' = \ov{t \mapsto u} \\\\
        \wsterm
           {H}{h_0}
           {\textsc{WS}_i}
           {h + \evalbs{\bindspec_i}{\vartheta'}}
           {\vartheta}{u_i}{T_i}  \quad (\forall i)
       }
       {\wsterm{H}{h_0}{\textsc{WS}_K~K~\ov{ws}}{h}{\vartheta}{K~\ov{u}}{S}} \\\\

     \inferrule*[right=\textsc{WsInvReg}]
       {K : \ov{b : \alpha} \to \ov{[bs] t : T} \to S \\\\
        \vartheta' = \ov{t \mapsto u} \\\\
        \wsterm{H}{h_0}{ws}{h}{\vartheta}{K~\ov{u}}{S}}
       {\wsterm
           {H}{h_0}
           {\textsc{WS}_I~K~i~ws}
           {h + \evalbs{\bindspec_i}{\vartheta'}}
           {\vartheta}{u_i}{T_i}
       } \\\\

     \inferrule*[right=\textsc{WsWeak}]
       {\wsterm{H}{h_0}{ws}{h}{\vartheta}{u}{S}}
       {\wsterm
          {H}{h_0}
          {\textsc{WS}_W~ws~bs}
          {h + \evalbs{\bindspec}{\vartheta}}
          {\vartheta}
          {\text{wk}~u~\evalbs{\bindspec}{\vartheta}}
          {S}
       } \\\\

     \inferrule*[right=\textsc{WsStr}]
       {\wsterm
          {H}{h_0}
          {ws}
          {h + \evalbs{\bindspec}{\vartheta}}
          {\vartheta}
          {\text{wk}~u~\evalbs{\bindspec}{\vartheta}}
          {S}
       }
       {\wsterm{H}{h_0}{\textsc{WS}_T~ws~\bindspec}{h}{\vartheta}{u}{S}
       } \\\\

     \inferrule*[right=\textsc{WsSubst}]
       {\wsterm{H}{h_0}{ws1}{h}{\vartheta}{u1}{S1} \\\\
        \wsterm{H}{h_0}{ws2}{S_\alpha~h}{\vartheta}{u2}{S2}
       }
       {\wsterm
           {H}{h_0}{\textsc{WS}_S~ws1~ws2}{h}{\vartheta}
           {\text{su}_\alpha~0~u1~u2}{S2}
       } \\\\
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Well-scoping proof term interpretation}
\label{fig:wellscopingproofterms}
\end{figure}

Figure \ref{fig:wellscopingproofterms} gives the full interpretation
of well-scoping proof terms.

\begin{lem} The syntax-directed elaboration is correct, i.e.
$$
\inferrule*[]
 {%% \LENV = \ov{(r@@\alpha)}, \ov{([\bindspec_b]b : \beta)}, \ov{[\bindspec_t]t : T} \\
  %% \wfbindspec{\epsilon}{\bindspec}{} \\
  %% \vartheta = \ov{(r \mapsto n)}, \ov{(t \mapsto u)} \\
  \wfsym{\bindspec}{\symbolicterm}{S} \\
  \wnindex{H}{h_0}{wn}{h_0}{\vartheta}{n}{\alpha} \\
  \wsterm{H}{h_0}{ws}{h_0 + \evalbs{\bindspec_t}{\vartheta}}{\vartheta}{u}{T} \\
  P = \ov{\ov{(r:wn), (t:ws)}}
 }
 {\wsterm{H}{h_0}{\text{symws}~P~\bindspec~\symbolicterm}
    {h_0 + \evalbs{\bindspec}{\vartheta}}{\vartheta}
    {\evalsym{\bindspec}{\symbolicterm}{\vartheta}}{S}
 }
$$
\end{lem}

\begin{cor}[Well-scoped evaluation]
$$
\inferrule*[]
 {%% \LENV = \ov{(r@@\alpha)}, \ov{([\bindspec_b]b : \beta)}, \ov{[\bindspec_t]t : T} \\
  %% \wfbindspec{\epsilon}{\bindspec}{} \\
  %% \vartheta = \ov{(r \mapsto n)}, \ov{(t \mapsto u)} \\
  \wfsym{\bindspec}{\symbolicterm}{S} \\
  h_0 \vdash n : \alpha \\
  h_0 + \evalbs{\bindspec_t}{\vartheta} \vdash u : T
 }
 {h_0 + \evalbs{\bindspec}{\vartheta} \vdash
  \evalsym{\bindspec}{\symbolicterm}{\vartheta} : S
 }
$$
\end{cor}

%% \subsection{Well-scoped expression contexts}
%%
%% It remains to construct $E$ from the hypotheses $H$. In case we have a
%% well-formedness hypotheses added to the rule we can simply use these with
%% $\text{wn}_H$ or $\text{ws}_H$. Otherwise we have for a sort variable $t$ an
%% expression context $\symboliccoterm_t$ such that
%% $([\bindspec] (\symboliccoterm_t\llbracket t \rrbracket) : S) \in H$ in which
%% case
%%
%% $$\textsc{WS}_t := cosymws~(\text{ws}_H~\bindspec~(\symboliccoterm_t \llbracket t
%% \rrbracket))~\symboliccoterm_t~S$$ witnesses well-scopedness of
%% $\vartheta~t$. Similarly, for a free variable $r$ we have an expression context
%% $\symboliccoterm_r$ such that
%% $([\bindspec] (\symboliccoterm_t\llbracket K~r \rrbracket) : S') \in H$ and
%%
%% $$\textsc{WN}_r := \text{wn}_I~K~(cosymws~(\text{ws}_H~\bindspec~(\symboliccoterm_r
%% \llbracket K~r \rrbracket))~\symboliccoterm_r~S')$$
%% witnesses well-scopedness of
%% $\vartheta~r$.  Similar to the correctness proof of $symws$ we can proof that
%% $cosymws$ is correct.
%%
%% \begin{figure}[t]
%% \begin{center}
%% \fbox{
%%   \begin{minipage}{0.95\columnwidth}
%%   \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
%%       \symboliccoterm & ::=  & \bullet \mid K~\ov{b}~\ov{\symbolicterm}~\symboliccoterm~\ov{\symbolicterm} \\
%%                       & \mid & \symboliccoweaken~\symboliccoterm~\bindspec
%%     \end{array}
%%   \]
%%   \end{minipage}
%% }
%% \end{center}
%% \caption{Grammar of symbolic expression contexts}
%% \label{fig:grammarsymboliccoterms}
%% \end{figure}
%%
%%
%%
%%
%% \begin{figure}[t]
%% \begin{center}
%% \fbox{
%%   \begin{minipage}{0.95\columnwidth}
%%     %% box (plug : sym → cosym →ws)
%%     %% plug sym  •  = sym
%%     %% plug sym  (K (overline b) (overline sym1) cosym (overline sym2)) =
%%     %%   K (overline b) (overline sym1) (plug sym cosym) (overline sym2)
%%     %% plug sym  (coweaken cosym bs) =
%%     %%   weaken (plug sym cosym) bs
%%     \begin{code}
%%     box (cosymws : ws → cosym → ws)
%%     cosymws ws  • = ws
%%     cosymws ws  (K (overline b) (overline sym1) cosym (overline sym2)) =
%%       wsI K (length ((overline sym1))) (cosymws ws cosym)
%%     cosymws ws  (coweaken cosym bs) =
%%       wsT (cosymws ws cosym) bs
%%     \end{code}
%%   \end{minipage}
%% }
%% \end{center}
%% \caption{Symbolic expression contexts}
%% \label{fig:elabsymboliccoterm}
%% \end{figure}
%%
%% \begin{figure}[t]
%% \begin{center}
%% \fbox{
%%   \begin{minipage}{0.95\columnwidth}
%%   \framebox{\mbox{$\wfsym{\bindspec\to\bindspec}{\symboliccoterm}{T \to S}$}} \\
%%   \[ \begin{array}{c}
%%
%%      \inferrule* [right=\textsc{CoSymHole}]
%%        {\,}
%%        {\wfsym{\bindspec\to\bindspec}{\bullet}{S \to S}
%%        } \\\\
%%
%%      \inferrule* [right=\textsc{CoSymReg}]
%%        {K : (\ov{[\bindspec_x]x:\alpha}) \to
%%             (\ov{[\bindspec_t]t:T}) \to S \\
%%         \TODO{How should this work??}
%%        }
%%        {\wfsym
%%           {{\color{red}??}\to\bindspec_2}
%%           {K~\ov{b}~\ov{\symbolicterm_1}~\symboliccoterm~\ov{\symbolicterm_2}}
%%           {T \to S}
%%        } \\\\
%%
%%      \inferrule* [right=\textsc{CoSymWeaken}]
%%        {\wfsym{\bindspec_1\to\bindspec_2,\bindspec'}{\symboliccoterm}{T \to S}
%%        }
%%        {\wfsym{\bindspec_1\to\bindspec_2}{\symboliccoweaken~\symboliccoterm~\bindspec'}{T \to S}
%%        } \\\\
%%
%%      %% \inferrule* [right=\textsc{SymWeaken}]
%%      %%   {\wfsym{\bindspec}{\symbolicterm}{S}
%%      %%   }
%%      %%   {\wfsym{\bindspec, \bindspec'}{\symbolicweaken~\symbolicterm~\bindspec'}{S}
%%      %%   } \\\\
%%      %% \inferrule* [right=\textsc{SymSubst}]
%%      %%   {([\bindspec]x:\alpha) \in \LENV \\ (\alpha:T) \in \VENV \\
%%      %%    \wfsym{\bindspec}{\symbolicterm_1}{T} \\
%%      %%    \wfsym{\bindspec, x}{\symbolicterm_2}{S}
%%      %%   }
%%      %%   {\wfsym{\bindspec}{\symbolicsubst~x~\symbolicterm_1~\symbolicterm_2}{S}
%%      %%   } \\
%%      \end{array}
%%   \]
%%
%%   \end{minipage}
%% }
%% \end{center}
%% \caption{Well-formed symbolic expression contexts}
%% \label{fig:wellformedsymboliccoterms}
%% \end{figure}


\subsection{Equality witnesses}

Figure \ref{fig:termequalitygrammar} contains the language of equality witnesses
that we are using and Figure \ref{fig:termequalitysemantics} their
interpretation.

%% $(\eqtrefl{\bindspec}{\symbolicterm}{S})$ stands for reflexivity
%% which means that the two evaluations of $\symbolicterm$ are equal. The witness
%% formers $\eqttranscon$ and $\eqtsymcon$ encode transitivity and symmetry.


\begin{figure}[t]
\begin{center}
\fbox{\small
  \begin{minipage}{0.98\columnwidth}
  \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
      qt  & ::=  & \eqtrefl{\bindspec}{\symbolicterm}{S} \mid \eqtsym{qt} \mid \eqttrans{qt}{qt} \\
          & \mid & \eqtreg{K}{\ov{qt}} \mid \eqtshiftweaken{\bindspec} \mid
                   \eqtshiftsubst{} \mid \eqtsubstweaken{} \mid \eqtsubstsubst{}
    \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Grammar of term equality witnesses}
\label{fig:termequalitygrammar}
\end{figure}

\begin{figure}[t]
\begin{center}
\fbox{\small
  \begin{minipage}{0.98\columnwidth}
  \framebox{\mbox{$\eqterm{h}{c}{\vartheta}{qt}{h}{u}{u}{S}$}} \\
  \vspace{-2mm}
  \[ \begin{array}{c}

     \inferrule*[right=Refl]
       {h = \evalbs{\bindspec}{\vartheta} \\
        u = sh~c~\evalsym{\bindspec}{\symbolicterm}{\vartheta} = \evalsym{\bindspec}{\symbolicterm}{(sh_\LENV~c~\vartheta)}
       }
       {\eqterm
          {h_0}{c}{\vartheta}{(\eqtrefl{\bindspec}{\symbolicterm}{S})}
          {h_0 + h}{u}{u}{S}
       } \\\\

     \inferrule*[right=Sym]
       {\eqterm{h_0}{c}{\vartheta}{qt}{h}{u}{v}{S}
       }
       {\eqterm{h_0}{c}{\vartheta}{(\eqtsym{qt})}{h}{v}{u}{S}
       } \\\\

    \inferrule*[right=Trans]
       {\eqterm{h_0}{c}{\vartheta}{qt_1}{h}{u}{v}{S} \\
        \eqterm{h_0}{c}{\vartheta}{qt_2}{h}{v}{w}{S}
       }
       {\eqterm{h_0}{c}{\vartheta}{(\eqttrans{qt_1}{qt_2})}{h}{u}{w}{S}
       } \\\\

     \inferrule*[right=Reg]
       {K : \ov{([\bindspec_b]b : \alpha)} \to \ov{([\bindspec_t] t : T)} \to S \\\\
        \vartheta' = \ov{t \mapsto u} \\\\
        \ov{\eqterm{h_0}{c}{\vartheta}{qt}{h + \evalbs{\bindspec_t}{\vartheta'}}{u}{v}{T}}
       }
       {\eqterm{h_0}{c}{\vartheta}{(\eqtreg{K}{\ov{qt}})}{h}{K~\ov{u}}{K~\ov{v}}{S}
       } \\\\

     \inferrule*[right=CongWeaken]
       {h' = \evalbs{\bindspec}{\vartheta} \\
        \eqterm{h_0}{c}{\vartheta}{qt}{h}{u}{v}{S}
       }
       {\eqterm
          {h_0}{c}{\vartheta}{\eqtcongweaken{qt}{\bindspec}}
          {h+h'}{wk~u~h'}{wk~v~h'}{S}
       } \\\\

     %% \inferrule*[right=CongSubst]
     %%   { \,
     %%   }
     %%   {\eqterm
     %%     {h_0}{c}{\vartheta}{\color{red}{qcu}}
     %%     {h}{}{}{S}
     %%   } \\\\

     \inferrule*[right=ShiftWeaken]
       {h_1 = \evalbs{\bindspec_1}{\vartheta} \\
        h_2 = \evalbs{\bindspec_2}{\vartheta} \\\\
        c_1 = c + h_1 \\
        u_1 = \sh{\alpha}{(\wk{c_1}{h_2})}{(\wk{u}{h_2})} \\
        u_2 = \wk{(\sh{\alpha}{c_1}{u})}{h_2}
       }
       {\eqterm
         {h_0}{c}{\vartheta}{\eqtshiftweaken{\bindspec_1}{\bindspec_2}}
         {h_0 + h_1 + h_2}{u_1}{u_2}{S}
       } \\\\

     \inferrule*[right=ShiftSubst]
       {h = \evalbs{\bindspec}{\vartheta} \\\\
        u_1 = \sh{\alpha}{cα}{(\su{\beta}{0}{u}{v})} \\\\
        u_2 = \su{\beta}{0}{(\sh{\alpha}{c}{u})}{(\sh{\alpha}{(c + 1_\beta)}{v})}
       }
       {\eqterm
          {h_0}{c}{\vartheta}{qhu~\bindspec}
          {h_0 + h}{u_1}{u_2}{S}
       } \\\\

     %% \inferrule*[right=SubstWeaken]
     %%   {h = \evalbs{\bindspec}{\vartheta} \\\\
     %%    u_1 = \su{\alpha}{(\wk{x}{h})}{u}{(\wk{v}{h})} \\\\
     %%    u_2 = \wk{(\su{\alpha}{x}{u}{v})}{h}
     %%   }
     %%   {\eqterm
     %%      {h_0}{c}{\vartheta}{quw~\bindspec}
     %%      {}{u_1}{u_2}{S}
     %%   } \\\\
     %%
     %% \inferrule*[right=SubstSubst]
     %%   {h = \evalbs{\bindspec}{\vartheta} \\\\
     %%    u_1 = \su{\alpha}{x}{u_\alpha}{(\su{\beta}{0}{u_\beta}{v})} \\\\
     %%    u_2 = \su{\beta}{0}{(\su{\alpha}{x}{u_\alpha}{u_\beta})}{(\su{\alpha}{(\wk{x}{1_\beta})}{u_\alpha}{v})}
     %%   }
     %%   {\eqterm
     %%      {h_0}{c}{\vartheta}{quw~\bindspec}
     %%      {}{u_1}{u_2}{S}
     %%   } \\\\

     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Term equality semantics}
\label{fig:termequalitysemantics}
\end{figure}


\subsection{Shift elaboration}

The relation $\eqterm{h_0}{c}{\vartheta}{qt}{h}{u}{v}{S}$ interprets equality
witnesses for the purpose of proving commutation of symbolic evaluation with
shifting. Only proof term formers relevant to this lemma are interpreted. The
cutoff $c$ and the value environment $\vartheta$ are parameters to this
relation.


\begin{lem}[Soundness]
$$
  \inferrule*[]
  {\eqterm{h_0}{c}{\vartheta}{\eqt}{h}{u}{v}{S}
  }
  {u = v
  }
$$
\end{lem}

Figure \ref{fig:shiftcommelablration} shows the elaboration function for the
shift commutation lemma.

\begin{figure}[t]
\begin{center}
\fbox{\small
  \begin{minipage}{0.98\columnwidth}
    \begin{code}
    box (shsym : bs → sym → qt)
    shsym bs s      = qrf bs s
    shsym bs (K r)  = qrf bs (K r)
    shsym bs (K b)  = qrf bs (K b)
    shsym bs (K (overline b) (overline sym)) =
      qcn K (overline (shsym (bs,bs') sym))
      where K : (overline (b':alpha)) -> ([bs']t:T) -> S
    shsym bs (weaken s bs') = qhh bs s bs'
    shsym bs (subst b sym s) = qhu bs sym s
    \end{code}
  \end{minipage}
}
\end{center}
\caption{Shift commutation elaboration}
\label{fig:shiftcommelablration}
\end{figure}



\begin{lem}[Elaboration correctness] The elaboration for the shift commutation
  is correct.
$$
  \inferrule*[]
  {\wfsym{\bindspec}{\symbolicterm}{S} \\
    \eqt = |shsym bs sym| \\
    h = \evalbs{bs}{\vartheta} \\
    u = sh~(c + h)~\evalsym{bs}{\symbolicterm}{\vartheta} \\
    v = \evalsym{bs}{\symbolicterm}{(sh_\LENV~(c + h)~\vartheta)}
  }
  {\eqterm{h_0}{c}{\vartheta}{\eqt}{h_0 + h}{u}{v}{S}
  }
$$
\end{lem}


\begin{cor}\label{cor:shifteval}
$$
  \inferrule*[]
  {\wfsym{\bindspec}{\symbolicterm}{S} \\
    h = \evalbs{\bindspec}{\vartheta}
  }
  {sh~(c+h)~\evalsym{\bindspec}{\symbolicterm}{\vartheta} =
    \evalsym{\bindspec}{\symbolicterm}{(sh_\LENV~c~\vartheta)}
  }
$$
\end{cor}

\paragraph{Lookup premise}
We still need to prove that the premises of rule $r$ hold.  A lookup premise
$\cbrc{x \cto \ov{\symbolicterm}}$ for an environment clause
$\alpha \cto \ov{S}$ gives rise to the proof obligation

$$
  \inferrule*[]
    {(n : \evalsym{bs}{\symbolicterm'}{\vartheta}) \in \Gamma}
    {(sh~c~n : \evalsym{bs}{\symbolicterm'}{sh_\LENV~c~\vartheta}) \in \Gamma}
$$
\noindent which we get from Corollary \ref{cor:shifteval} and by proving
$$
  \inferrule*[]
    {(n : \ov{u}) \in \Gamma, \Delta \\
     c = \domain{\Delta}
    }
    {(sh~c~n : \ov{sh~c~u}) \in \Gamma,\ov{v},\Delta}
$$
\noindent by induction over $\Delta$.

\paragraph{Judgement premise}
A judgement premise $\rulebindspec~\judgement~\ov{\symbolicterm}$
 gives rise to the proof obligation
$$
\Gamma, \ov{v}, \Delta , \evalsym{\epsilon}{rbs}{sh_\LENV~c~\vartheta}
      \vdash_R
      \ov{
        \evalsym
          {\lfloor \rulebindspec \rfloor}
          {\symbolicterm}
          {sh_\LENV~c~\vartheta}
        }
$$
\noindent which we get from the induction hypothesis
$$
 \Gamma, \ov{v}, \Delta, sh~c~\evalsym{\epsilon}{\rulebindspec}{\vartheta}
      \vdash_R
      \ov{sh~(c + \evalbs{\lfloor \rulebindspec \rfloor}{\vartheta})~
        \evalsym
          {\lfloor \rulebindspec \rfloor}
          {\symbolicterm}
          {\vartheta}
        }
$$
and Corollary \ref{cor:shifteval}.



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
