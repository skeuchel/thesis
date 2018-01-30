%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%format (box (stuff)) = "\hspace{-1em}\framebox{\mbox{\ensuremath{" stuff "}}}"
%format (evalsym (bs) sym th) = "\llbracket\: {" bs "} \mid {" sym "} \:\rrbracket_{" th "}"
%format (mathit x)    = "\mathit{" x "}"
%format ci      = c  "_" i
%format ki      = k  "_" i
%format mi      = m  "_" i
%format si      = s  "_" i
%format ti      = t  "_" i
%format (sub (s)) = "_{" s "}"

%format  wn0   =   "\text{wn}_0"
%format  wnI   =   "\text{wn}_I"
%format  wnT   =   "\text{wn}_T"
%format  wnW   =   "\text{wn}_W"
%format  wsI   =   "\text{ws}_I"
%format  wsK   =   "\text{ws}_K"
%format  wsS   =   "\text{ws}_S"
%format  wsT   =   "\text{ws}_T"
%format  wsV   =   "\text{ws}_V"
%format  wsW   =   "\text{ws}_W"

\section{Well-Scopedness}\label{sec:elab:wellscopedness}

{ % FEXISTSPROD SCOPE
\input{src/MacrosFExists}

In this section, we develop a proof elaboration of well-scopedness lemmas
for user defined relations. Similar to the previous section, we begin
by giving a semi-formal overview of the proof steps before developing
a formal elaboration.

The well-scopedness lemmas state that indices of relations with environments are
well-scoped in the domain of the environment. For example for the formalized
typing relation $\typing{\Gamma}{e}{\tau}$ of \fexistsprod{} from the Overview
Section \ref{sec:formalization} we want to prove the following two
well-scopedness lemmas
\[
  \inferrule*[]
     { \wellscoped{}{E} \\
     \typing{E}{t}{T}
     }
     { \wellscopedterm{E}{t}
     } \qquad
  \inferrule*[]
     { \wellscoped{}{E} \\
     \typing{E}{t}{T}
     }
     { \kinding{E}{T}
     }
\]

Both lemmas are proved by induction of the typing derivation and the induction
steps basically boil down to proving that the expressions in the conclusion of a
rule are well-scoped assuming that the expressions in the premises are
well-scoped. Consider the typing rule for type application of \fexistsprod{}

\[ \inferrule* [right=\textsc{TTApp}]
     {\typing{E}{t}{\forall\bullet.T} \\
      \kinding{E}{S}
     }
     {\typing{E}{(\tapp{e}{S})}{(\suty~0~S~T)}}
\]

To prove that the type $(\suty~0~S~T)$ of the conclusion is well-scoped we have
to use the substitution lemma for well-scopedness of types. This still leaves us
with the obligation to prove that the types represented by the meta-variables
$S$ and $T$ are well-scoped. The well-scopedness of $S$ is given by the second
premise. The induction hypothesis for the first premise gives us the
well-scopedness of $(\forall\bullet.T)$. By inversion of the well-scopedness
rule for universal quantification we can conclude that $T$ is well-scoped.

} % FEXISTSPROD SCOPE

The next two sections develop the formal elaboration of the inductive steps.
Section \ref{ssec:elab:wellscoped:witnesses} presents the domain-specific
witness language and Section \ref{ssec:elab:wellscoped:elabfuncs} presents
the elaboration function from symbolic expressions to witnesses.

%-------------------------------------------------------------------------------
\subsection{Witnesses of Well-Scoping}\label{ssec:elab:wellscoped:witnesses}

%format ws1
%format ws2

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
    \vspace{-2mm}
    \[ \begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
        wn  & ::=  & |hyp g α| \mid |local α bs| \mid |weaken wn bs| \mid |strengthen wn bs| \mid |varinv K ws| \\
        ws  & ::=  & |hyp bs sym| \mid |var K wn| \mid |reg K (overline ws)| \mid |reginv K n ws| \\
            & \mid & |weaken ws bs| \mid |strengthen ws bs| \mid |subst ws1 ws2| \\
        H   & ::=  & \ov{(g : \alpha)}, \ov{([bs]\symbolicterm : S)} \\
      \end{array}
    \]
    \end{minipage}
  }
  \caption{Well-Scopedness Witness DSL}
  \label{fig:elab:wellscopednesswitness:grammar}
\end{figure}

Figure \ref{fig:elab:wellscopednesswitness:grammar} defines the grammar of the
witnesses for indices |wn| and for terms of sorts |ws| which are mutually
recursive. The interpretation witnesses is relative to a fixed rule local
environment $\LENV = \ov{(r@@\alpha)}, \ov{([\bindspec_b]b : \beta)},
\ov{[\bindspec_t]t : T}$ and also a fixed value environment $\vartheta = \ov{(r
  \mapsto n)}, \ov{(t \mapsto u)}$. Furthermore, we use an environment $H$ to
hold hypotheses, which is populated from both the induction hypotheses of the
rule and from well-scopedness premises. The witnesses describe the use of a
hypothesis |hyp|, the well-scopedness of a local reference |local|, the
application of a constructor rule |var| or |reg|, the inversion of a constructor
rule |varinv| or |reginv|, use of a weakening lemma |weaken| or of a
strengthening lemma |strengthen| (the inversion of weakening), or use of a
substitution lemma |subst|.

Figure \ref{fig:wellscopednessproofterms} contains selected rules that define
the intended meaning of the proof terms with respect to the de Bruijn
representation. (See Appendix \ref{appendix:elaboration} for the remainder.) The
relation $\wnindex{H}{h_0}{wn}{h}{\vartheta}{\alpha}{n}$ denotes that $wn$
witnesses that $n$ is a well-scoped de Bruijn index for namespace $\alpha$ with
respect to $h$ and $\wsterm{H}{h_0}{ws}{h}{\vartheta}{u}{S}$ denotes that $ws$
witnesses that $u$ is a well-scoped in the de Bruijn term of sort $S$ with
respect to $h$. These two relations are mutually-recursive and completely syntax
directed in $wn$ respectively $ws$.

Also note, that both relations are parameterized by $H, \vartheta$ and $h_0$, an
additional parameter that represents the outer scope, i.e. the domain of the
implicit environment during the proof of the well-scopedness lemma. The binding
specification in the witness terms always denote the local scope relative to the
outer scope $h_0$.

The rule \textsc{WnHyp} refers to hypotheses in $H$. The hypothesis for a global
variable $g$ represents the assumption that the de Bruijn index $\vartheta~g$ is
well-scoped in the outer scope $h_0$. The remaining rules axiomatically encode
properties of well-scopedness relations. For example, rule \textsc{WsVar}
corresponds to the variable rule of semantic well-scoping and \textsc{WnInvVar}
to its inversion, i.e. we can establish the well-scopedness of a de Bruijn index
from the well-scopedness of a variable constructor. Rule \textsc{WsSubst}
denotes the substitution lemma for well-scoping, and \textsc{WsStrength} denotes
the strengthening lemma, i.e. an inversion of the weakening lemma.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
    \framebox{\mbox{$\wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}$}} \\
    \[ \begin{array}{c}
       \inferrule*[right=\textsc{WnHyp}]
                   {(g:\alpha) \in H}
                   {\wnindex
                      {H}{h_0}
                      {|hyp g α|}
                      {h_0}
                      {\vartheta}{\vartheta~g}{\alpha}
                   } \\\\
       \inferrule*[right=\textsc{WnVarInv}]
                   {K : \alpha \rightarrow S \\
                    \wsterm{H}{h_0}{ws}{h}{\vartheta}{K~n}{S}
                   }
                   {\wnindex{H}{h_0}{|varinv K ws|}{h}{\vartheta}{n}{\alpha}}
       \end{array}
    \]

    \framebox{\mbox{$\wsterm{H}{h_0}{ws}{h}{\vartheta}{u}{S}$}} \\
    \[ \begin{array}{c}
       \inferrule*[right=\textsc{WsVar}]
         {K : \alpha \rightarrow S \\
          \wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}
         }
         {\wsterm{H}{h_0}{|var K wn|}{h}{\vartheta}{K~n}{S}} \\\\

       \inferrule*[right=\textsc{WsSubst}]
         {\wsterm{H}{h_0}{ws_1}{h}{\vartheta}{u_1}{S_1} \\
          \wsterm{H}{h_0}{ws_2}{S_\alpha~h}{\vartheta}{u_2}{S_2}
         }
         {\wsterm
             {H}{h_0}{|subst ws1 ws2|}{h}{\vartheta}
             {\text{subst}_\alpha~0~u_1~u_2}{S_2}
         } \\\\

      \inferrule*[right=\textsc{WsStrengthen}]
         {\wsterm
            {H}{h_0}
            {ws}
            {h + \evalbs{\bindspec}{\vartheta}}
            {\vartheta}
            {|lift|~u~\evalbs{\bindspec}{\vartheta}}
            {S}
         }
         {\wsterm{H}{h_0}{|strengthen ws bs|}{h}{\vartheta}{u}{S}
         }
       \end{array}
    \]
    \end{minipage}
  }
  \caption{Well-scopedness proof terms}
  \label{fig:wellscopednessproofterms}
\end{figure}

Since the axiomatic rules of the witness language are backed by concreted lemmas
for well-scoping, we can establish soundness of the interpretation

\begin{lem}[Soundness]
  Let $\vartheta = \ov{(g \mapsto n)}, \ov{(t \mapsto u)}$ and $\ov{g'}
  \subseteq \ov{g}$. If the hypotheses $H = \ov{(g':\alpha)},
  \ov{([\bindspec]sym:S)}$ are valid, i.e. $\ov{h_0 \vdash_\alpha \vartheta~g'}$
  and \\ $\ov{h_0 + \evalbs{\bindspec}{\vartheta} \vdash_S
    \evalsym{\bindspec}{\symbolicterm}{\vartheta}}$, then

  \begin{enumerate}
  \item
    \[ \inferrule*[]
         {\wnindex{H}{h_0}{wn}{h}{\vartheta}{n'}{\beta}}
         {h \vdash_\beta n'}
    \]
  \item
    \[ \inferrule*[]
         {\wsterm{H}{h_0}{ws}{h}{\vartheta}{u'}{T'}}
         {h \vdash_{T'} u'}
    \]
  \end{enumerate}
\end{lem}

%% $$
%% \inferrule*[]
%%  {
%%   \vartheta = \ov{(r \mapsto n)}, \ov{(t \mapsto u)} \\
%%   \ov{r'} \subseteq \ov{r} \\
%%   \ov{h_0 \vdash \vartheta~r' : \alpha} \\
%%   \ov{h_0 + \evalbs{\bindspec}{\vartheta} \vdash \evalsym{\bindspec}{\symbolicterm}{\vartheta} : S} \\
%%   \wnindex
%%     {H}{h_0}
%%     {wn}
%%     {h}
%%     {\vartheta}{n}{\alpha}
%%  }
%%  {h \vdash n : \alpha
%%  }
%% $$
%%
%% $$
%% \inferrule*[]
%%  {H = \ov{(r':\alpha)}, \ov{([\bindspec]sym:S)} \\
%%   \vartheta = \ov{(r \mapsto n)}, \ov{(t \mapsto u)} \\
%%   \ov{r'} \subseteq \ov{r} \\
%%   \ov{h_0 \vdash \vartheta~r' : \alpha} \\
%%   \ov{h_0 + \evalbs{\bindspec}{\vartheta} \vdash \evalsym{\bindspec}{\symbolicterm}{\vartheta} : S} \\
%%   \wsterm
%%     {H}{h_0}
%%     {ws}
%%     {h}
%%     {\vartheta}{u}{T}
%%  }
%%  {h \vdash u : T
%%  }
%% $$

%-------------------------------------------------------------------------------

\subsection{Proof Elaboration}\label{ssec:elab:wellscoped:elabfuncs}

We can split the proof of the induction steps of the lemma into two stages.
First, we establish well-scopedness of terms represented by sort and global
meta-variables of the conclusion, potentially by using inversion lemmas on the
induction hypotheses. Second, we use the rules of the well-scopedness relations
and derived rules to establish well-scopedness of the terms in the conclusion.
In short, this step amounts to using the fact that evaluation of well-scoped
symbolic expression in a well-scoped context yields well-scoped terms.

Similarly, we can also split the elaboration into two corresponding stages. The
first stage elaborates one-hole contexts \cite{huet1997zipper} that describe
invertible paths to meta-variable in the premises into witnesses that use
inversions and hypotheses. We collect the result of the first stage into an
environment $P ::= \ov{g:wn}, \ov{s:ws}$ that holds the proof terms for the
meta-variables. The second stage elaborates the expression in the conclusion
into witness terms by using $P$ for occurring meta-variables.

%if False
The definition with correct associativity would be

symwnα (bs, bα)   bα = wn0 α bs
symwnα (bs, bβ)   bα = wnW (symwnα bs x) bβ
symwnα (bs, f s)  bα = wnW (symwnα bs x) (f s)
%endif

%format (evalbig theta bs1 bs2) = "\evalbig{" theta "}{" bs1 "}{" bs2 "}"
%format bs_b = "\bindspec_b"
%format bs_t = "\bindspec_t"
%format symwnα = "\text{symwn}_{\alpha}"
%format symws  = "\text{symws}"
%format sym1
%format sym2

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.95\columnwidth}
    \begin{code}
      box (symwnα : bs → b → wn)
      symwnα (bs,b,bs') b = weaken (local α bs) bs'

      box (symws : P → bs → sym → ws)
      symws P bs s = ws  where (s:ws) ∈ P
      symws P bs (K g) = var K (weaken wn bs)
        where (g:wn) ∈ P
      symws P bs (K b) = var K (symwnα bs b)
        where K : α → S
      symws P bs (K (overline b') (overline sym)) = reg K (overline ((symws P bs' sym)))
        where  K : (bindspec bs_b b : α) → (bindspec bs_t t : T) → S
               (overline (evalbig (overline (b ↦ b'), overline (t ↦ sym)) bs_t bs'))
      symws P (bs,bs') (weaken sym bs') =
        weaken (symws P bs sym) bs'
      symws P bs (subst b sym1 sym2) =
        subst (symws P bs sym1) (symws P (bs,b) sym2)
      \end{code}
    \end{minipage}
  }
  \caption{Well-scopedness of de Bruijn terms}
  \label{fig:wellscopednesselaboration}
\end{figure}

We only present the formal elaboration of the second stage. Figure
\ref{fig:wellscopednesselaboration} contains the elaboration function |symws|
from symbolic expressions to witnesses |ws|. The argument $P$ is the proof term
environment for sort and global meta-variables, and the $\bindspec$ argument is
the local scope of the symbolic expressions that is elaborated.

In case of a sort meta-variable or a variable constructor with a global variable
we look up the proof term in $P$. For the global variable we need to weaken to
the local scope first and then wrap it in the variable constructor. For a
locally bound variable $b$ the helper function $\text{symwn}_\alpha$ first uses
$|local|$ to witness the fact that $b$ is well-scoped in $\bindspec,b$ and then
weakens with the difference $\bindspec'$ to create a proof term for
well-scopedness in $\bindspec,b,\bindspec'$\footnote{For simplicity, the
  presented elaborations in Figure \ref{fig:wellscopednesselaboration} have the
  wrong associativity when weakening local and global meta-variables into the
  local scope. \Loom and \Needle contain elaborations that deal with associativity
  correctly.}.

For a regular constructor $K$ we symbolically evaluate the local scopes of the
sort fields and proceed recursively and wrap the results in |reg|. In case of a
symbolic weakening we need to strip off the tail $bs'$ to get the local scope
for the recursive position. Finally, for $subst~b~sym_1~sym_2$ we recurse into
$sym_1$ with the same local scope but account for the additional variable $b$
when recursing into $sym_2$.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% TeX-command-default: "Make"
%%% End:
