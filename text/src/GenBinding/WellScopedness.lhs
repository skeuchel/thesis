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

\section{Well-scopedness}\label{sec:wellscopedness}

For user-defined relations with environments we want to generically establish
that a proof of a judgement implies well-scopedness of the sort terms of the
judgement. For example for the typing relation $\Gamma \vdash e : \tau$ from
Section \ref{sec:overview} we want to prove
$$
  \inferrule*[]
    {\Gamma \vdash e : \tau
    }
    {\domain{\Gamma} \vdash e \wedge \domain{\Gamma} \vdash \tau
    }
$$

A proof of this lemma follows by induction on the derivation of the premise and
is accomplished in two steps. First, we establish well-scopedness of the sort
and global meta-variables of the conclusion, potentially by using inversion
lemmas on the induction hypotheses. For example for an application rule
$$
\inferrule*[]
 {\Gamma \vdash e_1 : \tau_1 \to \tau_2 \\
  \Gamma \vdash e_2 : \tau_1
 }
 {\Gamma \vdash e_1~e_2 : \tau_2
 }
$$

we get $(\domain{\Gamma} \vdash e_1)$ and $(\domain{\Gamma} \vdash e_2)$ from
the induction hypotheses, but we still need to invert the hypothesis
$(\domain{\Gamma} \vdash \tau_1 \to \tau_2)$ from the first premise to get
$(\domain{\Gamma} \vdash \tau_2)$.

In some cases, it is impossible to establish well-scopedness from the premises,
e.g. because a meta-variable is not used in the premises or only
appears in non-invertible positions. Then we have to add an extra well-formedness
premises to the judgements.

Second, we use the rules of the well-scopedness relations and derived rules to
establish well-scopedness of the terms in the conclusion, e.g.
$(\domain{\Gamma} \vdash e_1~e_2)$ and $(\domain{\Gamma} \vdash \tau_2)$ for the
application rule. In short, this step amounts to using the fact that
evaluation of well-scoped symbolic expression in a well-scoped context yields
well-scoped terms.

This section wants to establish such well-scopedness lemmas for \Knot's
relational specification generically. These take the form
$$
  \inferrule*[]
  { 0 \vdash u_E : E \\
    \judgsimpl{u_E}{R}{\ov{v}} \\
    (R : E \times \ov{T}) \in \RENV \\
  }
  {\ov{\domain{u_E} \vdash v : T}
  }.
$$

The interesting reasoning happens during the inductive steps, which we
formalize in two stages: First, we elaborate symbolic expressions and one-hole
contexts to a DSL of proof terms for well-scopedness.  Second, we interpret
these proof terms as an axiomatic well-scopedness judgement which we prove
sound with the semantic judgements $(h \vdash_\alpha n)$ and $(h \vdash_S u)$
from Section \ref{sec:terms}.

This approach has two benefits: The elaboration makes the
structure of the proof explicit. Also, the proof term DSL is
independent of an assignment of values to meta-variables (and also independent
of the de Bruijn representation) which makes it clear that all necessary
information is given by the symbolic expressions.

Moreover, because the elaboration function is a key component of \Knot's code
generator \Needle, this gives us a handle on an important part of \Needle's
implementation. We have generically established the correctness of the
elaboration function in \Coq for a simplified (single-variable binding only)
datatype-generic implementation of \Knot \cite{knotneedle} which roughly
translates to an indirect correctness proof of \Needle's implementation of the
elaboration.


%-------------------------------------------------------------------------------
\subsection{Witnesses of Well-scoping}

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.95\columnwidth}
  \vspace{-2mm}
  \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
      wn  & ::=  & \textsc{WN}_H~g~\alpha \mid \textsc{WN}_0~\alpha~\bindspec \mid \textsc{WN}_W~wn~\bindspec \\
          & \mid & \textsc{WN}_T~wn~\bindspec \mid \textsc{WN}_I~K~ws \\
      ws  & ::=  & \textsc{WS}_H~\bindspec~\symbolicterm \mid \textsc{WS}_V~K~wn \mid \textsc{WS}_K K~\ov{ws} \\
          & \mid & \textsc{WS}_I~K~n~ws \mid \textsc{WS}_W~ws~\bindspec \mid \textsc{WS}_T~ws~\bindspec \\
          & \mid & \textsc{WS}_S~ws_1~ws_2 \\
    \end{array}
  \]
  \hrule
  \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lr}
      H   & ::= & \ov{(g : \alpha)}, \ov{([bs]\symbolicterm : S)} & \text{Hypotheses} \\
    \end{array}
  \]
  \small
  \framebox{\mbox{$\wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \hspace{3cm}
     \inferrule*[right=\textsc{WnHyp}]
                 {(g:\alpha) \in H}
                 {\wnindex
                    {H}{h_0}
                    {\textsc{WN}_H~r}
                    {h_0}
                    {\vartheta}{\vartheta~g}{\alpha}
                 } \\\\
     \inferrule*[right=\textsc{WnInvVar}]
                 {K : \alpha \rightarrow S \\\\
                  \wsterm{H}{h_0}{ws}{h}{\vartheta}{K~n}{S}
                 }
                 {\wnindex{H}{h_0}{\textsc{WN}_I~K~ws}{h}{\vartheta}{n}{\alpha}}
     \end{array}
  \]

  \framebox{\mbox{$\wsterm{H}{h_0}{ws}{h}{\vartheta}{u}{S}$}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \hspace{3cm}
     \inferrule*[right=\textsc{WsVar}]
       {K : \alpha \rightarrow S \\\\
        \wnindex{H}{h_0}{wn}{h}{\vartheta}{n}{\alpha}
       }
       {\wsterm{H}{h_0}{\textsc{WS}_V~K~wn}{h}{\vartheta}{K~n}{S}} \\\\

     \inferrule*[right=\textsc{WsSubst}]
       {\wsterm{H}{h_0}{ws1}{h}{\vartheta}{u1}{S1} \\\\
        \wsterm{H}{h_0}{ws2}{S_\alpha~h}{\vartheta}{u2}{S2}
       }
       {\wsterm
           {H}{h_0}{\textsc{WS}_S~ws1~ws2}{h}{\vartheta}
           {\text{su}_\alpha~0~u1~u2}{S2}
       } \\\\

    \inferrule*[right=\textsc{WsStr}]
       {\wsterm
          {H}{h_0}
          {ws}
          {h + \evalbs{\bindspec}{\vartheta}}
          {\vartheta}
          {\shstar~u~\evalbs{\bindspec}{\vartheta}}
          {S}
       }
       {\wsterm{H}{h_0}{\textsc{WS}_T~ws~\bindspec}{h}{\vartheta}{u}{S}
       }
     \end{array}
  \]
  \vspace{-2mm}
  \end{minipage}
}
\end{center}
\caption{Well-scopedness proof terms}
\label{fig:wellscopednessproofterms}
\end{figure}

Figure \ref{fig:wellscopednessproofterms} (top) defines the language of proof
terms targetted by the elaboration, and Figure
\ref{fig:wellscopednessproofterms} (bottom) contains selected rules that define
the intended meaning of the proof terms with respect to the de Bruijn
representation. (See Appendix
\ref{appendix:elaboration} for the remainder.)

The interpretation is relative to a fixed local environment
$\LENV = \ov{(r@@\alpha)}, \ov{([\bindspec_b]b : \beta)}, \ov{[\bindspec_t]t :
  T}$ and also fix a value environment
$\vartheta = \ov{(r \mapsto n)}, \ov{(t \mapsto u)}$. Furthermore, we use an
environment $H$ to hold hypotheses, which we get either from the induction or
from additional well-formedness annotations. An additional parameter is $h_0$
that represents an outer scope which in our case is the domain of the
environment term $h_0 = \domain{u_E}$.

The relation $\wnindex{H}{h_0}{wn}{h}{\vartheta}{\alpha}{n}$ denotes that $wn$
witnesses that $n$ is a well-scoped de Bruijn index for namespace $\alpha$ with
respect to $h$ and $\wsterm{H}{h_0}{ws}{h}{\vartheta}{u}{S}$ denotes that $ws$
witnesses that $u$ is a well-scoped in the de Bruijn term of sort $S$ with
respect to $h$. These two relations are mutually-recursive and completely syntax
directed in $wn$ respectively $ws$.

The rules \textsc{WnHyp} refers to hypotheses in $H$. The hypothesis for a
global variable $g$ represents the assumption that the de Bruijn index
$\vartheta~g$ is well-scoped in the outer scope $h_0$. The remaining rules
axiomatically encode properties of well-scopedness relations. For example, rule
\textsc{WsVar} corresponds to the variable rule of semantic well-scoping and
\textsc{WnInvVar} to its inversion, i.e. we can establish the well-scopedness of
a de Bruijn index from the well-scopedness of a variable constructor. Rule
\textsc{WsSubst} denotes the substitution lemma for well-scoping and
\textsc{WsStr} an inversion of the weakening lemma which is possible because
$\shstar$ on terms is injective.

The axiomatic rules are backed by concreted lemmas for well-scoping, hence we
can establish soundness.

\begin{lem}[Soundness]
  Let $\vartheta = \ov{(r \mapsto n)}, \ov{(t \mapsto u)}$ and
  $\ov{r'} \subseteq \ov{r}$. If the hypotheses
  $H = \ov{(r':\alpha)}, \ov{([\bindspec]sym:S)}$ are valid, i.e.
  $\ov{h_0 \vdash_\alpha \vartheta~r'}$ and \\
  $\ov{h_0 + \evalbs{\bindspec}{\vartheta} \vdash_S \evalsym{\bindspec}{\symbolicterm}{\vartheta}}$,
  then
  \begin{enumerate}
  \item $\forall wn, n', \beta. \wnindex{H}{h_0}{wn}{h}{\vartheta}{n'}{\beta} \Rightarrow  h \vdash_\beta n'$ and
  \item $\forall ws, u', T'. \wsterm{H}{h_0}{ws}{h}{\vartheta}{u'}{T'} \Rightarrow h \vdash_{T'} u'$.
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

\subsection{Well-scopedness Elaboration}

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
\begin{center}
\fbox{
  \begin{minipage}{0.95\columnwidth}
  \begin{code}
    box (symwnα : bs → b → wn)
    symwnα (bs,x,bs') x  = wnW (wn0 α bs) bs'

    box (symws : P → bs → sym → ws)
    symws P bs s = ws  where (s:ws) ∈ P
    symws P bs (K r) = wsV K (wnW wn bs)
      where (r:wn) ∈ P
    symws P bs (K b) = wsV K (symwnα bs b)
      where K : α → S
    symws P bs (K (overline b') (overline sym)) = wsK K (overline ((symws P bs' sym)))
      where  K : (bindspec bs_b b : α) → (bindspec bs_t t : T) → S
             (overline (evalbig (overline (b ↦ b'), overline (t ↦ sym)) bs_t bs'))
    symws P (bs,bs') (weaken sym bs') =
      wsW (symws P bs sym) bs'
    symws P bs (subst b sym1 sym2) =
      wsS (symws P bs sym1) (symws P (bs,b) sym2)
    \end{code}
  \vspace{-5mm}
  \end{minipage}
}
\end{center}
\caption{Well-scopedness of de Bruijn terms}
\label{fig:wellscopednesselaboration}
\end{figure}

For the elaboration we discuss the second step first. Figure
\ref{fig:wellscopednesselaboration} contains the elaboration function from
symbolic expressions to our proof term DSL. The argument $P$ is an environment
that holds proof terms for all sort and global meta-variables, which we get from
the first step of the proof, and the $\bindspec$ argument is the local scope of
the symbolic expressions that is elaborated. In case of a sort meta-variable or
a variable constructor with a global variable we look up the proof term in $P$.
For the global variable we additionally need to weaken to the local scope first
via $\textsc{WN}_W~wn~\bindspec$ and wrap it in the variable constructor with
$\textsc{WS}_V~K$. For a locally bound variable $b$ the helper function
$\text{symwn}_\alpha~bs~b$ first uses $\textsc{WN}_0~\alpha~\bindspec$ to
witness the fact that $b$ is well-scoped in $\bindspec,b$ and then weakens with
the difference $\bindspec'$ to create a proof term for well-scopedness in
$\bindspec,b,\bindspec'$. |symws| then wraps the result in a variable
constructor with $\textsc{WS}_V~K$. For a regular constructor $K$ we
symbolically evaluate the local scopes of the sort fields and proceed
recursively and wrap the results in a $\textsc{WS}_K~K$. In case of a symbolic
weakening we need to strip off the tail $bs'$ to get the local scope for the
recursive position. Finally, for $subst~b~sym_1~sym_2$
we recurse into $sym_1$ with the same local scope but account for the additional
variable $b$ when recursing into $sym_2$.

Given proof terms $P$ for the well-scopedness of global respectively sort
meta-variables the elaboration function $\text{symws}$ constructs a proof term
for the well-scopedness of any symbolic expression.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% TeX-command-default: "Make"
%%% End:
