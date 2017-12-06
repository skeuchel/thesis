%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

\section{Interaction Lemmas}\label{sec:elab:interaction}

Formalizations involve a number of interaction boilerplate lemmas between
|shift|, |weaken| and |subst|. These lemmas are for example needed in weakening
and substitution lemmas for typing relations.

In this Section, we develop an syntax-directed elaboration for these lemmas.
Since this class of lemmas state the equality of different applications of
operations, we develop a witness language for term equality of our de Bruijn
representation.

We discuss the two types of interaction lemmas in Section
\ref{ssec:elab:interaction:overview} and develop a semi-formal induction proof
for one of them in Section \ref{ssec:elab:interaction:semiformal}. The formal
witness language is developed in Section \ref{ssec:elab:interaction:witness}.
Finally, the elaboration is presented in Section
\ref{ssec:elab:interaction:elaboration}.


\subsection{Overview}\label{ssec:elab:interaction:overview}

There are two distinct types of interaction lemmas: commutation lemmas and a
cancelation lemma.

\subsubsection{Commutation}\label{ssec:elab:interaction:overview:commutation}
Two operation always commute when they are operating on different variables. For
instance, weakening of terms by introducing two distinct variables $x$ and $y$
%
\[ \Gamma,\Delta_1,\Delta_2 \leadsto \Gamma,x,\Delta_1,y,\Delta_2 \]
%
\noindent can be implemented by 2 consecutive shifts. The order of these shifts
is irrelevant, which we have to prove, i.e. we have the following commuting
diagram:
%
\[ \xymatrixcolsep{5pc}
   \xymatrix{
   |Γ,Δ₁,Δ₂|   \ar[r]^{|shiftβ h₂|}   \ar[d]_{|shiftα (h₁ + h₂)|} & |Γ,Δ₁,y,Δ₂| \ar[d]^{|shiftα (h₁ + Iβ + h₂)|}  \\
   |Γ,x,Δ₁,Δ₂|                   \ar[r]_{|shiftβ h₂|} & |Γ,x,Δ₁,y,Δ₂|
   }
\]
%
\noindent where $h_1 := |dom Δ₁|$ and $h_2 := |dom Δ₂|$, $\alpha$ is the
namespace of $x$, and $\beta$ the namespace of $y$. Usually only the special
case $\Delta_2 \equiv \epsilon$ of this lemma is used. However, for the
induction to go throught the more general case needs to be proved. Also the
lemma can be homogenous, i.e. $\alpha = \beta$, or heterogeneous, i.e. $\alpha
\neq \beta$.

\begin{lem}\label{lem:elab:shiftcomm}
\[ \forall u, h_1, h_2.
     |shiftα (h1 + Iβ + h2) (shiftβ h2 u)| =
     |shiftβ h2 (shiftα (h1 + h2) u)|
\]
\end{lem}

Similar lemmas hold for the commutation of a substitution and a shifting and two
substitutions. Extra care needs to be taken when a substitution is involved,
since the substitute(s) may also need to be changed.

\subsubsection{Cancelation}
When operating on the same variable, a shifting followed by a substitution
cancel each other out:
 $$|substα v 0α (shiftα 0α u) = u|.$$


\subsection{Semi-formal Proofs}\label{ssec:elab:interaction:semiformal}


\subsubsection{Stability of Binding Specifications}\label{sec:elab:stability}

For the proofs of interaction lemmas we need an auxiliary property of \Knot's de
Bruijn interpretation: shifting and substituting variables in |t| does not
change the scoping of bound variables. This property can be seen as an
enforcement of lexical scoping. In particular this means that evaluation of
binding specifications functions should remain stable under syntactic
operations. This is ultimately achieved by ruling out functions over sorts with
variables: function evaluation can never reach variable cases and thus their
results only depends on the parts of the structure that are left unchanged by
syntactic operations. The following lemma states the stability property.


%% This includes, in particular the stabiltity of evaluation of binding
%% specifications functions.

\begin{lem}\label{lem:elab:funstability}
For all terms |t| of sort |S| and all |f : S → overline α| the
following holds:
\begin{enumerate}
  \item $\hsforall |∀ β, c.     evalfun f (shiftβ c t)   = evalfun f t|$
  \item $\hsforall |∀ β, s, c.  evalfun f (substβ c s t) = evalfun f t|$
\end{enumerate}
\begin{proof}
By induction over the structure of |t| and nested induction over the
right-hand side of |f|.
\end{proof}
\end{lem}

The nested induction of the lemma above deserves essentially proves that
evaluation of binding specifications is invariant under shifting and
substitution. This is a useful result of its own.

\begin{cor}\label{lem:elab:evalstability}
Let $bs$ be a binding specification and $\vartheta = \overline{t_i \mapsto
  u_i}^i$ a local value environment. For given cut-offs $\overline{h_i}^i$ and
substitutes $\overline{v_i}^i$ define the following value environments

\[ \begin{array}{lcl}
     \vartheta'(t_i)  & := & |shiftα|~h_i~u_i     \\
     \vartheta''(t_i) & := & |substα|~h_i~v_i~u_i \\
   \end{array}
\]

\begin{enumerate}
  \item $\hsforall |∀ bs.     evalbs bs ϑ'   = evalbs bs ϑ|$
  \item $\hsforall |∀ bs.     evalbs bs ϑ''  = evalbs bs ϑ|$
\end{enumerate}
\begin{proof}By induction over $bs$ and using Lemma \ref{lem:elab:funstability}
  for function calls.
\end{proof}
\end{cor}



\subsubsection{Shift Commutation}
In this section we discuss the proof and elaboration of Lemma
\ref{lem:elab:shiftcomm} in detail. The other interaction lemmas are proved
similarly.

A prerequisite is a proof of the lemma in the case of a variable. The variable
case lemma is largely independent of a concrete \Knot specification, only the
declared namespaces are involved. Hence the proof of the variable case can be
implemented generically and does not need any special elaboration of the
specification.

\begin{proof}[Proof of Lemma \ref{lem:elab:shiftcomm}]
The proof of the lemma proceeds by induction over u. As discussed the variable
constructor is easy to handle. Hence, we focus on the the inductive steps of the
regular constructors.

For the regular case suppose that we need to show the statement for $K~\ov{u}$
with $K : \overline{x : \alpha} \rightarrow \overline{[bs] t : T} \rightarrow
S$. Define the constructor local value environment $\vartheta$ and two shifted
value environments

\[ \begin{array}{lcl}
      \vartheta(t_i)   & := & u_i                                    \\
      \vartheta'(t_i)  & := & |shiftβ (h2 + evalbs bs ϑ)|~u_i        \\
      \vartheta''(t_i) & := & |shiftα ((h1 + h2) + evalbs bs ϑ)|~u_i \\
   \end{array}
\]

The lemma follows by applying the following equational reasoning to each field
$u$ with binding specification |bs|:

\begin{tabular}{cll}
  & |shiftα (((h1 + Iβ) + h2) + evalbs bs ϑ')|  & |(shiftβ (h2 + evalbs bs ϑ) u)|        \\ $\equiv$ & \multicolumn{2}{l}{By Lemma \ref{lem:elab:evalstability}.} \\
  & |shiftα (((h1 + Iβ) + h2) + evalbs bs ϑ)|   & |(shiftβ (h2 + evalbs bs ϑ) u)|        \\ $\equiv$ & \multicolumn{2}{l}{By associativity.}            \\
  & |shiftα ((h1 + Iβ) + (h2 + evalbs bs ϑ))| & |(shiftβ (h2 + evalbs bs ϑ) u)|        \\ $\equiv$ & \multicolumn{2}{l}{By the inductive hypothesis.} \\
  & |shiftβ (h2 + evalbs bs ϑ)|               & |(shiftα (h1 + (h2 + evalbs bs ϑ)) u)| \\ $\equiv$ & \multicolumn{2}{l}{By associativity.}            \\
  & |shiftβ (h2 + evalbs bs ϑ)|               & |(shiftα ((h1 + h2) + evalbs bs ϑ) u)| \\ $\equiv$ & \multicolumn{2}{l}{By Lemma \ref{lem:elab:evalstability}.} \\
  & |shiftβ (h2 + evalbs bs ϑ'')|             & |(shiftα ((h1 + h2) + evalbs bs ϑ) u)| \\
\end{tabular}
\end{proof}


\subsection{Term Equality Witnesses}\label{ssec:elab:interaction:witness}

Figure \ref{fig:elab:equalitywitness:grammar} shows a grammar for our witness
language. There are two sorts: |eqh| which encodes equalities between domains
and |equ| that encodes equalities between de Bruijn terms. Both sorts have
productions for |refl|, |sym| and |trans| that represent the \emph{reflexivity},
\emph{symmetry} and \emph{transitivity} of an \emph{equivalence relation}. The
remaining productions encode other properties of the respective equalities.

The productions for |congsuccα| respectively |congplus| encode congruences for
the successors and plus functions, and |assocplus| witnesses the associativity
of plus. The stability of evaluating a binding function |f| is added as the
primitive |shiftα f t|.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \vspace{-3mm}
      \[ \begin{array}{lcl}
           |eqh| & ::=  & |refl| \mid |sym eqh| \mid |trans eqh eqh| \mid |congsuccα eqh| \mid |congplus eqh eqh| \\
                 & \mid & |assocplus| \mid |shiftα f t| \\ %% \mid |substα f t|
           |equ| & ::=  & |refl| \mid |sym equ| \mid |trans equ equ| \mid |ih| \\
                 & \mid & |congshiftα eqh equ| \\ %% \mid |congsubstα eqh equ equ| \\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Equality Witness DSL}
  \label{fig:elab:equalitywitness:grammar}
\end{figure}

The interpretation of the domain equality witnesses is show in Figure
\ref{fig:elab:equalitywitness:domain:interpretation}. The judgement
$\Eqh{\vartheta}{eqh}{h_1}{h_2}$ denotes that $eqh$ witnesses the equality of
$h_1$ and $h_2$ under the value environment $\vartheta$.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\Eqh{\vartheta}{eqh}{h}{h}$}} \\
      \[ \begin{array}{c}
           \inferrule*[right=\textsc{EqhRefl}]
                      {\;}
                      {\Eqh{\vartheta}{|refl|}{h}{h}} \qquad
           \inferrule*[right=\textsc{EqhSym}]
                      {\Eqh{\vartheta}{|eqh|}{h_1}{h_2}}
                      {\Eqh{\vartheta}{|sym eqh|}{h_2}{h_1}} \\\\
           \inferrule*[right=\textsc{EqhTrans}]
                      {\Eqh{\vartheta}{|eqh1|}{h_1}{h_2} \\
                       \Eqh{\vartheta}{|eqh2|}{h_2}{h_3}}
                      {\Eqh{\vartheta}{|trans eqh1 eqh2|}{h_1}{h_3}} \\\\
           \inferrule*[right=\textsc{EqhCongSucc}]
                      {\Eqh{\vartheta}{|eqh|}{h_1}{h_2}}
                      {\Eqh{\vartheta}{|congsuccα eqh|}{S_\alpha~h_1}{S_\alpha~h_2}} \\\\
           \inferrule*[right=\textsc{EqhCongPlus}]
                      {\Eqh{\vartheta}{|eqh1|}{h_1}{h_3} \\
                       \Eqh{\vartheta}{|eqh2|}{h_2}{h_4}
                      }
                      {\Eqh{\vartheta}{|congplus eqh1 eqh2|}{h_1 + h_2}{h_3 + h_4}} \\\\
           \inferrule*[right=\textsc{EqhAssocPlus}]
                      {\;}
                      {\Eqh{\vartheta}{|assocplus|}{(h_1 + h_2) + h_3}{h_1 + (h_2 + h_3)}} \\\\
           \inferrule*[right=\textsc{EqhFunShift}]
                      {\;}
                      {\Eqh{\vartheta}{|shiftα f t|}{|evalfun f (shiftα h (ϑ (t)))|}{|evalfun f (ϑ (t))|}} \\\\
           %% \inferrule*[right=\textsc{EqhFunSubst}]
           %%            {\;}
           %%            {\Eqh{\vartheta}{|substα f t|}{|evalfun f (substα h u (ϑ (t)))|}{|evalfun f (ϑ (t))|}} \\\\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Interpretation of Domain Equality Witnesses}
  \label{fig:elab:equalitywitness:domain:interpretation}
\end{figure}


\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \framebox{\mbox{$\Equ{u}{u}{\vartheta}{eqh}{u}{u}$}} \\
      \[ \begin{array}{c}
           \inferrule*[right=\textsc{EquRefl}]
                      {\;}
                      {\Equ{v_0}{v_1}{\vartheta}{|refl|}{u}{u}} \\\\
           \inferrule*[right=\textsc{EquSym}]
                      {\Equ{v_0}{v_1}{\vartheta}{|equ|}{u_1}{u_2}}
                      {\Equ{v_0}{v_1}{\vartheta}{|sym equ|}{u_2}{u_1}} \\\\
           \inferrule*[right=\textsc{EquTrans}]
                      {\Equ{v_0}{v_1}{\vartheta}{|equ1|}{u_1}{u_2} \\
                       \Equ{v_0}{v_1}{\vartheta}{|equ2|}{u_2}{u_3}}
                      {\Equ{v_0}{v_1}{\vartheta}{|trans equ1 equ2|}{u_1}{u_3}} \\\\
           \inferrule*[right=\textsc{EquIH}]
                      {\;}
                      {\Equ{v_0}{v_1}{\vartheta}{|ih|}{v_0}{v_1}} \\\\
           \inferrule*[right=\textsc{EquCongShift}]
                      {\Eqh{\vartheta}{|eqh|}{h_1}{h_2} \\
                       \Equ{v_0}{v_1}{\vartheta}{|equ|}{u_1}{u_2}}
                      {\Equ{v_0}{v_1}{\vartheta}{|congshiftα eqh equ|}{|shiftα|~h_1~u_1}{|shiftα|~h_2~u_2}} \\\\
           %% \inferrule*[right=\textsc{EquCongSubst}]
           %%            {\Eqh{\vartheta}{|eqh|}{h_1}{h_2} \\\\
           %%             \Equ{v_0}{v_1}{\vartheta}{|equ1|}{u_1}{u_2} \\\\
           %%             \Equ{v_0}{v_1}{\vartheta}{|equ2|}{u_3}{u_4}}
           %%            {\Equ{v_0}{v_1}{\vartheta}{|congsubstα eqh equ1 equ2|}{|substα|~h_1~u_1~u_3}{|substα|~h_2~u_2~u_4}} \\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Interpretation of Term Equality Witnesses}
  \label{fig:elab:equalitywitness:interpretation}
\end{figure}


\begin{lem}[Soundness]\label{lem:elab:equalitywitness:soundness}
  The domain and term equality witness languages are sound:
  \begin{enumerate}
  \item
    \[ \inferrule*[]
         {\Eqh{\vartheta}{|eqh|}{h_1}{h_2}
         }
         {h_1 \equiv h_2
         }
    \]
  \item
    \[ \inferrule*[]
         {\Equ{v_0}{v_1}{\vartheta}{|equ|}{u_1}{u_2} \\
          v_0 \equiv v_1
         }
         {u_1 \equiv u_2
         }
    \]
  \end{enumerate}
\end{lem}


\subsection{Proof Elaboration}\label{ssec:elab:interaction:elaboration}

\subsubsection{Elaboration of Stability}

The elaboration function in Figure \ref{fig:elab:shiftstability} produces an
equality witness for Corollary \ref{lem:elab:evalstability}. The corollary is
proven by induction over list-like binding specifications. The elaboration
function follows the same recursive structure and is a fold over binding
specifications. When the binding specification contains a function call, the
stability axiom is used. Congruences are used to make sure we are in the proper
position.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{spec}
        evalBindspecShiftα : bs → eqh
        evalBindspecShiftα []         =  refl
        evalBindspecShiftα (bs, x)    =  congsuccβ (evalBindspecShiftα bs)
          where x : β ∈ LENV
        evalBindspecShiftα (bs, f t)  =  congplus (evalBindspecShiftα bs) (shiftα f t)
      \end{spec}
    \end{minipage}
  }
  \caption{Elaboration of Shift Stability}
  \label{fig:elab:shiftstability}
\end{figure}

%{
%format hi = h "_" i
%format ui = u "_" i

It remains to proof that the elaboration function indeed produces a witness for
Corollary \ref{lem:elab:evalstability}, which is done in the following lemma.

\begin{lem}[Correctness of Stability Elaboration]
  The elaboration for the stability of binding specification evaluation under
  shifting is correct.

  \[ \inferrule*[]
       {|eqh = evalBindspecShiftα bs|     \\
        |ϑ  = (overlinei ui)|             \\
        |ϑ' = (overlinei (shiftα hi ui))|
       }
       {\Eqh{\vartheta}{eqh}{|evalbs bs ϑ'|}{|evalbs bs ϑ|}
       }
  \]
\end{lem}
%}

\subsubsection{Elaboration of Shift Commutation}

Figure \ref{fig:elab:shiftcomm} contains the elaboration function |shiftcomm|
for the inductive step of the shift commutation lemma. We split the semi-formal
proof of Section \ref{ssec:elab:interaction:semiformal} into three parts
\begin{enumerate}
\item the reasoning steps before the application of the induction hypothesis,
  which are encoded by |shiftcomm1|,
\item the application of the induction hypothesis, and
\item the remaining reasoning steps, which are encoded by |shiftcomm2|.
\end{enumerate}

%format shiftcomm1
%format shiftcomm2
\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{spec}
        shiftcomm1     :  bs → equ
        shiftcomm1 bs  =  congshiftα
                            (trans (congplus refl (evalBindspecShiftβ bs)) assocplus)
                            refl

        shiftcomm2     :  bs → equ
        shiftcomm2 bs  =  congshiftβ
                            (congplus refl (evalBindspecShiftα bs))
                            (congshiftα assocplus refl)

        shiftcomm      :  bs → equ
        shiftcomm bs   =  trans (shiftcomm1 bs) (trans ih (sym (shiftcomm2 bs))
      \end{spec}
    \end{minipage}
  }
  \caption{Elaboration of Shift Commutation}
  \label{fig:elab:shiftcomm}
\end{figure}

%{
%format hi = h "_" i
%format ui = u "_" i

\begin{lem}[Correctness of Shift Commutation Elaboration]
  The elaboration for the shift commutation witness is correct.

  \[ \inferrule*[]
       {|equ = shiftcomm bs|   \\
        |ϑ  = (overlinei ui)|  \\\\
        |v0 = shiftα ((h1 + Iβ) + (h2 + evalbs bs ϑ)) (shiftβ (h2 + evalbs bs ϑ) u)| \\\\
        |v1 = shiftβ (h2 + evalbs bs ϑ) (shiftα (h1 + (h2 + evalbs bs ϑ)) u)| \\\\
        |u0 = shiftα (((h1 + Iβ) + h2) + evalbs bs ϑ') (shiftβ (h2 + evalbs bs ϑ) u)| \\\\
        |u1 = shiftβ (h2 + evalbs bs ϑ'') (shiftα ((h1 + h2) + evalbs bs ϑ) u)| \\
       }
       {\Equ{v_0}{v_1}{\vartheta}{equ}{u_0}{u_1}
       }
  \]
\end{lem}
%}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
