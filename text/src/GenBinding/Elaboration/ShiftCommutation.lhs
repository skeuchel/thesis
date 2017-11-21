%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

\section{Interaction Lemmas}

Formalizations involve a number of interaction boilerplate lemmas between
|shift|, |weaken| and |subst|. These lemmas are for example needed in weakening
and substitution lemmas for typing relations. We discuss the two types of
interaction lemmas that appear and their generic proofs. First by giving
informal induction proofs of the lemmas and then a formal elaboration of the
inductive steps.

\paragraph{Commutation}
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

\paragraph{Cancelation}
When operating on the same variable, a shifting followed by a substitution
cancel each other out:
 $$|substα v 0α (shiftα 0α u) = u|.$$


\subsection{Shift Commutation}
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

\end{proof}


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
  & |shiftα ((h1 + Iβ + h2) + evalbs bs ϑ')|  & |(shiftβ (h2 + evalbs bs ϑ) u)|        \\ $\equiv$ & \multicolumn{2}{l}{By Lemma \ref{lem:elab:evalstability}.} \\
  & |shiftα ((h1 + Iβ + h2) + evalbs bs ϑ)|   & |(shiftβ (h2 + evalbs bs ϑ) u)|        \\ $\equiv$ & \multicolumn{2}{l}{By associativity.}            \\
  & |shiftα ((h1 + Iβ) + (h2 + evalbs bs ϑ))| & |(shiftβ (h2 + evalbs bs ϑ) u)|        \\ $\equiv$ & \multicolumn{2}{l}{By the inductive hypothesis.} \\
  & |shiftβ (h2 + evalbs bs ϑ)|               & |(shiftα (h1 + (h2 + evalbs bs ϑ)) u)| \\ $\equiv$ & \multicolumn{2}{l}{By associativity.}            \\
  & |shiftβ (h2 + evalbs bs ϑ)|               & |(shiftα ((h1 + h2) + evalbs bs ϑ) u)| \\ $\equiv$ & \multicolumn{2}{l}{By Lemma \ref{lem:elab:evalstability}.} \\
  & |shiftβ (h2 + evalbs bs ϑ'')|             & |(shiftα ((h1 + h2) + evalbs bs ϑ) u)| \\
\end{tabular}

\subsection{Proof Term Elaboration}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \[ \begin{array}{lcl}
           |eqh| & ::=  & |refl| \mid |sym eqh| \mid |trans eqh eqh| \mid |congsuccα eqh| \mid |congplus eqh eqh| \\
                 & \mid & |assoc| \mid |shiftα f t| \mid |substα f t|       \\
         \end{array}
      \]
      \hrule
      \vspace{2mm}
      \framebox{\mbox{$\Eqh{\vartheta}{eqh}{h}{h}$}} \\
      \vspace{-5mm}
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
                      {\Eqh{\vartheta}{eqh}{h_1}{h_2}}
                      {\Eqh{\vartheta}{|congsuccα eqh|}{S_\alpha~h_1}{S_\alpha~h_2}} \\\\
           \inferrule*[right=\textsc{EqhCongPlus}]
                      {\Eqh{\vartheta}{eqh1}{h_1}{h_3} \\
                       \Eqh{\vartheta}{eqh2}{h_2}{h_4}
                      }
                      {\Eqh{\vartheta}{|congplus eqh1 eqh2|}{h_1 + h_2}{h_3 + h_4}} \\\\
           \inferrule*[right=\textsc{EqhAssocPlus}]
                      {\;}
                      {\Eqh{\vartheta}{|assoc|}{h_1 + (h_2 + h_3)}{(h_1 + h_2) + h_3}} \\\\
           \inferrule*[right=\textsc{EqhFunShift}]
                      {\;}
                      {\Eqh{\vartheta}{|shiftα f t|}{|evalfun f (shiftα h (ϑ (t)))|}{|evalfun f (ϑ (t))|}} \\\\
           \inferrule*[right=\textsc{EqhFunSubst}]
                      {\;}
                      {\Eqh{\vartheta}{|substα f h s t|}{|evalfun f (substα h u (ϑ (t)))|}{|evalfun f (ϑ (t))|}} \\\\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Elaboration of shift commutation}
  \label{fig:shiftcomm}
\end{figure}



%% \paragraph{Well-Scopedness} The syntactic operations preserve well-scoping. This
%% includes shifting, weakening and substitution lemmas. If a sort does not
%% depend on the namespace of the substitute, we can formulate a strengthening
%% lemma instead:
%% $$
%% \begin{array}{c}
%% \inferrule*[]
%%   {|h + Iα ⊢ u : S| \\ |α ∉ depsOf S|
%%   }
%%   {|h ⊢ u : S|}
%% \end{array}
%% $$

%% %format (shifthvlα (k) (c) (x) (y)) = x " \xhookrightarrow{\makebox[.7cm]{$" c "$}}_\alpha " y

%% \paragraph{Environment Lookup} Lemmas for shifting, weakening and strengthening
%% for environment lookups form the variable cases for corresponding lemmas of
%% typing relations. These lemmas also explain how the associated data in the
%% context is changed. For operating somewhere deep in the context we use relations,
%% like for example $|shifthvlα Γ c Γ1 Γ2|$ which denotes that |Γ2| is the result
%% after inserting a new |α| variable at cutoff position |c| in |Γ1|. The shifting
%% lemma for lookups is then:
%% $$
%% \begin{array}{c}
%% \inferrule*[]
%%   {|shifthvlα Γ c Γ1 Γ2| \\
%%    |(n : overline u) inα Γ1|}
%%   {|(shiftN c n : overline (shiftα' c u) ) inα Γ2|}
%% \end{array}
%% $$

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
