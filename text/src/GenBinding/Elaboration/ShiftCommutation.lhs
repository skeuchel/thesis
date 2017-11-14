%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

\section{Interaction Lemmas}

Formalizations involve a number of interaction boilerplate lemmas between
|shift|, |weaken| and |subst|. These lemmas are for example needed in weakening
and substitution lemmas for typing relations. We discuss the two types of
interaction lemmas that appear first and then showcase the elaboration of one of
these lemmas.

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
lemma can be homogenous, i.e. $\alpha = \beta$ or heterogeneous $\alpha \neq
\beta$.


Similar lemmas hold for the commutation of a substitution and a shifting and two
substitutions. Extra care needs to be taken when a substitution is involved,
since the substitute(s) may also need to be changed.

\paragraph{Cancelation}
When operating on the same variable, a shifting followed by a substitution
cancel each other out:
 $$|substα v 0α (shiftα 0α u) = u|.$$

\subsection{Shift Commutation}

As an example of elaborating proofs interaction lemmas we showcase the
commutation of two shifts. A prerequisite is a proof of the lemma in the case of
a variable. The variable case lemma is largely independent of a concrete \Knot
specification, only the declared namespaces are involved. Hence the proof of the
variable case can be implemented generically and does not need any special
elaboration of the specification.

The proof of the lemma proceeds by induction over terms. As discussed the
variable constructor is easy to handle. Hence, we focus on the elaboration for
the inductive steps of the regular constructors.

For the regular case suppose that we need to show the statement for |K
(overlinei ti)| with |K : (overlinei (si,bsi)) → s|. Let $t'_i$ be the result of
applying the inner shift to the $i$-th field.
\[ t'_i |= shiftα (lift bsi (overlinei ti) (k + 0)) ti| \]

The lemma follows by applying the following equational reasoning to
each field $t$ with binding specification |bs|:

\begin{spec}
      shiftα (lift bs (overlinei t'i) (k + (1 + c)))         (shiftα (lift bs (overlinei ti) (k + 0)) t)

  ==  {-" \text{By Lemma \ref{lem:liftshift}.} "-}

      shiftα (lift bs (overlinei ti) (k + (1 + c)))          (shiftα (lift bs (overlinei ti) (k + 0)) t)

  ==  {-" \text{By Lemma \ref{lem:liftassoc}.} "-}

      shiftα (lift bs (overlinei ti) k + (1 + c))            (shiftα (lift bs (overlinei ti) k + 0) t)

  ==  {-" \text{By the inductive hypothesis.} "-}

      shiftα (lift bs (overlinei ti) k + 0)                  (shiftα (lift bs (overlinei ti) k + c) t)

  ==  {-" \text{By Lemma \ref{lem:liftassoc}.} "-}

      shiftα (lift bs (overlinei ti) (k + 0))                (shiftα (lift bs (overlinei ti) (k + c)) t)

  ==  {-" \text{By Lemma \ref{lem:liftshift}.} "-}

      shiftα (lift bs (overlinei t'i) (k + 0))               (shiftα (lift bs (overlinei ti) (k + c)) t)
\end{spec}


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
