%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

\section{Interaction Lemmas}

Formalizations involve a number of interaction boilerplate lemmas between
|shift|, |weaken| and |subst|. These lemmas are for example needed in weakening
and substitution lemmas for typing relations. Two operation always commute when
they are operating on different variables and a shifting followed by a
substitution on the same variable cancel each other out:
 $$|substα v 0α (shiftα 0α u) = u|.$$

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
