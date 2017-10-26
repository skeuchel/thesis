%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%-------------------------------------------------------------------------------
\section{Expression Semantics}
\label{sec:exprsemantics}

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
  \caption{Expression semantics}
  \label{fig:sem:expressions}
\end{figure}

We now define the semantics of symbolic expressions as an evaluation to concrete
de Bruijn terms. Figure~\ref{fig:sem:expressions} contains the definition. The
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

%-------------------------------------------------------------------------------

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
