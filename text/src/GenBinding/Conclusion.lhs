%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\section{Conclusion}

In this paper, we presented extensions to the \Knot specification language for
syntax with binding to cover specifications of semantic relations. A type system
keeps track of the scope of meta-variable to guarantee that relations are
well-scoped. We also extend \Knot's code generator \Needle to generate weakening
and substitution lemmas for relations in \Coq. As a result, \Knot covers a
larger extent of boilerplate functions and lemmas than any prior work on
first-order representations.

%%% Local Variables:
%%% mode: latex
%%% TeX-command-default: "Make"
%%% TeX-master: "Main"
%%% End:
