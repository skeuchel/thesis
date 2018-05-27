%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%if False

\begin{code}
import Prelude hiding (print)
\end{code}

%endif

%format eval = "\Varid{eval}"
%format interface = "\textsf{\textbf{interface}}"
%format implements = "\textsf{\textbf{implements}}"
%format public = "\textsf{\textbf{public}}"
%format . = "."

\section{Expression Problem}\label{sec:mod:expressionproblem}

\begin{figure}[t]
\fbox{\hspace{-5pt}
  \begin{minipage}{0.98\columnwidth}
    \begin{spec}
      data ArithExp
        =  Lit Int
        |  Add ArithExp ArithExp

      eval :: ArithExp -> Int
      eval (Lit i)      =  i
      eval (Add e1 e2)  =  eval e1 + eval e2
    \end{spec}
  \end{minipage}
}
\caption{Evaluation of arithmetic expressions (Haskell)}
\label{fig:mod:monolithicexpressionshaskell}
\end{figure}

\begin{figure}[t]
\fbox{\hspace{-5pt}
  \begin{minipage}{0.98\columnwidth}
    \begin{spec}
      interface ArithExp {
        int eval();
      }
      class Lit implements ArithExp {
        public int lit;
        public int eval() { return lit; }
      }
      class Add implements ArithExp {
        public ArithExp e1, e2;
        public int eval() { return e1.eval() + e2.eval(); }
      }
    \end{spec}
  \end{minipage}
}
\caption{Evaluation of arithmetic expressions (Java)}
\label{fig:mod:monolithicexpressionsjava}
\end{figure}

Consider the Haskell program for the evaluation of simple arithmetic expressions
in Figure \ref{fig:mod:monolithicexpressionshaskell}. We have a datatype
|ArithExp|, representing arithmetic expressions with constructors for integer
literals and addition, and an evaluation function |eval :: ArithExp -> Int| that
evaluates an expression to an integer value.

Figure \ref{fig:mod:monolithicexpressionsjava} shows an equivalent Java
program. The |ArithExp| interface contains an |int eval()| method. The two cases
of a literal and an addition are handled by the two classes |Lit| and |Add| that
implement |ArithExp|.

%-------------------------------------------------------------------------------

We can extend these programs along two dimensions:
\begin{enumerate}
  \item Adding a new case, e.g. a constructor for multiplication.
  \item Adding a new operation, e.g. converting an expression to a string.
\end{enumerate}

\begin{figure}[t]
\fbox{\hspace{-5pt}
  \begin{minipage}{0.98\columnwidth}
\begin{code}
data ArithExp
  =  Lit Int
  |  Add ArithExp ArithExp
  |  Mul ArithExp ArithExp

eval :: ArithExp -> Int
eval (Lit i)      =  i
eval (Add e1 e2)  =  eval e1 + eval e2
eval (Mul e1 e2)  =  eval e1 * eval e2

print :: ArithExp -> String
print (Lit i)      =  show i
print (Add e1 e2)  =  "(" ++ print e1 ++ "+" ++ print e2 ++ ")"
print (Mul e1 e2)  =  "(" ++ print e1 ++ "*" ++ print e2 ++ ")"
\end{code}
  \end{minipage}
}
\caption{Extended arithmetic expressions (Haskell)}
\label{fig:mod:monolithicexpressionshaskellextended}
\end{figure}

In Haskell, performing the second extension in our example is easy: we add one
more function to the program

\begin{spec}
print :: ArithExp -> String
print (Lit i)      =  show i
print (Add e1 e2)  =  "(" ++ print e1 ++ "+" ++ print e2 ++ ")"
\end{spec}

However, covering a new case inevitably requires modifying existing code: it has
to be added to the |ArithExp| datatype declaration and, for totality, also to
existing functions. Figure \ref{fig:mod:monolithicexpressionshaskellextended}
shows the code with both extensions.

%-------------------------------------------------------------------------------

\begin{figure}[t]
\fbox{\hspace{-5pt}
  \begin{minipage}{0.98\columnwidth}
    \begin{spec}
      interface ArithExp {
        int eval();
        String print();
      }
      class Lit implements ArithExp {
        public int lit;
        public int eval() { return lit; }
        public String print() { return String.valueOf(lit); }
      }
      class Add implements ArithExp {
        public ArithExp e1, e2;
        public int eval() { return e1.eval() + e2.eval(); }
        public String print() {
          return e1.print().concat("+").concat(e2.print());
        }
      }
      class Mul implements ArithExp {
        public ArithExp e1, e2;
        public int eval() { return e1.eval() * e2.eval(); }
        public String print() {
          return e1.print().concat("*").concat(e2.print());
        }
      }
    \end{spec}
  \end{minipage}
}
\caption{Extended arithmetic expressions (Java)}
\label{fig:mod:monolithicexpressionsjavaextended}
\end{figure}

In Java the situation is reversed. The multiplication case can easily be added
by creating a new class |Mul| that implements |Exp|.

\begin{spec}
class Mul implements ArithExp {
  public ArithExp e1, e2;
  public int eval () { return e1.eval() * e2.eval(); }
}
\end{spec}

However, the conversion to a |String| inevitably requires editing the existing
code and adding a new method to the |ArithExp| interface and existing
implementations of that interface.\footnote{We disregard the |toString()| method
  that is part of the base class |Object|.} Figure
\ref{fig:mod:monolithicexpressionsjavaextended} shows the code with both
extensions.

%-------------------------------------------------------------------------------

Performing such extensions in both dimensions simultaneously and modularly, i.e.
without changing or recompiling the existing code, and keeping the code
type-safe was coined as \emph{the expression problem} by
\citet{expression-problem}. Solutions to the expression problem exist in
multiple languages: \citet{expression-problem} presents a solution in Java using
Generics and the \emph{Datatypes \`a la Carte} (DTC) approach
\cite{swierstra2008dtc} is a well-known solution in the Haskell programming
language. In both of these solutions, modularity has to be anticipated and
catered for from the beginning however. Indeed, we cannot reuse the datatype
declaration and interface declarations from this section, but have to use ones
that account for modular extensions. We will call a Haskell datatype that can be
modularly extended a \emph{modular datatype} and use the term \emph{modular
  function} for modularly extensible functions that are defined on modular
datatypes.

Our goal to modularly engineer programming language meta-theory adds a third
dimension to the expression problem: \emph{modular proofs} of statements about
modular functions on modular datatypes. In the remainder of this chapter we
first present the DTC approach (Section \ref{sec:mod:datatypesalacarte}) and
then discuss stumbling and building blocks to extend the approach to support
modular reasoning (Sections \ref{sec:mod:reasoningalacarte},
\ref{sec:mod:churchencodings} and \ref{sec:mod:mendler}).

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
