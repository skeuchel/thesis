%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt
%include macros.fmt

%format white = "~"
%format catchError = "\Varid{catch}"
%format throwError = "\Varid{throw}"


\begin{figure*}[t]
  \setlength\mathindent{1mm}
  \scriptsize
  \centering
  \fbox{
    \begin{minipage}[t]{\columnwidth}
      \begin{tabular}{@@{}l@@{}l@@{}}
        \begin{minipage}[t]{0.5\linewidth}
          \ruleline{Identity monad}
          \vspace{-4pt}
          \begin{spec}
            newtype Id a

            Id           :: a -> Id a
            runId        :: Id a -> a
          \end{spec}
          %
          \ruleline{State transformer}
          \vspace{-4pt}
          \begin{spec}
            newtype StateT s m a

            StateT       :: (s -> m (a,s)) -> StateT s m a
            runStateT    :: StateT s m a -> s -> m (a,s)
          \end{spec}
          %
          \ruleline{Reader transformer}
          \vspace{-4pt}
          \begin{spec}
            newtype ReaderT e m a

            ReaderT      :: (e -> m a) -> ReaderT e m a
            runReaderT   :: ReaderT e m a -> e -> m a
          \end{spec}
        \end{minipage}
      &
        \begin{minipage}[t]{0.5\linewidth}
          \ruleline{Failure transformer}
          \vspace{-4pt}
          \begin{spec}
            newtype FailT m a

            FailT        :: m (Maybe a) -> FailT m a
            runFailT     :: FailT m a -> m (Maybe a)
          \end{spec}
          %
          \ruleline{Exception transformer}
          \vspace{-4pt}
          \begin{spec}
            newtype ExcT x m a

            ExcT         :: m (Either x a) -> ExcT x m a
            runExcT      :: ExcT x m a -> m (Either x a)
          \end{spec}
        \end{minipage}
      \end{tabular}
    \end{minipage}
  }
  \caption{Monad transformers}
  \label{fig:mod:monadtransformers}
\end{figure*}
