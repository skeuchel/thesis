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
        \begin{minipage}[t]{0.48\linewidth}
          \ruleline{Monad classes}
          \vspace{-4pt}
          \begin{spec}
          class Functor m => Monad m where
            return        :: a -> m a
            (>>=)         :: m a -> (a -> m b) -> m b
            return_bind   :: return x >>= f == f x
            bind_return   :: p >>= return == p
            bind_bind     ::  (p >>= f) >>= g ==
                              p >>= \x -> (f x >>= g)
            fmap_bind     ::  fmap f t ==
                              t >>= (return . f)
          \end{spec}
          %
          \ruleline{State class}
          \vspace{-4pt}
          \begin{spec}
            class Monad m  => MonadState s m where
              get             :: m s
              put             :: s -> m ()
              get_drop        :: get >> t == t
              put_get         ::  put s >> get ==
                                  put s >> return s
              get_put         :: get >>= put == return ()
              get_get         ::  get >>= \s -> get >>= f s ==
                                  get >>= \s -> f s s
              put_put         :: put s1 >> put s2 == put s2
          \end{spec}
          %
          \ruleline{Failure class}
          \vspace{-4pt}
          \begin{spec}
            class Monad m => FailMonad m where
              fail            :: m a
              bind_fail       :: fail >>= f == fail
          \end{spec}
        \end{minipage}
      &
        \begin{minipage}[t]{0.52\linewidth}
          \ruleline{Reader class}
          \vspace{-4pt}
          \begin{spec}
            class Monad m  => MonadReader e m where
              ask             :: m e
              local           :: (e -> e) -> m a -> m a
              ask_query       :: ask >> t == t
              local_return   :: local f . return = return
              ask_ask         ::  ask >>= \s -> ask >>= f s ==
                                  ask >>= \s -> f s s
              ask_bind        :: t >>= \x -> ask >>= \e -> f x e ==
                                  ask >>= \e -> t >>= \x -> f x e
              local_bind      ::  local f (t >>= g) ==
                                  local f t >>= local f . g
              local_ask       :: local f ask == ask >>= return . f
              local_local     :: local f . local g == local (g . f)
          \end{spec}
          %
          \ruleline{Exception class}
          \vspace{-4pt}
          \begin{spec}
            class Monad m  => MonadError x m where
              throwError      :: x -> m a
              catchError      :: m a -> (x -> m a) -> m a
              bind_throw      :: throw e >>= f == throw e
              catch_throw1    :: catch (throw e) h == h e
              catch_throw2    :: catch t throw == t
              catch_return    ::  catch (return x) h == return x
              fmap_catch      ::  fmap f (catch t h) ==
                                  catch (fmap f t) (fmap f . h)
          \end{spec}
        \end{minipage}
      \end{tabular}
    \end{minipage}
  }
  \vspace{-2mm}
  \caption{Key classes, definitions and laws from \Name's monadic library.}
  \label{fig:mod:monadclasses}
\end{figure*}
