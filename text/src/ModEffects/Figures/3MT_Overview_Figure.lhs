%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt
%include macros.fmt

%format white = "~"
%format catchError = "\Varid{catch}"
%format throwError = "\Varid{throw}"

\begin{figure*}[ht]
\scriptsize
\begin{center}
\hspace{-.5cm}
\begin{minipage}[t]{0.9\linewidth}

\hspace{.65cm}\ruleline{Monad class}
< class Functor m => Monad m where
<     return       :: a -> m a
<     (>>=)        :: m a -> (a -> m b) -> m b
<     return_bind  :: return x >>= f == f x
<     bind_return  :: p >>= return == p
<     bind_bind    ::  (p >>= f) >>= g ==
<                      p >>= \x -> (f x >>= g)
<     fmap_bind    :: fmap f t == t >>= (return . f)
<

\hspace{.65cm}\ruleline{State class}
< class Monad m  => MonadState s m where
<   get        :: m s
<   put        :: s -> m ()
<   get_query  :: get >> t == t
<   put_get    :: put s >> get == put s >> return s
<   get_put    :: get >>= put == return ()
<   get_get    :: get >>= \s >>= get >>= f s ==
<                 get >>= \s -> f s s
<   put_put    :: put s1 >> put s2 == put s2

\hspace{.65cm}\ruleline{Reader class}
< class Monad m  => MonadReader e m where
<   ask           :: m e
<   local         :: (e -> e) -> m a -> m a
<   ask_query     :: ask >> t == t
<   local_return  :: local f . return = return
<   ask_ask       ::  ask >>= \s >>= ask >>= f s ==
<                       ask >>= \s -> f s s
<   ask_bind      ::  t >>= \x -> ask >>= \e -> f x e ==
<                       ask >>= \e -> t >>= \x -> f x e
<   local_bind    ::  local f (t >>= g) ==
<                       local f t >>= local f . g
<   local_ask     :: local f ask == ask >>= return . f
<   local_local   :: local f . local g == local (g . f)

\hspace{.65cm}\ruleline{Failure class}
< class Monad m => FailMonad m where
<   fail         :: m a
<   bind_fail    :: fail >>= f == fail
<

% <   fmap_throw    :: fmap f (throw e) = throw e -- remove?

\hspace{.65cm}\ruleline{Exception class}
< class Monad m  => MonadError x m where
<   throwError    :: x -> m a
<   catchError    :: m a -> (x -> m a) -> m a
<   bind_throw    :: throw e >>= f == throw e
<   catch_throw1  :: catch (throw e) h == h e
<   catch_throw2  :: catch t throw == t
<   catch_return  :: catch (return x) h == return x
<   fmap_catch    ::  fmap f (catch t h) ==
<                     catch (fmap f t) (fmap f . h)

\end{minipage}
\caption{Key classes, definitions and laws from \Name's monadic library. The names of algebraic laws are in bold.}
\label{fig:mod:monadclasses}
\end{center}
\end{figure*}

\begin{figure*}[!ht]
\scriptsize
\begin{center}
\begin{minipage}[t]{0.9\linewidth}
\hspace{.5cm}\ruleline{Identity monad}\quad
< newtype Id a
<
< Id           :: a -> Id a
< runId        :: Id a -> a
<
\hspace{.5cm}\ruleline{Failure transformer}
< newtype FailT m a
<
< FailT        :: m (Maybe a) -> FailT m a
< runFailT     :: FailT m a -> m (Maybe a)
<
\hspace{.5cm}\ruleline{State transformer}
< newtype StateT s m a
<
< StateT       :: (s -> m (a,s)) -> StateT s m a
< runStateT    :: StateT s m a -> s -> m (a,s)
<
\hspace{.5cm}\ruleline{Exception transformer}
< newtype ExcT x m a
<
< ExcT         :: m (Either x a) -> ExcT x m a
< runExcT      :: ExcT x m a -> m (Either x a)
<
\hspace{.5cm}\ruleline{Reader transformer}
< newtype ReaderT e m a
<
< ReaderT :: (e -> m a) -> ReaderT e m a
< runReaderT :: ReaderT e m a -> e -> m a

\end{minipage}
\caption{Monad transformers}
\label{fig:mod:monadtransformers}
\end{center}
\end{figure*}
