-- Granule interpreter
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# options_ghc -Wno-incomplete-uni-patterns #-}

module Language.Granule.Interpreter.Eval where

import Language.Granule.Interpreter.Desugar
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Context
import Language.Granule.Utils

import Data.Text (cons, pack, uncons, unpack, snoc, unsnoc)
import qualified Data.Text.IO as Text
import Control.Monad (when, foldM)

import qualified Control.Concurrent as C (forkIO)
import qualified Control.Concurrent.Chan as CC (newChan, writeChan, readChan, Chan)
import System.IO (hFlush, stdout, stderr)
import qualified System.IO as SIO

-- Imports for pointers
import qualified Foreign.Marshal.Alloc as PtrAlloc (malloc) -- free
-- import qualified Foreign.Ptr as Ptr (castPtr)
import qualified Foreign.Storable as PtrP (poke, Storable(..)) -- peek
import GHC.Ptr

type RValue = Value (Runtime ()) ()
type RExpr = Expr (Runtime ()) ()

-- | Runtime values only used in the interpreter
data Runtime a =
  -- | Primitive functions (builtins)
    Primitive ((Value (Runtime a) a) -> Value (Runtime a) a)

  -- | Primitive operations that also close over the context
  | PrimitiveClosure (Ctxt (Value (Runtime a) a) -> (Value (Runtime a) a) -> (Value (Runtime a) a))

  -- | File handler
  | Handle SIO.Handle

  -- | Channels
  | Chan (CC.Chan (Value (Runtime a) a))

  -- | Delayed side effects wrapper
  | PureWrapper (IO (Expr (Runtime a) ()))

  -- | Pointers
  | Pointer (IO (Ptr (Value (Runtime a) a)))

-- Problematic as this could container functions which are not really storable
instance PtrP.Storable RValue where
  sizeOf _ = 0
  alignment _ = 0
  peek = undefined
  poke = undefined


diamondConstr :: IO (Expr (Runtime ()) ()) -> RValue
diamondConstr = Ext () . PureWrapper

isDiaConstr :: RValue -> Maybe (IO (Expr (Runtime ()) ()))
isDiaConstr (Pure _ e) = Just $ return e
isDiaConstr (Ext _ (PureWrapper e)) = Just e
isDiaConstr _ = Nothing

instance Show (Runtime a) where
  show (Chan _) = "Some channel"
  show (Primitive _) = "Some primitive"
  show (PrimitiveClosure _) = "Some primitive closure"
  show (Handle _) = "Some handle"
  show (PureWrapper _) = "<suspended IO>"
  show (Pointer _) = "<pointer>"

instance Pretty (Runtime a) where
  pretty = show

evalBinOp :: Operator -> RValue -> RValue -> RValue
evalBinOp op v1 v2 = case op of
    OpPlus -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 + n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 + n2)
      _ -> evalFail
    OpTimes -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 * n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 * n2)
      _ -> evalFail
    OpDiv -> case (v1, v2) of
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 / n2)
      _ -> evalFail
    OpMinus -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> NumInt (n1 - n2)
      (NumFloat n1, NumFloat n2) -> NumFloat (n1 - n2)
      _ -> evalFail
    OpEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 == n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 == n2)) []
      _ -> evalFail
    OpNotEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 /= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 /= n2)) []
      _ -> evalFail
    OpLesserEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 <= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 <= n2)) []
      _ -> evalFail
    OpLesser -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 < n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 < n2)) []
      _ -> evalFail
    OpGreaterEq -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 >= n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 >= n2)) []
      _ -> evalFail
    OpGreater -> case (v1, v2) of
      (NumInt n1, NumInt n2) -> Constr () (mkId . show $ (n1 > n2)) []
      (NumFloat n1, NumFloat n2) -> Constr () (mkId . show $ (n1 > n2)) []
      _ -> evalFail
  where
    evalFail = error $ show [show op, show v1, show v2]

-- Call-by-value big step semantics
evalIn :: (?globals :: Globals) => Ctxt RValue -> RExpr -> IO RValue
evalIn ctxt (App s _ _ e1 e2) = do
    -- (cf. APP_L)
    v1 <- evalIn ctxt e1
    case v1 of
      (Ext _ (Primitive k)) -> do
        -- (cf. APP_R)
        v2 <- evalIn ctxt e2
        return $ k v2

      Abs _ p _ e3 -> do
        -- (cf. APP_R)
        v2 <- evalIn ctxt e2
        -- (cf. P_BETA)
        pResult <- pmatch ctxt [(p, e3)] v2
        case pResult of
          Just e3' -> evalIn ctxt e3'
          _ -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in application at " <> pretty s

      Constr _ c vs -> do
        -- (cf. APP_R)
        v2 <- evalIn ctxt e2
        return $ Constr () c (vs <> [v2])

      _ -> error $ show v1
      -- _ -> error "Cannot apply value"

evalIn ctxt (Binop _ _ _ op e1 e2) = do
     v1 <- evalIn ctxt e1
     v2 <- evalIn ctxt e2
     return $ evalBinOp op v1 v2

evalIn ctxt (LetDiamond s _ _ p _ e1 e2) = do
  -- (cf. LET_1)
  v1 <- evalIn ctxt e1
  case v1 of
    (isDiaConstr -> Just e) -> do
        -- Do the delayed side effect
        eInner <- e
        -- (cf. LET_2)
        v1' <- evalIn ctxt eInner
        -- (cf. LET_BETA)
        pResult  <- pmatch ctxt [(p, e2)] v1'
        case pResult of
          Just e2' -> evalIn ctxt e2'
          Nothing -> error $ "Runtime exception: Failed pattern match " <> pretty p <> " in let at " <> pretty s

    other -> fail $ "Runtime exception: Expecting a diamonad value but got: "
                      <> prettyDebug other

-- Hard-coded 'scale', removed for now
evalIn _ (Val _ _ _ (Var _ v)) | internalName v == "scale" = return
  (Abs () (PVar nullSpan () False $ mkId " x") Nothing (Val nullSpan () False
    (Abs () (PVar nullSpan () False $ mkId " y") Nothing (
      letBox nullSpan (PVar nullSpan () False $ mkId " ye")
         (Val nullSpan () False (Var () (mkId " y")))
         (Binop nullSpan () False
           OpTimes (Val nullSpan () False (Var () (mkId " x"))) (Val nullSpan () False (Var () (mkId " ye"))))))))

evalIn ctxt (Val _ _ _ (Var _ x)) =
    case lookup x ctxt of
      Just val@(Ext _ (PrimitiveClosure f)) -> return $ Ext () $ Primitive (f ctxt)
      Just val -> return val
      Nothing  -> fail $ "Variable '" <> sourceName x <> "' is undefined in context."

evalIn ctxt (Val s _ _ (Promote _ e)) = do
  -- (cf. Box)
  v <- evalIn ctxt e
  return $ Promote () (Val s () False v)

evalIn _ (Val _ _ _ v) = return v

evalIn ctxt (Case _ _ _ guardExpr cases) = do
    v <- evalIn ctxt guardExpr
    p <- pmatch ctxt cases v
    case p of
      Just ei -> evalIn ctxt ei
      Nothing             ->
        error $ "Incomplete pattern match:\n  cases: "
             <> pretty cases <> "\n  expr: " <> pretty v

evalIn ctxt (Hole _ _ _ _) = do
  error "Trying to evaluate a hole, which should not have passed the type checker."

applyBindings :: Ctxt RExpr -> RExpr -> RExpr
applyBindings [] e = e
applyBindings ((var, e'):bs) e = applyBindings bs (subst e' var e)

{-| Start pattern matching here passing in a context of values
    a list of cases (pattern-expression pairs) and the guard expression.
    If there is a matching pattern p_i then return Just of the branch
    expression e_i and a list of bindings in scope -}
pmatch ::
  (?globals :: Globals)
  => Ctxt RValue
  -> [(Pattern (), RExpr)]
  -> RValue
  -> IO (Maybe RExpr)
pmatch _ [] _ =
  return Nothing

pmatch _ ((PWild _ _ _, e):_)  _ =
  return $ Just e

pmatch ctxt ((PConstr _ _ _ id innerPs, t0):ps) v@(Constr _ id' vs)
 | id == id' && length innerPs == length vs = do

  -- Fold over the inner patterns
  tLastM <- foldM (\tiM (pi, vi) -> case tiM of
                                      Nothing -> return Nothing
                                      Just ti -> pmatch ctxt [(pi, ti)] vi) (Just t0) (zip innerPs vs)

  case tLastM of
    Just tLast -> return $ Just tLast
    -- There was a failure somewhere
    Nothing  -> pmatch ctxt ps v

pmatch _ ((PVar _ _ _ var, e):_) v =
  return $ Just $ subst (Val nullSpan () False v) var e

pmatch ctxt ((PBox _ _ _ p, e):ps) v@(Promote _ (Val _ _ _ v')) = do
  match <- pmatch ctxt [(p, e)] v'
  case match of
    Just e -> return $ Just e
    Nothing -> pmatch ctxt ps v

pmatch ctxt ((PInt _ _ _ n, e):ps) (NumInt m) | n == m = return $ Just e

pmatch ctxt ((PFloat _ _ _ n, e):ps) (NumFloat m )| n == m = return $ Just e

pmatch ctxt (_:ps) v = pmatch ctxt ps v

valExpr :: ExprFix2 g ExprF ev () -> ExprFix2 ExprF g ev ()
valExpr = Val nullSpanNoFile () False

builtIns :: (?globals :: Globals) => Ctxt RValue
builtIns =
  [
    (mkId "div", Ext () $ Primitive $ \(NumInt n1)
          -> Ext () $ Primitive $ \(NumInt n2) -> NumInt (n1 `div` n2))
  , (mkId "pure",       Ext () $ Primitive $ \v -> Pure () (Val nullSpan () False v))
  , (mkId "tick",       Pure () (Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "intToFloat", Ext () $ Primitive $ \(NumInt n) -> NumFloat (cast n))
  , (mkId "showInt",    Ext () $ Primitive $ \n -> case n of
                              NumInt n -> StringLiteral . pack . show $ n
                              n        -> error $ show n)
  , (mkId "fromStdin", diamondConstr $ do
      when testing (error "trying to read stdin while testing")
      putStr "> "
      hFlush stdout
      val <- Text.getLine
      return $ Val nullSpan () False (StringLiteral val))

  , (mkId "readInt", diamondConstr $ do
        when testing (error "trying to read stdin while testing")
        putStr "> "
        hFlush stdout
        val <- Text.getLine
        return $ Val nullSpan () False (NumInt $ read $ unpack val))

  , (mkId "toStdout", Ext () $ Primitive $ \(StringLiteral s) ->
                                diamondConstr (do
                                  when testing (error "trying to write `toStdout` while testing")
                                  Text.putStr s
                                  return $ (Val nullSpan () False (Constr () (mkId "()") []))))
  , (mkId "toStderr", Ext () $ Primitive $ \(StringLiteral s) ->
                                diamondConstr (do
                                  when testing (error "trying to write `toStderr` while testing")
                                  let red x = "\ESC[31;1m" <> x <> "\ESC[0m"
                                  Text.hPutStr stderr $ red s
                                  return $ Val nullSpan () False (Constr () (mkId "()") [])))
  , (mkId "openHandle", Ext () $ Primitive openHandle)
  , (mkId "readChar", Ext () $ Primitive readChar)
  , (mkId "writeChar", Ext () $ Primitive writeChar)
  , (mkId "closeHandle",   Ext () $ Primitive closeHandle)
  , (mkId "showChar",
        Ext () $ Primitive $ \(CharLiteral c) -> StringLiteral $ pack [c])
  , (mkId "charToInt",
        Ext () $ Primitive $ \(CharLiteral c) -> NumInt $ fromEnum c)
  , (mkId "charFromInt",
        Ext () $ Primitive $ \(NumInt c) -> CharLiteral $ toEnum c)
  , (mkId "stringAppend",
        Ext () $ Primitive $ \(StringLiteral s) ->
          Ext () $ Primitive $ \(StringLiteral t) -> StringLiteral $ s <> t)
  , ( mkId "stringUncons"
    , Ext () $ Primitive $ \(StringLiteral s) -> case uncons s of
        Just (c, s) -> Constr () (mkId "Some") [Constr () (mkId ",") [CharLiteral c, StringLiteral s]]
        Nothing     -> Constr () (mkId "None") []
    )
  , ( mkId "stringCons"
    , Ext () $ Primitive $ \(CharLiteral c) ->
        Ext () $ Primitive $ \(StringLiteral s) -> StringLiteral (cons c s)
    )
  , ( mkId "stringUnsnoc"
    , Ext () $ Primitive $ \(StringLiteral s) -> case unsnoc s of
        Just (s, c) -> Constr () (mkId "Some") [Constr () (mkId ",") [StringLiteral s, CharLiteral c]]
        Nothing     -> Constr () (mkId "None") []
    )
  , ( mkId "stringSnoc"
    , Ext () $ Primitive $ \(StringLiteral s) ->
        Ext () $ Primitive $ \(CharLiteral c) -> StringLiteral (snoc s c)
    )
  , (mkId "isEOF", Ext () $ Primitive $ \(Ext _ (Handle h)) -> Ext () $ PureWrapper $ do
        b <- SIO.isEOF
        let boolflag =
             case b of
               True -> Constr () (mkId "True") []
               False -> Constr () (mkId "False") []
        return . Val nullSpan () False $ Constr () (mkId ",") [Ext () $ Handle h, boolflag])
  , (mkId "forkLinear", Ext () $ PrimitiveClosure fork)
  , (mkId "forkRep", Ext () $ PrimitiveClosure forkRep)
  , (mkId "fork",    Ext () $ PrimitiveClosure forkRep)
  , (mkId "recv",    Ext () $ Primitive recv)
  , (mkId "send",    Ext () $ Primitive send)
  , (mkId "close",   Ext () $ Primitive close)
  , (mkId "newPtr",  Ext () $ Primitive newPtr)
  -- , (mkId "swapPtr", peek poke castPtr) -- hmm probably don't need to cast the Ptr
  -- , (mkId "freePtr", free)
  ]
  where
    newPtr :: RValue -> RValue
    newPtr rval = Ext () $ Pointer $ do
      -- Allocate a pointer
      ptr <- PtrAlloc.malloc
      -- Stick the runtime value in it and return
      PtrP.poke ptr rval
      return ptr

    fork :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    fork ctxt e@Abs{} = diamondConstr $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan () False (valExpr e) (valExpr $ Ext () $ Chan c)) >> return ()
      return $ valExpr $ Ext () $ Chan c
    fork ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    forkRep :: (?globals :: Globals) => Ctxt RValue -> RValue -> RValue
    forkRep ctxt e@Abs{} = diamondConstr $ do
      c <- CC.newChan
      _ <- C.forkIO $
         evalIn ctxt (App nullSpan () False
                        (valExpr e)
                        (valExpr $ Promote () $ valExpr $ Ext () $ Chan c)) >> return ()
      return $ valExpr $ Promote () $ valExpr $ Ext () $ Chan c
    forkRep ctxt e = error $ "Bug in Granule. Trying to fork: " <> prettyDebug e

    recv :: (?globals :: Globals) => RValue -> RValue
    recv (Ext _ (Chan c)) = diamondConstr $ do
      x <- CC.readChan c
      return $ valExpr $ Constr () (mkId ",") [x, Ext () $ Chan c]
    recv e = error $ "Bug in Granule. Trying to recevie from: " <> prettyDebug e

    send :: (?globals :: Globals) => RValue -> RValue
    send (Ext _ (Chan c)) = Ext () $ Primitive
      (\v -> diamondConstr $ do
         CC.writeChan c v
         return $ valExpr $ Ext () $ Chan c)
    send e = error $ "Bug in Granule. Trying to send from: " <> prettyDebug e

    close :: RValue -> RValue
    close (Ext _ (Chan c)) = diamondConstr $ return $ valExpr $ Constr () (mkId "()") []
    close rval = error $ "Runtime exception: trying to close a value which is not a channel"

    cast :: Int -> Double
    cast = fromInteger . toInteger

    openHandle :: RValue -> RValue
    openHandle (Constr _ m []) =
      Ext () $ Primitive (\x -> diamondConstr (
        case x of
          (StringLiteral s) -> do
            h <- SIO.openFile (unpack s) mode
            return $ valExpr $ Ext () $ Handle h
          rval -> error $ "Runtime exception: trying to open from a non string filename" <> show rval))
      where
        mode = case internalName m of
            "ReadMode" -> SIO.ReadMode
            "WriteMode" -> SIO.WriteMode
            "AppendMode" -> SIO.AppendMode
            "ReadWriteMode" -> SIO.ReadWriteMode
            x -> error $ show x

    openHandle x = error $ "Runtime exception: trying to open with a non-mode value" <> show x

    writeChar :: RValue -> RValue
    writeChar (Ext _ (Handle h)) =
      Ext () $ Primitive (\c -> diamondConstr (
        case c of
          (CharLiteral c) -> do
            SIO.hPutChar h c
            return $ valExpr $ Ext () $ Handle h
          _ -> error $ "Runtime exception: trying to put a non character value"))
    writeChar _ = error $ "Runtime exception: trying to put from a non handle value"

    readChar :: RValue -> RValue
    readChar (Ext _ (Handle h)) = diamondConstr $ do
          c <- SIO.hGetChar h
          return $ valExpr (Constr () (mkId ",") [Ext () $ Handle h, CharLiteral c])
    readChar _ = error $ "Runtime exception: trying to get from a non handle value"

    closeHandle :: RValue -> RValue
    closeHandle (Ext _ (Handle h)) = diamondConstr $ do
         SIO.hClose h
         return $ valExpr (Constr () (mkId "()") [])
    closeHandle _ = error $ "Runtime exception: trying to close a non handle value"

evalDefs :: (?globals :: Globals) => Ctxt RValue -> [Def (Runtime ()) ()] -> IO (Ctxt RValue)
evalDefs ctxt [] = return ctxt
evalDefs ctxt (Def _ var _ (EquationList _ _ _ [Equation _ _ rf [] e]) _ : defs) = do
    val <- evalIn ctxt e
    case extend ctxt var val of
      Just ctxt -> evalDefs ctxt defs
      Nothing -> error $ "Name clash: `" <> sourceName var <> "` was already in the context."
evalDefs ctxt (d : defs) = do
    let d' = desugar d
    evalDefs ctxt (d' : defs)

-- Maps an AST from the parser into the interpreter version with runtime values
class RuntimeRep t where
  toRuntimeRep :: t () () -> t (Runtime ()) ()

instance RuntimeRep Def where
  toRuntimeRep (Def s i rf eqs tys) = Def s i rf (toRuntimeRep eqs) tys

instance RuntimeRep EquationList where
  toRuntimeRep (EquationList s i rf eqns) = EquationList s i rf (map toRuntimeRep eqns)

instance RuntimeRep Equation where
  toRuntimeRep (Equation s a rf ps e) = Equation s a rf ps (toRuntimeRep e)

instance RuntimeRep Expr where
  toRuntimeRep (Val s a rf v) = Val s a rf (toRuntimeRep v)
  toRuntimeRep (App s a rf e1 e2) = App s a rf (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Binop s a rf o e1 e2) = Binop s a rf o (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (LetDiamond s a rf p t e1 e2) = LetDiamond s a rf p t (toRuntimeRep e1) (toRuntimeRep e2)
  toRuntimeRep (Case s a rf e ps) = Case s a rf (toRuntimeRep e) (map (\(p, e) -> (p, toRuntimeRep e)) ps)
  toRuntimeRep (Hole s a rf vs) = Hole s a rf vs

instance RuntimeRep Value where
  toRuntimeRep (Ext a ()) = error "Bug: Parser generated an extended value case when it shouldn't have"
  toRuntimeRep (Abs a p t e) = Abs a p t (toRuntimeRep e)
  toRuntimeRep (Promote a e) = Promote a (toRuntimeRep e)
  toRuntimeRep (Pure a e) = Pure a (toRuntimeRep e)
  toRuntimeRep (Constr a i vs) = Constr a i (map toRuntimeRep vs)
  -- identity cases
  toRuntimeRep (CharLiteral c) = CharLiteral c
  toRuntimeRep (StringLiteral c) = StringLiteral c
  toRuntimeRep (Var a x) = Var a x
  toRuntimeRep (NumInt x) = NumInt x
  toRuntimeRep (NumFloat x) = NumFloat x

eval :: (?globals :: Globals) => AST () () -> IO (Maybe RValue)
eval (AST dataDecls defs _ _ _) = do
    bindings <- evalDefs builtIns (map toRuntimeRep defs)
    case lookup (mkId entryPoint) bindings of
      Nothing -> return Nothing
      -- Evaluate inside a promotion of pure if its at the top-level
      Just (Pure _ e)    -> fmap Just (evalIn bindings e)
      Just (Ext _ (PureWrapper e)) -> do
        eExpr <- e
        fmap Just (evalIn bindings eExpr)
      Just (Promote _ e) -> fmap Just (evalIn bindings e)
      -- ... or a regular value came out of the interpreter
      Just val           -> return $ Just val
