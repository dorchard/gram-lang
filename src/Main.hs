------------------
------ Granule ------
------------------

import Eval
import Syntax.Parser
import Syntax.Pretty
import Checker.Checker
import System.Environment

version :: String
version = "Granule v0.2.0.0"

main :: IO ()
main = do
  args <- getArgs
  case args of
    []      -> putStrLn "Usage: gran <SOURCE_FILE>"
    (src:_)  -> do
      -- Get the filename
      input <- readFile src
      -- Flag '-d' turns on debug mode
      run input (if length args >= 2 then args !! 1 == "-d" else False)

run :: String -> Bool -> IO ()
run input debug = do
  -- Welcome message
  putStrLn version

  -- Parse
  let (ast, nameMap) = parseDefs input

  -- Debugging mode produces the AST and the pretty printer
  if debug
    then do
      putStrLn $ "AST:          " ++ show ast
      putStrLn $ "\nSource:\n"    ++ pretty ast
    else return ()

  -- Type check
  checked <- check ast debug nameMap
  putStrLn $ showCheckerResult checked

  case checked of
    -- If type checking succeeds then evaluate the program...
    Right True -> do
      val <- eval ast
      case val of
        Just val' -> putStrLn $ pretty val'
        Nothing   -> return ()
    _ -> return ()

showCheckerResult :: Either String Bool -> String
showCheckerResult (Left s) = s
showCheckerResult (Right True) = "Ok."
showCheckerResult (Right False) = "Failed."
