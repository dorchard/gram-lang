import qualified HappyParser
import Eval
import Expr
import Type
import Checker
import System.Environment

run :: String -> Bool -> IO ()
run input debug = do
  let ast = HappyParser.parseDefs input
  if debug
    then do
      putStrLn $ "AST:          " ++ (show ast)
      putStrLn $ "\nSource:\n"    ++ (pretty ast)
    else return ()
  checked <- check ast debug
  putStrLn $ "\nType checking:\t" ++ (showCheckerResult checked)
  putStrLn $ "\nEvaluating main:\t" ++ (show $ eval ast)

main :: IO ()
main = do
  args <- getArgs
  input <- readFile (head args)
  run input (if length args >= 2 then args !! 1 == "-d" else False)

showCheckerResult :: Either String Bool -> String
showCheckerResult (Left s) = s
showCheckerResult (Right True) = "Ok!"
showCheckerResult (Right False) = "Failed!"