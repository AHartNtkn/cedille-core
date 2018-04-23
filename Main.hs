import System.Environment
import Core

main :: IO ()
main = do
  args <- System.Environment.getArgs
  let val = fromString $ mconcat args
  ann <- annotate val

  putStrLn "[Term]"
  putStrLn =<< toString val
  putStrLn ""

  putStrLn "[Type]"
  putStrLn =<< toString (typOf ann)
  putStrLn ""

  putStrLn "[Normal]"
  putStrLn =<< toString (norOf ann)
  putStrLn ""

  return ()