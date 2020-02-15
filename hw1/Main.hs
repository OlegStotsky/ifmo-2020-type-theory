infixl 4 :@:

data Term = Idx Int
          | Term :@: Term
          | Lmb Term
          deriving (Eq, Read, Show)

shift :: Int -> Term -> Term
shift val t = go 0 val t where
    go cutOff val (Idx x) | x >= cutOff = Idx $ x+val
    go cutOff val i@(Idx x) = i
    go cutOff val (t1 :@: t2) = (go cutOff val t1) :@: (go cutOff val t2)
    go cutOff val (Lmb t) = Lmb $ go (cutOff + 1) val t

main :: IO ()
main = do
  let t1 = Lmb $ (Idx 0) :@: (Idx 1 :@: Idx 2)
  let test = Lmb $ Lmb $ Lmb $ Idx 2 :@: Idx 3 :@: Idx 1
  putStrLn $ show $ shift 0 t1
  putStrLn $ show $ shift 4 test