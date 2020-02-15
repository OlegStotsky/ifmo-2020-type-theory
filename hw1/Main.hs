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

substDB :: Int -> Term -> Term -> Term
substDB j n (Idx x) | x == j = n
substDB j n i@(Idx x) = i
substDB j n (t1 :@: t2) = (substDB j n t1) :@: (substDB j n t2)
substDB j n (Lmb t) = Lmb $ substDB (j+1) (shift 1 n) t

main :: IO ()
main = do
  let t1 = Lmb $ (Idx 0) :@: (Idx 1 :@: Idx 2)
  let test = Lmb $ Lmb $ Lmb $ Idx 2 :@: Idx 3 :@: Idx 1
  putStrLn $ show $ shift 0 t1
  putStrLn $ show $ shift 4 test