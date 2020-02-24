import qualified Data.Map
import qualified Data.List
import Control.Monad.State

type Symb = String 
infixl 4 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)



data Term = Idx Int
          | Term :@: Term
          | Lmb Symb Term
          deriving (Read, Show)

instance Eq Term where
  Idx m     == Idx n      =  m == n
  (t1:@:s1) == (t2:@:s2)  =  t1 == t2 && s1 == s2
  Lmb _ t1  == Lmb _ t2   =  t1 == t2
  _         == _          =  False

type Context = [Symb]

shift :: Int -> Term -> Term
shift val t = go 0 val t where
    go cutOff val (Idx x) | x >= cutOff = Idx $ x+val
    go cutOff val i@(Idx x) = i
    go cutOff val (t1 :@: t2) = (go cutOff val t1) :@: (go cutOff val t2)
    go cutOff val (Lmb sym t) = Lmb sym $ go (cutOff + 1) val t

substDB :: Int -> Term -> Term -> Term
substDB j n (Idx x) | x == j = n
substDB j n i@(Idx x) = i
substDB j n (t1 :@: t2) = (substDB j n t1) :@: (substDB j n t2)
substDB j n (Lmb sym t) = Lmb sym $ substDB (j+1) (shift 1 n) t

betaRuleDB :: Term -> Term
betaRuleDB ((Lmb _ t) :@: s) = shift (-1) $ substDB 0 (shift 1 s) t

oneStepDBN :: Term -> Maybe Term
oneStepDBN (Idx _) = Nothing
oneStepDBN (l@(Lmb _ _) :@: r) = Just $ betaRuleDB (l :@: r)
oneStepDBN (a :@: b) = case oneStepDBN a of
                        Nothing -> case oneStepDBN b of 
                          Nothing -> Nothing
                          Just exp -> Just $ a :@: exp
                        Just exp -> Just $ exp :@: b
oneStepDBN (Lmb sym body) = do res <- oneStepDBN body
                               return $ Lmb sym res

nfDB :: (Term -> Maybe Term) -> Term -> Term 
nfDB f t = case f t of
              Just x -> nfDB f x
              Nothing -> t

unique :: Eq a => [a] -> [a]
unique [x] = [x]
unique [] = []
unique (x:xs) = let l = unique xs in if elem x l then l else x:l
          
freeVars :: Expr -> [Symb] 
freeVars (Var x) = [x]
freeVars (left :@ right) = unique $ (freeVars left) ++ (freeVars right)
freeVars (Lam x m) = Prelude.filter (/=x) (freeVars m)

e2t :: Expr -> (Context, Term)
e2t exp = (context, go context exp) where
  context = freeVars exp
  go context (Var sym) = let (Just ind) = Data.List.elemIndex sym context in Idx ind
  go context (l :@ r) = (go context l) :@: (go context r)
  go context (Lam sym t) = Lmb sym (go (sym:context) t)

main' :: IO ()
main' = do 
  let x = Var "x"
  let y = Var "y"
  putStrLn $ show $ e2t x
  putStrLn $ show $ e2t y
  let t1 = Lam "x" x
  let t2 = Lam "y" y
  let t3 = Lam "x" y
  putStrLn $ show $ e2t t1
  putStrLn $ show $ e2t t2
  putStrLn $ show $ e2t t3
  let t4 = Lam "x" $ t3
  putStrLn $ show $ e2t t4

t2e :: Context -> Term -> Expr
t2e ctx t = evalState (go ctx t) 0 where
  go :: Context -> Term -> State Integer Expr
  go ctx (Idx x) = return $ Var $ ctx !! x
  go ctx (l :@: r) = do newL <- (go ctx l)
                        newR <- (go ctx r)
                        return $ newL :@ newR
  go ctx (Lmb sym t) = do id <- get
                          case Data.List.elemIndex sym ctx of
                             Just idx -> do put $ (id+1)
                                            let newName = sym ++ "______" ++ (show id)
                                            newBody <- go (newName:ctx) t
                                            return $ Lam newName newBody
                             Nothing -> do newBody <- go (sym:ctx) t 
                                           return $ Lam sym newBody

main'' :: IO ()
main'' = do 
  let x = Var "x"
  let y = Var "y"
  putStrLn $ show $ let (ctx, t) = e2t x in t2e ctx t
  putStrLn $ show $ let (ctx, t) = e2t y in t2e ctx t
  let t1 = Lam "x" x
  let t2 = Lam "y" y
  let t3 = Lam "x" y
  putStrLn $ show $ let (ctx, t) = e2t t1 in t2e ctx t
  putStrLn $ show $ let (ctx, t) = e2t t2 in t2e ctx t
  putStrLn $ show $ let (ctx, t) = e2t t3 in t2e ctx t
  let t4 = Lam "x" $ t3
  putStrLn $ show $ let (ctx, t) = e2t t4 in t2e ctx t