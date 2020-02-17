import qualified Data.Map
import qualified Data.Set
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

e2t :: Expr -> (Context,Term)
e2t exp = toResult $ evalState (go Data.Set.empty exp Data.Map.empty) (0) where
  toResult (s, t) = (Data.Set.toList s, t)
  go :: Data.Set.Set String -> Expr -> Data.Map.Map String Int -> State Int (Data.Set.Set String, Term)
  go context (Var x) m = do st <- get
                            if Data.Map.member x m then 
                              return $ (context, Idx $ (st - (m Data.Map.! x)-1))
                            else
                              return $ (Data.Set.insert x context, Idx $ st + 1)
  go context (l :@ r) m = do (newContextL, newL) <- go context l m
                             (newContextR, newR) <- go context r m
                             return $ (Data.Set.union newContextL newContextR, newL :@: newR)
  go context (Lam x t) m = do st <- get
                              put $ (st+1)
                              let newM = Data.Map.insert x st m
                              (newContext, newBody) <- go context t newM
                              return $ (Data.Set.delete x newContext, Lmb x newBody)