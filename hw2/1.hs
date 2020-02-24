type Symb = String
infixl 4 :@: 
infixr 3 :->

data Type = Boo
          | Type :-> Type
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Symb Term Term deriving (Show)

instance Eq Term where
  Fls       == Fls         =  True
  Tru       == Tru         =  True
  If b u w  == If b1 u1 w1 =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1      =  m == m1
  (u:@:w)   == (u1:@:w1)   =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 =  t == t1 && u == u1
  Let sym t term == Let sym' t' term' = sym == sym' && t == t' && term == term'
  _         == _           =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

shift :: Int -> Term -> Term
shift val t = go 0 val t where
    go cutOff val Fls = Fls
    go cutOff val Tru = Tru
    go cutOff val (If t1 t2 t3) = If newT1 newT2 newT3 where
                                    newT1 = go cutOff val t1
                                    newT2 = go cutOff val t2
                                    newT3 = go cutOff val t3
    go cutOff val (Idx x) | x >= cutOff = Idx $ x+val
    go cutOff val i@(Idx x) = i
    go cutOff val (t1 :@: t2) = (go cutOff val t1) :@: (go cutOff val t2)
    go cutOff val (Lmb sym t term) = Lmb sym t newBody where 
                                       newBody = go (cutOff + 1) val term

substDB :: Int -> Term -> Term -> Term
substDB _ _ Fls = Fls
substDB _ _ Tru = Tru
substDB j n (If t1 t2 t3) = If newT1 newT2 newT3 where
                              newT1 = substDB j n t1
                              newT2 = substDB j n t2
                              newT3 = substDB j n t3
substDB j n (Idx x) | x == j = n
substDB j n i@(Idx x) = i
substDB j n (t1 :@: t2) = (substDB j n t1) :@: (substDB j n t2)
substDB j n (Lmb sym t term) = Lmb sym t newBody where
                                newBody = substDB (j+1) (shift 1 n) term
substDB j n (Let sym t term) = Let sym t newBody where
                                newBody = substDB (j+1) (shift 1 n) term

isValue :: Term -> Bool
isValue Tru = True
isValue Fls = True
isValue (Lmb _ _ _) = True
isValue _ = False

oneStep :: Term -> Maybe Term
oneStep (If Tru t _) = return $ t
oneStep (If Fls _ t) = return $ t
oneStep (If t1 t2 t3) = do reducedT1 <- oneStep t1
                           return $ (If reducedT1 t2 t3)
oneStep ((Lmb sym t term) :@: r) | isValue r = return $ substDB 0 r term
oneStep (l@(Lmb sym t term) :@: r) = do r' <- oneStep r
                                        return $ l :@: r'
oneStep (l :@: r) = do l' <- oneStep l
                       return $ l' :@: r
oneStep (Let sym t term) | isValue t = return $ substDB 0 t term
oneStep (Let sym t term) = do t' <- oneStep t
                              return $ Let sym t' term
oneStep _ = Nothing

whnf :: Term -> Term 
whnf u = case oneStep u of 
            Just u' -> whnf u'
            Nothing -> u


infer :: Env -> Term -> Maybe Type
infer env t = inferHelper env t 0

inferHelper :: Env -> Term -> Int -> Maybe Type
inferHelper (Env env) (Idx x) depth = return $ snd $ env !! x
inferHelper env Tru depth = return $ Boo
inferHelper env Fls depth = return $ Boo
inferHelper env (If t1 t2 t3) depth = do
                      t1Type <- inferHelper env t1 depth
                      case t1Type of 
                        Boo ->  do t2Type <- inferHelper env t2 depth
                                   t3Type <- inferHelper env t3 depth
                                   if t2Type == t3Type then 
                                    return $ t2Type
                                   else
                                    Nothing
                        _ -> Nothing
inferHelper (Env env) (Lmb sym t term) depth = do termType <- inferHelper (Env $ (sym, t):env) term (depth+1)
                                                  return $ t :-> termType
inferHelper env (t1 :@: t2) depth = do leftType <- inferHelper env t1 depth
                                       rightType <- inferHelper env t2 depth
                                       case leftType of
                                          (l :-> r) -> if l /= rightType then
                                                        Nothing
                                                      else
                                                        return $ r
                                          _ -> Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []