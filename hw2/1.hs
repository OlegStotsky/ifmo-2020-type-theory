type Symb = String
infixl 4 :@: 
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | Type :* Type
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Let Pat Term Term deriving (Show)

data Pat = PVar Symb
         | PPair Pat Pat deriving (Show, Eq)

instance Eq Term where
  Fls       == Fls         =  True
  Tru       == Tru         =  True
  If b u w  == If b1 u1 w1 =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1      =  m == m1
  (u:@:w)   == (u1:@:w1)   =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 =  t == t1 && u == u1
  Let p t term == Let p' t' term' = p == p' && t == t' && term == term'
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
    go cutOff val (Pair fi se) = Pair newFi newSe where
                                  newFi = go cutOff val fi
                                  newSe = go cutOff val se
    go cutOff val (Fst term) = Fst $ go cutOff val term
    go cutOff val (Snd term) = Snd $ go cutOff val term
    go cutOff val (Let p t term) = let newTerm = go (1 + (size p)) val term in
                                     Let p t newTerm
                                   where 
                                     size :: Pat -> Int
                                     size (PVar _) = 1
                                     size (PPair u v) = (size u) + (size v) + 1

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
substDB j n (Let p t term) = Let p t newBody where
                                newBody = substDB (j + size p) (shift (size p) n) term
                                size :: Pat -> Int
                                size (PVar _) = 1
                                size (PPair u v) = (size u) + (size v)
substDB j n (Pair t1 t2) = Pair newT1 newT2 where
                              newT1 = substDB j n t1
                              newT2 = substDB j n t2                              
substDB j n (Fst t) = Fst $ substDB j n t
substDB j n (Snd t) = Snd $ substDB j n t

isValue :: Term -> Bool
isValue Tru = True
isValue Fls = True
isValue (Lmb _ _ _) = True
isValue (Pair u v) | isValue u && isValue v = True
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
oneStep (Fst p@(Pair u v)) | isValue p = return $ u
oneStep (Snd p@(Pair u v)) | isValue p = return $ v
oneStep (Fst t) = do t' <- oneStep t
                     return $ Fst t'
oneStep (Snd t) = do t' <- oneStep t
                     return $ Snd t'
oneStep (Pair u v) = case oneStep u of
                      Just u' -> Just $ Pair u' v
                      Nothing -> case oneStep v of
                        Just v' -> Just $ Pair u v'
                        _ -> Nothing
oneStep _ = Nothing

whnf :: Term -> Term 
whnf u = case oneStep u of 
            Just u' -> whnf u'
            Nothing -> u


infer :: Env -> Term -> Maybe Type
infer (Env env) (Idx x) = return $ snd $ env !! x
infer env Tru = return $ Boo
infer env Fls = return $ Boo
infer env (If t1 t2 t3) = do
                      t1Type <- infer env t1
                      case t1Type of 
                        Boo ->  do t2Type <- infer env t2
                                   t3Type <- infer env t3
                                   if t2Type == t3Type then 
                                    return $ t2Type
                                   else
                                    Nothing
                        _ -> Nothing
infer (Env env) (Lmb sym t term) = do termType <- infer (Env $ (sym, t):env) term
                                      return $ t :-> termType
-- infer e@(Env env) (Let p t term) = do   tType <- infer e t
                                        -- termType <- infer (Env $ (sym, tType):env) term
                                        -- return $ termType
infer env (t1 :@: t2) = do  leftType <- infer env t1
                            rightType <- infer env t2
                            case leftType of
                              (l :-> r) -> if l /= rightType then
                                            Nothing
                                          else
                                            return $ r
                              _ -> Nothing
infer env (Pair u v) = do uType <- infer env u
                          vType <- infer env v
                          return $ uType :* vType
infer env (Fst t) = do  tType <- infer env t                              
                        case tType of 
                          (t1 :* _) -> Just t1
                          _ -> Nothing
infer env (Snd t) = do  tType <- infer env t                              
                        case tType of 
                          (_ :* t2) -> Just t2
                          _ -> Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

main1 :: IO ()
main1 = do let cSnd = Lmb "z" (Boo :* Boo) (Snd (Idx 0));
           let cCurry = Lmb "f" (Boo :* Boo :-> Boo) $ Lmb "x" Boo $ Lmb "y" Boo $ (Idx 2) :@: Pair (Idx 1) (Idx 0);
           putStrLn $ show $ whnf (cCurry :@: cSnd :@: Fls :@: Tru)
           putStrLn $ show $ whnf (cCurry :@: cSnd :@: Fls)

main2 :: IO ()
main2 = do let cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1));
           let cUnCurry = Lmb "f" (Boo :-> Boo :-> Boo) $ Lmb "z" (Boo :* Boo) $ (Idx 1) :@: Fst (Idx 0) :@: Snd (Idx 0);
           putStrLn $ show $ infer0 (cUnCurry :@: cK)
           putStrLn $ show $ infer0 (cUnCurry :@: cK :@: Pair Fls Tru)
           putStrLn $ show $ infer0 (cUnCurry :@: cK :@: Fls)

main3 :: IO ()
main3 = do let test2 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 2);
           putStrLn $ show $ substDB 0 (Idx 40) test2