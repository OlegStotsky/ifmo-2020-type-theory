type Symb = String
infixl 4 :@: 
infixr 3 :->
infixl 5 :*
infixl 4 :+ 

data Type = Boo
          | Nat
          | Type :-> Type
          | Type :* Type
          | Type :+ Type
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Zero              
          | Succ Term         
          | Pred Term     
          | IsZero Term       
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Let Pat Term Term 
          | Fix Term 
          | Inl Term Type            
          | Inr Type Term   
          | Case Term Symb Term Term 
          deriving (Show)

data Pat = PVar Symb
         | PPair Pat Pat deriving (Show, Eq)

instance Eq Term where
  Fls       == Fls                 =  True
  Tru       == Tru                 =  True
  If b u w  == If b1 u1 w1         =  b == b1 && u == u1 && w == w1
  Zero      == Zero                =  True
  Succ u    == Succ u1             =  u == u1 
  Pred u    == Pred u1             =  u == u1
  IsZero u  == IsZero u1           =  u == u1
  Idx m     == Idx m1              =  m == m1
  (u:@:w)   == (u1:@:w1)           =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1         =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1        =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1          =  u == u1 && w == w1
  Fst z     == Fst z1              =  z == z1
  Snd z     == Snd z1              =  z == z1
  Fix u     == Fix u1              =  u == u1
  Inl u t   == Inl u1 t1           =  u == u1 &&  t == t1    
  Inr t u   == Inr t1 u1           =  t == t1 && u == u1   
  Case u _ t s == Case u1 _ t1 s1  =  u == u1 && t == t1 && s == s1 
  _         == _                   =  False

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
    go cutOff val (Let p t term) = let newTerm = go (cutOff + (size p)) val term in
                                      let newT = go cutOff val t in
                                     Let p newT newTerm
                                   where 
                                     size :: Pat -> Int
                                     size (PVar _) = 1
                                     size (PPair u v) = (size u) + (size v)
    go cutOff val (Succ t) = Succ $ go cutOff val t
    go cutOff val (Pred t) = Pred $ go cutOff val t
    go cutOff val (IsZero t) = IsZero $ go cutOff val t
    go cutOff val (Fix t) = Fix $ go cutOff val t
    go cutOff val (Inl term t) = Inl (go cutOff val term) t
    go cutOff val (Inr t term) = Inr t (go cutOff val term)
    go cutOff val (Case t1 sym t2 t3) = Case newT1 sym newT2 newT3 where
                                          newT1 = go cutOff val t1
                                          newT2 = go (cutOff + 1) val t2
                                          newT3 = go (cutOff +1) val t3
    go _ _ t = t

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
substDB j n (Let p t term) = Let p newT newBody where
                                newT = substDB j n t
                                newBody = substDB (j + size p) (shift (size p) n) term
                                size :: Pat -> Int
                                size (PVar _) = 1
                                size (PPair u v) = (size u) + (size v)
substDB j n (Pair t1 t2) = Pair newT1 newT2 where
                              newT1 = substDB j n t1
                              newT2 = substDB j n t2                              
substDB j n (Fst t) = Fst $ substDB j n t
substDB j n (Snd t) = Snd $ substDB j n t
substDB j n (Succ t) = Succ $ substDB j n t
substDB j n (Pred t) = Pred $ substDB j n t
substDB j n (IsZero t) = IsZero $ substDB j n t
substDB j n (Fix t) = Fix $ substDB j n t
substDB j n (Inl term t) = Inl (substDB j n term) t
substDB j n (Inr t term) = Inr t (substDB j n term)
substDB j n (Case t1 sym t2 t3) = Case newT1 sym newT2 newT3 where
                                    newT1 = substDB j n t1
                                    newT2 = substDB (j+1) (shift 1 n) t2
                                    newT3 = substDB (j+1) (shift 1 n) t3
substDB _ _ t = t

isValue :: Term -> Bool
isValue Tru = True
isValue Fls = True
isValue (Lmb _ _ _) = True
isValue (Pair u v) | isValue u && isValue v = True
isValue t | isNV t = True
isValue (Inl v t) | isValue v = True
isValue (Inr t v) | isValue v = True
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
oneStep (Let p t term) | isValue t = do m <- match p t
                                        return $ performSubst m term
                                      where
                                        performSubst m term = fst $ foldr (\(sym, term) (res, pos) -> (substDB pos term res, pos+1)) (term, 0) m
oneStep (Let p t term) = do t' <- oneStep t
                            return $ Let p t' term
oneStep (Fst p@(Pair u v)) | isValue p = return $ u
oneStep (Snd p@(Pair u v)) | isValue p = return $ v
oneStep (Fst t) = do t' <- oneStep t
                     return $ Fst t'
oneStep (Snd t) = do t' <- oneStep t
                     return $ Snd t'
oneStep (Pair u v) | not (isValue u) = do u' <- oneStep u
                                          return $ Pair u' v
oneStep (Pair u v) | (isValue u) = do v' <- oneStep v
                                      return $ Pair u v'                     
oneStep (Succ t) = do t' <- oneStep t
                      return $ Succ t'
oneStep (Pred Zero) = return $ Zero
oneStep (Pred (Succ nv)) | isNV nv = return $ nv
oneStep (Pred t) = do t' <- oneStep t
                      return $ Pred t'
oneStep (IsZero Zero) = return $ Tru
oneStep (IsZero (Succ nv)) | isNV nv = return $ Fls
oneStep (IsZero t) = do t' <- oneStep t
                        return $ IsZero t'
oneStep f@(Fix (Lmb sym t term)) = return $ substDB 0 f term
oneStep (Fix t) = do t' <- oneStep t
                     return $ Fix t'
oneStep (Inl term t) = do term' <- oneStep term
                          return $ Inl term' t
oneStep (Inr t term) = do term' <- oneStep term
                          return $ Inr t term'
oneStep (Case (Inl t1 t) sym t2 t3) | isValue t1 = return $ substDB 0 t1 t2
oneStep (Case (Inr t t1) sym t2 t3) | isValue t1 = return $ substDB 0 t1 t3
oneStep (Case t1 sym t2 t3) = do t1' <- oneStep t1                        
                                 return $ Case t1' sym t2 t3
oneStep _ = Nothing

whnf :: Term -> Term 
whnf u = case oneStep u of 
            Just u' -> whnf u'
            Nothing -> u


infer :: Env -> Term -> Maybe Type
infer _ Zero = return $ Nat
infer (Env env) (Idx x) = return $ snd $ env !! x
infer env Tru = return $ Boo
infer env Fls = return $ Boo
infer env (Succ t) = do tType <- infer env t
                        case tType of
                          Nat -> Just Nat
                          _ -> Nothing
infer env (Pred t) = do tType <- infer env t
                        case tType of
                          Nat -> Just Nat
                          _ -> Nothing
infer env (IsZero t) = do tType <- infer env t
                          case tType of
                            Nat -> Just Boo
                            _ -> Nothing
infer env (Fix t) = do tType <- infer env t
                       case tType of 
                         (t1 :-> t2) | t1 == t2 -> Just t1
                         _ -> Nothing
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
infer e@(Env env) (Let p t term) = do tType <- infer e t
                                      (Env newEnv) <- checkPat p tType
                                      infer (Env $ newEnv ++ env) term
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
infer env (Inl term s) = do t <- infer env term
                            return $ t :+ s
infer env (Inr t term) = do s <- infer env term
                            return $ t :+ s
infer e@(Env env) (Case t1 sym t2 t3) = do t1Type <- infer e t1
                                           case t1Type of 
                                              (s :+ t) -> do  t2Type <- infer (Env $ (sym, s) : env) t2
                                                              t3Type <- infer (Env $ (sym, t) : env) t3
                                                              if t2Type /= t3Type then 
                                                                Nothing
                                                              else 
                                                                return $ t2Type
                                              _ -> Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []


match :: Pat -> Term -> Maybe [(Symb,Term)]
match (PVar s) t | isValue t = return $ [(s, t)]
match (PPair l r) (Pair u v) | isValue u && isValue v = do lMatch <- (match l u) 
                                                           rMatch <- (match r v) 
                                                           return $ lMatch ++ rMatch
match _ _ = Nothing


checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar s) t = return $ Env $ [(s, t)]
checkPat (PPair u v) (t1 :* t2) = do (Env uCheck) <- checkPat u t1
                                     (Env vCheck) <- checkPat v t2
                                     return $ Env $ (vCheck ++ uCheck)
checkPat _ _ = Nothing

isNV :: Term -> Bool
isNV Zero = True
isNV (Succ t) | isNV t = True
isNV _ = False

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
           let [pa,pb,pc,pd] = PVar <$> ["a","b","c","d"];
           putStrLn $ show $ match (PPair pa pb) (Pair Tru Fls)
           putStrLn $ show $ match (PPair (PPair pa pb) pc) (Pair (Pair Tru Fls) Tru)
           putStrLn $ show $ match pa (If Tru Fls Tru)
           let test0 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 0);
           putStrLn $ show $ oneStep test0
           let test1 = Let (PPair (PVar "a") (PVar "b")) (Pair Tru Fls) (Idx 1);
           putStrLn $ show $ oneStep test1

main4 :: IO ()
main4 = do let [pa,pb] = PVar <$> ["a","b"];
           let cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1));
           let cUnCurry' = Lmb "f" (Boo :-> Boo :-> Boo) $ Lmb "z" (Boo :* Boo) $ Let (PPair (PVar "x") (PVar "y")) (Idx 0) $ Idx 3 :@: Idx 1 :@: Idx 0;
           putStrLn $ show $ infer0 cUnCurry'
           putStrLn $ show $ infer0 (cUnCurry' :@: cK)
           putStrLn $ show $ infer0 (cUnCurry' :@: cK :@: Pair Fls Tru)
           putStrLn $ show $ infer0 (cUnCurry' :@: cK :@: Fls)
           let pair  = Pair Tru cK;
           let ppair = PPair pa pb;
           putStrLn $ show $ infer0 $ Let ppair pair (Idx 0);

one   = Succ Zero
two   = Succ one
three = Succ two
four  = Succ three
five  = Succ four
six   = Succ five
seven = Succ six
eight = Succ seven
nine  = Succ eight
ten   = Succ nine

plus_ = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $ 
  If (IsZero $ Idx 1) 
     (Idx 0) 
     (Succ $ Idx 2 :@: Pred (Idx 1) :@: Idx 0)
plus = Fix plus_

minus_ = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $ 
  If (IsZero $ Idx 0)
     (Idx 1) 
     (Pred $ Idx 2 :@: Idx 1 :@: Pred (Idx 0))
minus = Fix minus_

eq_ = Lmb "f" (Nat :-> Nat :-> Boo) $ Lmb "m" Nat $ Lmb "n" Nat $ 
  If (IsZero $ Idx 1) 
     (IsZero $ Idx 0) 
     (If (IsZero $ Idx 0) 
         (IsZero $ Idx 1) 
         (Idx 2 :@: Pred (Idx 1) :@: Pred (Idx 0)))
eq = Fix eq_

mult_ = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $ 
  If (IsZero $ Idx 1) 
     Zero 
     (plus :@: Idx 0 :@: (Idx 2 :@: Pred (Idx 1) :@: Idx 0))
mult = Fix mult_

power_  = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $ 
  If (IsZero $ Idx 0) 
     one 
     (mult :@: Idx 1 :@: (Idx 2 :@: Idx 1 :@: Pred (Idx 0)))
power = Fix power_          

main5 :: IO ()
main5 = do let test = minus :@: (power :@: nine :@: two) :@: (mult :@: eight :@: ten);
           putStrLn $ show $ whnf test
           putStrLn $ show $ whnf $ eq :@: test :@: one
           putStrLn $ show $ whnf $ IsZero (Succ (Pred Fls))
           putStrLn $ show $ infer0 (Lmb "f" (Nat :-> Nat) $ Fix $ Idx 0)