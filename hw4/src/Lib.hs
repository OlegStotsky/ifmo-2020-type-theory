module Lib where

import           Data.List  (find, findIndex)
import           Data.Maybe

type Symb = String

infix 1 <:

infixl 4 :@:

infixr 3 :->

infixl 4 \/

infix 5 /\

data Type
  = Boo
  | Type :-> Type
  | TRcd [(Symb, Type)]
  | Top
  deriving (Read, Show, Eq)

data Pat
  = PVar Symb
  | PRcd [(Symb, Pat)]
  deriving (Read, Show, Eq)

data Term
  = Fls
  | Tru
  | If Term Term Term
  | Idx Int
  | Term :@: Term
  | Lmb Symb Type Term
  | Let Pat Term Term
  | Rcd [(Symb, Term)]
  | Prj Symb Term
  deriving (Read, Show)

instance Eq Term where
  Fls == Fls = True
  Tru == Tru = True
  If b u w == If b1 u1 w1 = b == b1 && u == u1 && w == w1
  Idx m == Idx m1 = m == m1
  (u :@: w) == (u1 :@: w1) = u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 = t == t1 && u == u1
  Let p u w == Let p1 u1 w1 = p == p1 && u == u1 && w == w1
  Rcd xs == Rcd xs1 = xs == xs1
  Prj l u == Prj l1 u1 = l == l1 && u == u1
  _ == _ = False

newtype Env =
  Env [(Symb, Type)]
  deriving (Read, Show, Eq)

shift :: Int -> Term -> Term
shift val t = go 0 val t
  where
    go cutOff val Fls = Fls
    go cutOff val Tru = Tru
    go cutOff val (If t1 t2 t3) = If newT1 newT2 newT3
      where
        newT1 = go cutOff val t1
        newT2 = go cutOff val t2
        newT3 = go cutOff val t3
    go cutOff val (Idx x)
      | x >= cutOff = Idx $ x + val
    go cutOff val i@(Idx x) = i
    go cutOff val (t1 :@: t2) = (go cutOff val t1) :@: (go cutOff val t2)
    go cutOff val (Lmb sym t term) = Lmb sym t newBody
      where
        newBody = go (cutOff + 1) val term
    go cutOff val (Let p t term) =
      let newTerm = go (cutOff + (size p)) val term
       in let newT = go cutOff val t
           in Let p newT newTerm
    go cutOff val (Prj sym term) = Prj sym (go cutOff val term)
    go cutOff val (Rcd xs) = Rcd $ (\(sym, term) -> (sym, go cutOff val term)) <$> xs

size :: Pat -> Int
size (PVar _)  = 1
size (PRcd xs) = sum $ (\(_, pat) -> size pat) <$> xs

substDB :: Int -> Term -> Term -> Term
substDB _ _ Fls = Fls
substDB _ _ Tru = Tru
substDB j n (If t1 t2 t3) = If newT1 newT2 newT3
  where
    newT1 = substDB j n t1
    newT2 = substDB j n t2
    newT3 = substDB j n t3
substDB j n (Idx x)
  | x == j = n
substDB j n i@(Idx x) = i
substDB j n (t1 :@: t2) = (substDB j n t1) :@: (substDB j n t2)
substDB j n (Lmb sym t term) = Lmb sym t newBody
  where
    newBody = substDB (j + 1) (shift 1 n) term
substDB j n (Let p t term) = Let p newT newBody
  where
    newT = substDB j n t
    newBody = substDB (j + size p) (shift (size p) n) term
substDB j n (Prj sym term) = Prj sym (substDB j n term)
substDB j n (Rcd xs) = Rcd $ (\(sym, term) -> (sym, substDB j n term)) <$> xs

isValue :: Term -> Bool
isValue Tru         = True
isValue Fls         = True
isValue (Lmb _ _ _) = True
isValue (Rcd xs)    = all (isValue . snd) xs
isValue _           = False

match :: Pat -> Term -> Maybe [(Symb, Term)]
match (PVar s) t
  | isValue t = return $ [(s, t)]
match (PRcd xs) (Rcd ys)
  | all (isValue . snd) ys = concat <$> (sequence $ zipWith (\x y -> match (snd x) (snd y)) xs ys)
match (PRcd xs) (Rcd ys)
  | all (isValue . snd) ys = do
    let x = [match t t' | (sym, t) <- xs, (sym', t') <- ys, sym == sym']
    if length x < length xs || any (== Nothing) x
      then Nothing
      else do
        let transformed = fromJust <$> x
        return $ concat transformed
match _ _ = Nothing

oneStep :: Term -> Maybe Term
oneStep (If Tru t _) = return $ t
oneStep (If Fls _ t) = return $ t
oneStep (If t1 t2 t3) = do
  reducedT1 <- oneStep t1
  return $ (If reducedT1 t2 t3)
oneStep ((Lmb sym t term) :@: r)
  | isValue r = return $ substDB 0 r term
oneStep (l@(Lmb sym t term) :@: r) = do
  r' <- oneStep r
  return $ l :@: r'
oneStep (l :@: r) = do
  l' <- oneStep l
  return $ l' :@: r
oneStep (Let p t term)
  | isValue t = do
    m <- match p t
    return $ performSubst m term
  where
    performSubst m term = fst $ foldr (\(sym, term) (res, pos) -> (substDB pos term res, pos + 1)) (term, 0) m
oneStep (Let p t term) = do
  t' <- oneStep t
  return $ Let p t' term
oneStep (Prj sym (Rcd xs))
  | (not . null $ filter (\(s, _) -> s == sym) xs) && (isValue $ snd $ head $ filter (\(s, _) -> s == sym) xs) =
    Just $ snd $ head $ filter (\(s, _) -> s == sym) xs
oneStep (Prj sym t) = do
  t' <- oneStep t
  return $ Prj sym t'
oneStep (Rcd xs) =
  let oneStepped = (\(sym, t) -> (sym, oneStep t)) <$> xs
   in let found =
            findIndex
              (\x ->
                 case x of
                   (_, (Just _)) -> True
                   _             -> False)
              oneStepped
       in case found of
            (Just idx) ->
              let (l, r) = splitAt idx xs
               in Just $
                  Rcd $
                  l ++
                  (let (l, r) = oneStepped !! idx
                    in (l, fromJust r)) :
                  tail r
            Nothing -> Nothing
oneStep _ = Nothing

whnf :: Term -> Term
whnf u =
  case oneStep u of
    Just u' -> whnf u'
    Nothing -> u

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar s) t = return $ Env $ [(s, t)]
checkPat (PRcd xs) (TRcd ys) =
  let allSymbsFound = all id [any (\(sym, _) -> sym == sym') ys | (sym', _) <- xs]
   in if not allSymbsFound
        then Nothing
        else let x = [checkPat t t' | (sym, t) <- xs, (sym', t') <- ys, sym == sym']
              in if length x < length xs || elem Nothing x
                   then Nothing
                   else (\xs -> Env $ reverse $ concat $ (\(Env env) -> reverse env) <$> xs) <$> sequence x
checkPat _ _ = Nothing

infer :: Env -> Term -> Maybe Type
infer (Env env) (Idx x) = return $ snd $ env !! x
infer env Tru = return Boo
infer env Fls = return Boo
infer env (If t1 t2 t3) = do
  t1Type <- infer env t1
  case t1Type of
    Boo -> do
      t2Type <- infer env t2
      t3Type <- infer env t3
      return $ t2Type \/ t3Type
    _ -> Nothing
infer (Env env) (Lmb sym t term) = do
  termType <- infer (Env $ (sym, t) : env) term
  return $ t :-> termType
infer e@(Env env) (Let p t term) = do
  tType <- infer e t
  (Env newEnv) <- checkPat p tType
  infer (Env $ newEnv ++ env) term
infer e@(Env env) (Rcd xs) =
  if Nothing `elem` inferredTypes
    then Nothing
    else Just $ TRcd $ zip (fst <$> xs) (fromJust <$> inferredTypes)
  where
    inferredTypes = infer e . snd <$> xs
infer e@(Env env) (Prj sym rcd) = do
  rcdType <- infer e rcd
  case rcdType of
    TRcd xs -> do
      symIdx <- findIndex (\(s, _) -> s == sym) xs
      return $ snd $ xs !! symIdx
    _ -> Nothing
infer env (t1 :@: t2) = do
  leftType <- infer env t1
  rightType <- infer env t2
  case leftType of
    (l :-> r) ->
      if not (rightType <: l)
        then Nothing
        else return r
    _ -> Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

(<:) :: Type -> Type -> Bool
_ <: Top = True
(s :-> t) <: (s' :-> t') = isContraVariant && isCoVariant
  where
    isContraVariant = s' <: s
    isCoVariant = t <: t'
(TRcd xs) <: (TRcd ys) =
  let allSymbsFound = and [any (\(sym, _) -> sym == sym') xs | (sym', _) <- ys]
   in (allSymbsFound && and [t <: t' | (s, t) <- xs, (s', t') <- ys, s == s'])
Boo <: Boo = True
_ <: _ = False

(\/) :: Type -> Type -> Type
Boo \/ Boo = Boo
s@(s1 :-> s2) \/ t@(t1 :-> t2) =
  case helper s t of
    Just t -> t
    _      -> Top
  where
    helper (s1 :-> s2) (t1 :-> t2) = do
      m <- s1 /\ t1
      let j = s2 \/ t2
      return $ m :-> j
(TRcd xs) \/ (TRcd ys) = TRcd $ [(s, t \/ t') | (s, t) <- xs, (s', t') <- ys, s == s']
t1 \/ t2
  | t1 <: t2 = t2
t1 \/ t2
  | t2 <: t1 = t1
_ \/ _ = Top

(/\) :: Type -> Type -> Maybe Type
t /\ Top = return $ t
Top /\ t = return $ t
Boo /\ Boo = return $ Boo
s@(s1 :-> s2) /\ t@(t1 :-> t2) = do
  let m = s1 \/ t1
  j <- s2 /\ t2
  return $ m :-> j
(TRcd xs) /\ (TRcd ys) = do
  let both = [(s, t /\ t') | (s, t) <- xs, (s', t') <- ys, s == s']
  let onlyXS = [(s, t) | (s, t) <- xs, not $ any (\(s', _) -> s == s') both]
  let onlyYS = [(s, t) | (s, t) <- ys, not $ any (\(s', _) -> s == s') both]
  if Nothing `elem` (snd <$> both)
    then Nothing
    else return $ TRcd $ onlyXS ++ ((\m -> fromJust <$> m) <$> both) ++ onlyYS
t1 /\ t2
  | t1 <: t2 = Just $ t1
t1 /\ t2
  | t2 <: t1 = Just $ t2
_ /\ _ = Nothing

main' :: IO ()
main' = do
  let rec1 = TRcd [("lx", Boo), ("ly", Boo :-> Boo)]
  let rec2 = TRcd [("lz", TRcd []), ("ly", Boo :-> Boo), ("lx", Boo)]
  let rec3 = TRcd [("lz", Top), ("ly", Boo :-> Boo), ("lx", Top)]
  print (rec2 <: rec1)
  print (rec1 :-> Boo <: rec2 :-> Boo)
  print (rec2 <: rec3)
  print (rec1 <: rec3)
  print (rec3 <: rec1)

main'' :: IO ()
main'' = do
  let tr1 = TRcd [("la", Boo), ("lb", Boo :-> Boo)]
  let tr2 = TRcd [("lb", Boo :-> Boo), ("lc", TRcd [])]
  let tr3 = TRcd [("lb", Boo), ("lc", TRcd [])]
  putStrLn $ show $ tr1 \/ tr2
  putStrLn $ show $ tr1 /\ tr2
  putStrLn $ show $ tr1 \/ tr3
  putStrLn $ show $ tr1 /\ tr3

main''' :: IO ()
main''' = do
  let type1 = TRcd [("la",Boo),("lb",Boo :-> Boo)]
  let type2 = TRcd [("lb",Boo :-> Boo), ("lc",Boo :-> Boo :-> Boo)]
  let body1 = Rcd [("lb",Prj "lb" (Idx 0)),("lc",Lmb "x" Boo $ Prj "lb" (Idx 1))]
  let body2 = Rcd [("lb",Prj "lb" (Idx 0)),("la",Prj "lb" (Idx 0) :@: Tru)]
  let func1 = Lmb "x" type1 body1
  let func2 = Lmb "y" type2 body2
  putStrLn $ show $ infer0 func1
