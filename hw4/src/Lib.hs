module Lib where

import           Data.List  (find, findIndex)
import           Data.Maybe

type Symb = String
infix 1 <:
infixl 4 :@: 
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)] 
          | Top
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PRcd [(Symb,Pat)] 
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb,Term)]
          | Prj Symb Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Rcd xs    == Rcd xs1      =  xs == xs1
  Prj l u   == Prj l1 u1    =  l == l1 && u == u1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

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
              in if length x < length xs || any (== Nothing) x
                   then Nothing
                   else (\xs -> Env $ reverse $ concat $ (\(Env env) -> reverse $ env) <$> xs) <$> sequence x
checkPat _ _ = Nothing

infer :: Env -> Term -> Maybe Type
infer (Env env) (Idx x) = return $ snd $ env !! x
infer env Tru = return $ Boo
infer env Fls = return $ Boo
infer env (If t1 t2 t3) = do
  t1Type <- infer env t1
  case t1Type of
    Boo -> do
      t2Type <- infer env t2
      t3Type <- infer env t3
      if t2Type == t3Type
        then return $ t2Type
        else Nothing
    _ -> Nothing
infer (Env env) (Lmb sym t term) = do
  termType <- infer (Env $ (sym, t) : env) term
  return $ t :-> termType
infer e@(Env env) (Let p t term) = do
  tType <- infer e t
  (Env newEnv) <- checkPat p tType
  infer (Env $ newEnv ++ env) term
infer e@(Env env) (Rcd xs) =
  if any (== Nothing) inferredTypes
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
      if l /= rightType
        then Nothing
        else return $ r
    _ -> Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []



main' :: IO ()
main' = do
  let pat = PRcd [("lx", PVar "px"), ("ly", PVar "py")]
  let rec = Rcd [("lx", Tru), ("ly", Fls)]
  putStrLn $ show $ match pat rec
  putStrLn $ show $ oneStep $ Let pat rec $ If Tru (Idx 1) (Idx 0)
  putStrLn $ show $ whnf $ Let pat rec $ If Tru (Idx 1) (Idx 0)

main'' :: IO ()
main'' = do
  let cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1))
  let rec = Rcd [("lB", Tru), ("lK", cK)]
  let pat = PRcd [("lB", PVar "x"), ("lK", PVar "y")]
  putStrLn $ show $ infer0 rec
  putStrLn $ show $ checkPat pat <$> infer0 rec
  putStrLn $ show $ infer0 $ Let pat rec (Idx 0)
  putStrLn $ show $ infer0 $ Let pat rec (Idx 1)

main''' :: IO ()
main''' = do
  let cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1))
  let rec = Rcd [("lK", cK), ("lB1", Tru), ("lB2", Fls)]
  let pat = PRcd [("lB2", PVar "x"), ("lK", PVar "y")]
  putStrLn $ show $ infer0 rec
  putStrLn $ show $ checkPat pat <$> infer0 rec
  putStrLn $ show $ infer0 $ Let pat rec (Idx 1)
