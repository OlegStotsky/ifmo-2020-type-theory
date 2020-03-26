module Lib where

type Symb = String

infixl 4 :@:, :@>

infixr 3 :->

infix 1 ||-

data Type
  = TIdx Int -- типовой атом как индекс Де Брауна
  | Type :-> Type -- стрелочный тип
  | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
  deriving (Read, Show, Ord)

instance Eq Type where
  TIdx n1 == TIdx n2 = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  _ == _ = False

-- Объявление либо переменная, либо тип
data Decl
  = VDecl Symb Type --  объявление термовой переменной с ее типом, Symb - справочное имя этой переменной
  | TDecl Symb --  объявление типовой переменной, Symb - справочное имя этой переменной
  deriving (Read, Show, Ord)

instance Eq Decl where
  VDecl _ t1 == VDecl _ t2 = t1 == t2
  TDecl _ == TDecl _ = True
  _ == _ = False

type Env = [Decl]

data Term
  = Idx Int
  | Term :@: Term
  | Term :@> Type
  | Lmb Decl Term
  deriving (Read, Show, Eq, Ord)

lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl

-- типовой индекс в типе ссылается на номер объемлющего ForAll
botF = ForAll "a" (TIdx 0)

tArr = TIdx 0 :-> TIdx 0

topF = ForAll "a" tArr

-- Кодирование самоприменения в System F (примеры из лекции)
sa0 = lV "z" botF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)

sa1 = lV "z" topF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)

sa2 = lV "z" topF $ Idx 0 :@> topF :@: Idx 0

-- Комбинатор $I$ (TIdx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lV "x" (TIdx 0) $ Idx 0

cIF = lT "a" $ lV "x" (TIdx 0) $ Idx 0

-- Комбинаторы $K$ и $K_\ast$
tK = TIdx 1 :-> TIdx 0 :-> TIdx 1

tKF = ForAll "a" $ ForAll "b" tK

cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1

tKast = TIdx 1 :-> TIdx 0 :-> TIdx 0

tKastF = ForAll "a" $ ForAll "b" tKast

cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

-- Комбинатор $C$
tFlip = (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 1 :-> TIdx 2 :-> TIdx 0

tFlipF = ForAll "a" $ ForAll "b" $ ForAll "c" $ tFlip

cFlipF =
  lT "a" $
  lT "b" $
  lT "c" $ lV "f" (TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lV "y" (TIdx 2) $ lV "x" (TIdx 4) $ Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование булевых значений в System F
boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0

fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0

tru = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 1

ifThenElse = lT "a" $ lV "v" boolT $ lV "x" (TIdx 1) $ lV "y" (TIdx 2) $ Idx 2 :@> TIdx 3 :@: Idx 1 :@: Idx 0

notF = lV "v" boolT $ lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 3 :@> TIdx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" $ (TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0

natAbs body = lT "a" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) body

zero = natAbs $ Idx 0

one = natAbs $ Idx 1 :@: Idx 0

two = natAbs $ Idx 1 :@: (Idx 1 :@: Idx 0)

three = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))

four = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))

five = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))

six = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))

seven = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))

eight = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))

nine =
  natAbs $
  Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))))

ten =
  natAbs $
  Idx 1 :@:
  (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))))

------------------------------------
validEnv :: Env -> Bool
validEnv [] = True
validEnv (x:xs) =
  case x of
    (VDecl sym t) -> (xs ||- t) && validEnv xs
    (TDecl _)     -> validEnv xs

(||-) :: Env -> Type -> Bool
xs ||- (TIdx x) =
  case atMay xs x of
    (Just (TDecl _)) -> True
    _                -> False
xs ||- (l :-> r) = (xs ||- l) && (xs ||- r)
xs ||- (ForAll sym t) = ((TDecl sym) : xs) ||- t

atMay :: [a] -> Int -> Maybe a
atMay [] _       = Nothing
atMay (x:xs) 0   = Just x
atMay (x:xs) idx = atMay xs (idx - 1)

--data Type = TIdx Int         -- типовой атом как индекс Де Брауна
--          | Type :-> Type    -- стрелочный тип
--          | ForAll Symb Type
shiftT :: Int -> Type -> Type
shiftT val t = go 0 val t
  where
    go cutOff val (TIdx x)
      | x >= cutOff = TIdx $ x + val
    go cutOff val i@(TIdx x) = i
    go cutOff val (t1 :-> t2) = (go cutOff val t1) :-> (go cutOff val t2)
    go cutOff val (ForAll sym t) = ForAll sym $ go (cutOff + 1) val t

substTT :: Int -> Type -> Type -> Type
substTT j sigma (TIdx x)
  | x == j = sigma
substTT j sigma i@(TIdx x) = i
substTT j sigma (t1 :-> t2) = (substTT j sigma t1) :-> (substTT j sigma t2)
substTT j n (ForAll sym t) = ForAll sym $ substTT (j + 1) (shiftT 1 n) t

infer :: Env -> Term -> Maybe Type
infer env t = inferHelper env t

inferHelper :: Env -> Term -> Maybe Type
inferHalper env (Idx x)
  | validEnv env && (length env > x) =
    case env !! x of
      (VDecl sym t) -> Just $ t
      _             -> Nothing

inferHelper env (t1 :@: t2) = do
  leftType <- inferHelper env t1
  rightType <- inferHelper env t2
  case leftType of
    (l :-> r) ->
      if l /= rightType
        then Nothing
        else return $ r
    _ -> Nothing
inferHelper env (Lmb v@(VDecl sym t) body)
  | (env ||- t) = do
    bodyType <- inferHelper (v : env) body
    return $ t :-> shiftT (-1) bodyType
inferHelper env (Lmb v@(TDecl sym) body) = do
  bodyType <- inferHelper (v : env) body
  return $ ForAll sym bodyType
inferHelper env (term :@> t)
  | (env ||- t) = do
    termType <- inferHelper env term
    case termType of
      (ForAll sym t') -> Just $ shiftT (-1) $ substTT 0 (shiftT 1 t) t'
      _               -> Nothing
inferHelper _ _ = Nothing
