type Symb = String 

infixr 3 :->

data Type = TVar Symb      -- типовый атом
          | Type :-> Type deriving (Read, Ord, Eq, Show)  -- стрелочный тип

type Ctx = [Type]

data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизирована
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор 
             Int    -- головная переменная как индекс Де Брауна
             [TNF] deriving (Show, Eq, Read, Ord)  -- бёмовы хвостики
            
tArr = TVar "a" :-> TVar "a"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"

tK = TVar "a" :-> TVar "b" :-> TVar "a"

tKast = TVar "a" :-> TVar "b" :-> TVar "b"

tBiNat = (TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBiBiNat = (TVar "a" :-> TVar "b") :-> (TVar "b" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBinTree = (TVar "a" :-> TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

hw3last1 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "a"

hw3last2 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "b"

t3 = ((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a"

contFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "d")
               :-> (TVar "b" :-> TVar "c") :-> TVar "d"

selFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "a") 
               :-> (TVar "b" :-> TVar "c") :-> TVar "b"

monsterT = (((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a") :-> TVar "a" :-> TVar "a"

fixT = (TVar "a" :-> TVar "a") :-> TVar "a"

peirceT = ((TVar "p" :-> TVar "q") :-> TVar "p") :-> TVar "p"

uncurry2List :: Type -> (Symb,[Type])
uncurry2List (TVar sym) = (sym, [])
uncurry2List (a :-> b) = let (sym, xs) =  uncurry2List b in (sym, a:xs)

uncurry2RevList :: Type -> (Symb,[Type])
uncurry2RevList t = let (sym, xs) = uncurry2List t in (sym, reverse xs)

isTerm :: TNF -> Bool
isTerm (Meta _) = False
isTerm (TNF _ _ xs) = all isTerm xs

unMeta :: Ctx -> TNF -> [TNF]
unMeta zetas tnf@(TNF ctx idx tails) | isTerm tnf = [tnf]
unMeta zetas tnf@(TNF ctx idx tails) = (TNF ctx idx) <$> (combinations m) where
                          m = (unMeta (ctx ++ zetas)) <$> tails
unMeta zetas m@(Meta t) = (\(idx, o, (a, q)) -> TNF newCTX idx (Meta <$> q)) <$> suitable where
                  (alpha, omegas) = uncurry2List t
                  (alpha', newCTX) = uncurry2RevList t
                  newCTX' = newCTX ++ zetas
                  suitable = filter (\(idx, t, (sym, terms)) -> sym == alpha) withIdx
                  withIdx = (\(term, idx) -> (idx, term, uncurry2List term)) <$> (zip newCTX' [0..])

combinations :: [[a]] -> [[a]]
combinations ([]:xs) = []
combinations ((x:xs):ys) =  ((x:) <$> (combinations ys)) ++ combinations (xs:ys)
combinations _ = [[]]

allTNFGens :: Type -> [[TNF]]
allTNFGens tau = go tau 0 where
  go tau 0 = [[Meta tau]]
  go tau n = if areAllTerms || null x then 
      (x:xs) 
    else 
      
    where
      (x:xs) = go tau (n-1)
      areAllTerms = all isTerm x