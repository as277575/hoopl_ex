{-# LANGUAGE ScopedTypeVariables, GADTs, NoMonomorphismRestriction, NamedFieldPuns #-}

import Compiler.Hoopl
import Data.Map as Map

type Monada = CheckingFuelMonad (SimpleUniqueMonad)
type IdLabelMap = Map String Label
data LabelMapM a = LabelMapM (IdLabelMap -> Monada (IdLabelMap, a))
instance Monad LabelMapM where
  return x = LabelMapM (\m -> return (m, x))
  LabelMapM f1 >>= k = LabelMapM (\m -> do (m', x) <- f1 m
                                           let (LabelMapM f2) = k x
                                           f2 m')

labelFor :: String -> LabelMapM Label
labelFor l = LabelMapM f
  where f m = case Map.lookup l m of
                Just l' -> return (m, l')
                Nothing -> do l' <- freshLabel
                              let m' = insert l l' m
                              return (m', l')
run :: LabelMapM a -> Monada a
run (LabelMapM f) = f Map.empty >>= return . snd

data Lit = Bool Bool | Int Integer deriving (Eq, Show)
type Var = String
data Expr
 = Lit Lit
 | Var Var
 | Load Expr
 | Binop BinOp Expr Expr
  deriving Show
data BinOp = Add | Sub | Mul | Eq | Ne | Lt | Gt | Lte | Gte
  deriving Show

data Proc = Proc {
  name :: String,
  args :: [Var],
  entry :: Label,
  body :: Graph Node C C
}

data Node e x where
  Label :: Label -> Node C O
  Assign :: Var -> Expr -> Node O O
  Store :: Expr -> Expr -> Node O O
  Branch :: Label -> Node O C
  Cond :: Expr -> Label -> Label -> Node O C
  Call :: [Var] -> String -> [Expr] -> Label -> Node O C
  Return :: [Expr] -> Node O C

instance Show (Node e x) where
  show (Label l) = "NLabel " ++ show l
  show (Assign v e) = "NAssign " ++ show v ++ " " ++ show e
  show (Return l) = "NReturn " ++ show l
  show _ = "N... "

instance NonLocal Node where
  entryLabel (Label l) = l
  successors (Branch l) = [l]
  successors (Cond _ t f) = [t, f]
  successors (Call _ _ _ l) = [l]
  successors (Return _) = []

nodeToG :: Node e x -> Graph Node e x
nodeToG n@(Label _) = mkFirst n
nodeToG n@(Assign _ _) = mkMiddle n
nodeToG n@(Store _ _) = mkMiddle n
nodeToG n@(Branch _) = mkLast n
nodeToG n@(Cond _ _ _) = mkLast n
nodeToG n@(Call _ _ _ _) = mkLast n
nodeToG n@(Return _) = mkLast n

grafTestowy :: LabelMapM (Graph Node C C)
grafTestowy = do
  labelka <- labelFor "labelka"
  let poczatkowy = nodeToG $ Label labelka
  let przypisanie1 = nodeToG $ Assign "x" (Lit $ Int 5)
  let przypisanie2 = nodeToG $ Assign "y" (Var "x")
  let przypisanie3 = nodeToG $ Assign "z" (Var "y")
  let koncowy = nodeToG $ Return [Var "z"]
  return $ poczatkowy <*> przypisanie1 <*> przypisanie2
    <*> przypisanie3 <*> koncowy

proceduraTestowa :: LabelMapM Proc
proceduraTestowa = do
  g <- grafTestowy
  label <- labelFor "labelka"
  return $ Proc {
    name = "procedurka",
    args = [],
    entry = label,
    body = g
  }
  
type ConstFact = Map Var (WithTop Lit)
constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice {
  fact_name = "Const var value",
  fact_bot = empty,
  fact_join = joinMaps (extendJoinDomain constFactAdd) }
  where
    constFactAdd _ (OldFact old) (NewFact new) =
      if new == old then (NoChange, PElem new)
      else               (SomeChange, Top)

initFact :: [Var] -> ConstFact
initFact vars = fromList $ [(v, Top) | v <- vars] 

varHasLit :: FwdTransfer Node ConstFact
varHasLit = mkFTransfer ft
  where
    ft :: Node e x -> ConstFact -> Fact x ConstFact
    ft (Label _) f = f
    ft (Assign x (Lit k)) f = insert x (PElem k) f
    ft (Assign x _) f = insert x Top f
    ft (Store _ _) f = f
    ft (Branch l) f = mapSingleton l f
    ft (Cond (Var x) tl fl) f
      = mkFactBase constLattice
        [(tl, insert x (PElem (Bool True)) f),
         (fl, insert x (PElem (Bool False)) f)]
    ft (Cond _ tl fl) f = mkFactBase constLattice [(tl, f), (fl, f)]
    ft (Call vs _ _ bid) f = mapSingleton bid (Prelude.foldl toTop f vs)
        where toTop f v = insert v Top f
    ft (Return _) _ = mapEmpty

type MaybeChange a = a -> Maybe a

constProp :: forall m. FuelMonad m => FwdRewrite m Node ConstFact
constProp = mkFRewrite cp
  where
    cp :: Node e x -> ConstFact -> m (Maybe (Graph Node e x))
    cp (Assign x (Var y)) f = return $ case Map.lookup y f of
      Just (PElem lit) -> Just $ nodeToG $ (Assign x (Lit $ lit))
      otherwise -> Nothing
    cp (Return [Var x]) f = return $ case Map.lookup x f of
      Just (PElem lit) -> Just $ nodeToG $ (Return [Lit $ lit])
      otherwise -> Nothing
    cp _ _ = return Nothing

constPropPass = FwdPass {
  fp_lattice = constLattice,
  fp_transfer = varHasLit,
  fp_rewrite = constProp
}


przejscie = do
  proc@(Proc {entry, body, args}) <- run proceduraTestowa
  (body', _, _) <- analyzeAndRewriteFwd constPropPass (JustC [entry]) body
                   (mapSingleton entry (initFact args))
  return body'

rezultat :: Graph Node C C
rezultat = runSimpleUniqueMonad $ runWithFuel 99999 przejscie

showRezultat :: String
showRezultat = showGraph show rezultat
