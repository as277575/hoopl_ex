{- BASED ON:
 - ,,Hoopl: Dataflow Optimization Made Simple''
 -}

{- Instalacja Hoopl (obecnie 3.8.7.4) :
cabal update
cabal install cabal-install
cabal install containers
# ghc-pkg trust base
cabal install hoopl --ghc-options="-trust base"
-}

{- Uruchamianie przy pomocy ghci wymaga:
 - ghci -package ghc
 -}



import Compiler.Hoopl
import BlockId
import Cmm
import CmmNode
import Data.Set



{- Hoopl na przykładzie wyliczania dostępności zmiennych -}
{- ZACHĘCAM DO KRYTYKOWANIA MOJEGO KODU! -}



{- tutaj jakiś nasz własny opis zmiennych -}
type LocalVar = String
type GlobalVar = String
type VarSet = Set LocalVar

emptyVarSet :: VarSet
emptyVarSet = empty



{- Dataflow fact and operations
 - czyli to co chcielibyśmy wiedzieć dla pojedynczego wierzchołka w grafie 
 - tj. dla pojedynczej instrukcji kodu czwórkowego
-}
data AvailVars =
    UniverseMinus VarSet -- czyli wszystkie oprócz wymienionych
  | AvailVars VarSet -- czyli tylko te wymienione

{- i jakieś nasze operacje na tych faktach
 - (czyli nic ciekawego w tym akapicie) -}
extendAvail :: AvailVars -> LocalVar -> AvailVars -- add var to set
extendAvail (UniverseMinus varSet) localVar =
  UniverseMinus $ delete localVar varSet
extendAvail (AvailVars varSet) localVar =
  AvailVars $ insert localVar varSet
delFromAvail :: AvailVars -> LocalVar -> AvailVars -- remove var from set
delFromAvail (UniverseMinus varSet) localVar =
  UniverseMinus $ insert localVar varSet
delFromAvail (AvailVars varSet) localVar =
  AvailVars $ delete localVar varSet
elemAvail :: AvailVars -> LocalVar -> Bool -- set membership
elemAvail (UniverseMinus varSet) localVar =
  not $ member localVar varSet
elemAvail (AvailVars varSet) localVar =
  member localVar varSet
interAvail :: AvailVars -> AvailVars -> AvailVars -- set intersection
interAvail (UniverseMinus varSet1) (UniverseMinus varSet2) =
  UniverseMinus $ union varSet1 varSet2
interAvail (UniverseMinus varSet1) (AvailVars varSet2) =
  AvailVars $ difference varSet2 varSet1
interAvail (AvailVars varSet1) (UniverseMinus varSet2) =
  AvailVars $ difference varSet1 varSet2
interAvail (AvailVars varSet1) (AvailVars varSet2) =
  AvailVars $ intersection varSet1 varSet2
smallerAvail :: AvailVars -> AvailVars -> Bool -- compare sizes
smallerAvail availVars1 availVars2 =
  let varSet1 = case availVars1 of
          UniverseMinus varSet1' -> varSet1'
          AvailVars varSet1' -> varSet1'
  in let varSet2 = case availVars2 of
          UniverseMinus varSet2' -> varSet2'
          AvailVars varSet2' -> varSet2'
  in size varSet1 < size varSet2



{- Lattice -}
{- czyli opis naszego systemu wnioskowania o faktach -}
{- empty to początkowy fakt we wnioskowaniu - czyli wszystkie zmienne dostępne
 - add to operacja połączenia dwóch faktów - czyli przecięcie zbiorów -}
{- w dokumencie ,,dataflow made simple'' nie było jeszcze labelek, monady,
 - nicnierobiących typów Old/New-Fact oraz add miał inną kolejność argumentów
 -}
availVarsLattice :: SimpleUniqueMonad (DataflowLattice AvailVars)
availVarsLattice = do
  label <- freshLabel -- tylko do tego jest potrzebna monada
  let empty = UniverseMinus emptyVarSet
  let add label (OldFact old) (NewFact new)  = let join = interAvail new old in
        (if smallerAvail join old then SomeChange else NoChange, join)
  return $ DataflowLattice "" empty add



{- Transfer functions -}
newtype LastOuts a = LastOuts [(BlockId, a)]
data ForwardTransfers m l a = ForwardTransfers
 {ft_first_out :: BlockId -> a -> a,
  ft_middle_out :: m -> a -> a,
  ft_last_outs :: l -> a -> LastOuts a}
{- 
 data BackTransfers m l a = BackTransfers
 {bt_first_in :: Block -> a -> a,
  bt_middle_in :: m -> a -> a,
  bt_last_in :: l -> (BlockId -> a) -> a}
-}

availTransfers :: ForwardTransfers Cmm.Middle CmmLast AvailVars
availTransfers = ForwardTransfers (flip const) middleAvail lastAvail
{-
middleAvail :: CmmMiddle -> AvailVars -> AvailVars
middleAvail (MidAssign (CmmLocal x) (CmmLoad l)) avail | isStackSlotOf l x =
  extendAvail avail x
middleAvail (MidAssign lhs _expr) avail = foldVarsDefd delFromAvail avail lhs

lastAvail :: CmmLast -> AvailVars -> LastOuts AvailVars
lastAvail (LastCall _ (Just k) _ _) _ = LastOuts [(k, AvailVars emptyVarSet)]
lastAvail l avail = LastOuts $ map (\id -> (id, avail)) $ succs l
-}

