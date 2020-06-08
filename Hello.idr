module Main

import Average
import Data.Vect

data Format = Number Format
  | Str Format
  | Lit String Format
  | End

PrintfType : Format -> Type
PrintfType (Number x) = (i: Int) -> PrintfType x
PrintfType (Str x) = (s: String) -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String


printfFmt : (fmt: Format) -> (acc: String) -> PrintfType fmt
printfFmt (Number x) acc = \i => printfFmt x (acc ++ show i)
printfFmt (Str x) acc = \s => printfFmt x (acc ++ s)
printfFmt (Lit x y) acc = printfFmt y (acc ++ x)
printfFmt End acc = acc



TupleVect : (n: Nat) -> Type -> Type
TupleVect Z _ = ()
TupleVect (S k) t = (Nat, TupleVect k t)

test: TupleVect 4 Nat
test = (1, 2, 3, 4, ())



-- C-c C-t - Type-check name
-- C-c C-s - Add clause (add definition)
-- C-c C-d - Documentation
-- C-c C-l - List holes
-- C-c C-a Seach expressions
-- case-split

showAve : (str1 : String) -> String
showAve str = (show "test")

data DataStore : Type where
  MkData : (size: Nat) -> (items: Vect size String) -> DataStore

size: DataStore -> Nat
size (MkData s i) = s

items: (store: DataStore) -> Vect (size store) String
items (MkData size items) = items

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (addToData items) where
  addToData : Vect old String -> Vect (S old) String
  addToData [] = [newitem]
  addToData (x :: xs) = x :: addToData xs


data Command = Add String
  | Get Integer
  | Quit



parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
  False => Nothing
  True => Just (Get (cast val))
parseCommand "quit" _ = Just Quit
parseCommand _ _ = Just Quit


parse : (input : String) -> Maybe Command
parse input = case (Prelude.Strings.span (/= ' ') input) of
  (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos: Integer) -> (store: DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
  case integerToFin pos (size store) of
    Nothing => Just ("out of range\n", store)
    Just id => Just (index id store_items ++ "\n", store)


processCommand : Command -> DataStore -> Maybe (String, DataStore)
processCommand (Add x) ds = Just ("ID " ++ (show (size ds)) ++ "\n", addToStore ds x)
processCommand (Get x) ds = getEntry x ds
processCommand Quit _ = Nothing


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput ds s = case parse s of
  Nothing => Just ("Invalid command " ++ s ++ "\n", ds)
  Just command => processCommand command ds


main : IO ()
main = replWith (MkData _ []) "Command:  " processInput

allLengths: List String -> List Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y


isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not (isEven k)


fourInts : Vect 4 Int
fourInts = [0, 1, 2, 3]

allLengthsV : Vect len String -> Vect len Nat
allLengthsV [] = []
allLengthsV (word :: words) = length words :: allLengthsV words

insert : Ord elem => (x: elem) -> (Vect len elem) -> (Vect (S len) elem)
insert x [] = [x]
insert x (y :: xs) = case  x < y of
                          False => y :: insert x xs
                          True => x :: y :: xs

--insert x (y :: xs) = if x < y then x :: y :: xs else y :: insert y xs

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in
  insert x xsSorted


length_1 : List a -> Nat
length_1 [] = 0
length_1 (x :: xs) = 1 + (length_1 xs)

reverse_1  : List a -> List a
reverse_1 [] = []
reverse_1 (x :: xs) = reverse_1 xs ++ [x]


map1 : (a -> b) -> List a -> List b
map1 f [] = []
map1 f (x :: xs) = f x :: map f xs

map2 : (a -> b) -> Vect len a -> Vect len b
map2 f [] = []
map2 f (x :: xs) = f x :: map2 f xs

createEmpties: Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeHelper: (x : Vect n elem) ->
                 (xsTrans : Vect n (Vect k elem)) ->
                 Vect n (Vect (S k) elem)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys


transposeMat: Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
  zipWith (::) x xsTrans

transposeV : Vect n elem -> Vect n (Vect 1 elem)
transposeV [] = []
transposeV (x :: xs) = [x] :: transposeV xs

addMatrix: Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = let added = addMatrix xs ys in
  (zipWith (+) x y) :: added

data Direction = North
  | East
  | South
  | West


tryIndex: Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
  Nothing => Nothing
  Just idx => Just (index idx xs)

data PowerSource = Petrol | Pedal

data Vehicle : PowerSource -> Type where
  Bicycle: Vehicle Pedal
  Car: (fuel: Nat) -> Vehicle Petrol
  Bus: (fuel: Nat) -> Vehicle Petrol

wheels: Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4

refuel: Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200



--zip (+) x y :: ?hole1

--addMatrix [] = ?addMatrix_rhs_1
--addMatrix (x :: xs) = let xs_added = addMatrix xs in






-- StringOrInt : Bool -> Type
-- StringOrInt x = case x of
--   True => String
--   False => Int

-- getStringOrInt : (x : Bool) -> StringOrInt x
-- getStringOrInt x = case x of
--   True => ?xTrueType
--   False => ?yFalseType
