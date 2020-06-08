module Main

import Data.Vect

-- check that all functions are total
  %default total

zeroNotSuc : (0 = S k) -> Void
zeroNotSuc Refl impossible

sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

noRec : (contra : (k=j)-> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat : (num1: Nat) -> (num2: Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSuc
checkEqNat (S k) Z = No sucNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
  Yes prf => Yes (cong prf)
  No contra => No (noRec contra)

--noWhere : (contra: Elem value xs -> Void) -> Elem value (x::xs) -> Void

noWhere : (notThere: Elem value xs -> Void) -> (notHere: value = x -> Void) -> Elem value (x::xs) -> Void
noWhere notThere notHere Here = notHere Refl
noWhere notThere notHere (There later) = notThere later

notInNil1: Elem value [] -> Void
notInNil1 Here impossible
notInNil1 (There _) impossible


isElem1 : DecEq a => (value: a) -> (xs: Vect n a) -> Dec (Elem value xs)
isElem1 value [] = No notInNil1
isElem1 value (x :: xs) = case decEq value x of
  Yes Refl => Yes Here
  No contra => case isElem1 value xs of
    Yes prof => Yes (There prof)
    No contra1 => No (noWhere contra1 contra)


-- data Elem : a -> Vect k a -> Type where
--   Here : Elem x (x :: xs)
--   There : (later : Elem x xs) -> Elem x (y :: xs)


data Elem1 : a -> List a -> Type where
  Here : Elem1 x (x::xs)
  There: (later: Elem1 x xs) -> Elem1 x (y :: ys)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

notInEmptyList : Last [] value -> Void
notInEmptyList LastOne impossible
notInEmptyList (LastCons _) impossible

notInLast : (contra: value = x -> Void) -> (Last [x] value) -> Void
notInLast contra LastOne = contra Refl
notInLast contra (LastCons prf) impossible

anotherContra : (contra : Last [] value) -> Void
anotherContra LastOne impossible
anotherContra (LastCons _) impossible

Uninhabited (Last [] a) where
  uninhabited LastOne impossible

notAnywhere : (contra: Last (x::xs) value -> Void) -> (Last (y::x::xs) value) -> Void
notAnywhere contra (LastCons prf) = contra prf


--notAnywhere contra LastOne = contra ?hole
--notAnywhere contra (LastCons prf) = contra prf

--notAnywhere contra LastOne = contra ?hole_2
--notAnywhere contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInEmptyList
isLast [x] value = case decEq value x of
       Yes Refl => Yes LastOne
       No contra => No (notInLast contra)
isLast (x :: y :: xs) value = case isLast (y :: xs) value of
  Yes prf => Yes (LastCons prf)
  No contra => No (notAnywhere contra)



-- game functions
removeElem_auto : (value: a) -> (xs: Vect (S n) a) -> {auto prf: Elem value xs} -> Vect n a
removeElem_auto value (value :: ys) {prf=Here} = ys
removeElem_auto {n = Z} value (y :: []) {prf=There later} =  absurd later
removeElem_auto {n = (S k)} value (y :: ys) {prf=There later} = y :: removeElem_auto value ys


data WordState : (guesses_remaing: Nat) -> (letters: Nat) -> Type where
  MkWordState: (word: String) -> (missing: Vect letters Char) -> WordState guessess_remaining letters

data Finished: Type where
  Lost: (game: WordState 0 (S letters)) -> Finished
  Won: (game: WordState (S guesses) 0) -> Finished


data ValidInput : List Char -> Type where
  Letter: (c: Char) -> ValidInput [c]

isValidNil : ValidInput [] -> Void
isValidNil (Letter _) impossible

isMoreChar : (ValidInput (c1::c2::cs)) -> Void
isMoreChar (Letter _) impossible


isValidInput : (cs: List Char) -> Dec (ValidInput cs)
isValidInput [] = No isValidNil
isValidInput (c::[]) = Yes (Letter c)
isValidInput (c1::c2::cs) = No isMoreChar


isValidString : (s: String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess: IO (x**ValidInput x)
readGuess = do putStr "Guess"
               x <- getLine
               case isValidString (toUpper x) of
                 Yes prf => pure (_ ** prf)
                 No contra => do putStrLn "Invalid guess"
                                 readGuess
processGuess : (letter: Char) ->
  WordState (S guesses) (S letters) ->
  Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = case isElem letter missing of
  Yes prf => Right (MkWordState word (removeElem_auto letter missing))
  No contra => Left (MkWordState word missing)


game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st = do
  (_ ** Letter letter) <- readGuess
  case processGuess letter st of
    Left l => do putStrLn "Wrong"
                 case guesses of
                   Z => pure (Lost l)
                   S k => game l
    Right r => do putStrLn "Right!"
                  case letters of
                    Z => pure (Won r)
                    S k => game r
