module Main

import Data.Vect

data EqNat : (num1: Nat)-> (num2: Nat) -> Type where
  Same : (num: Nat) -> EqNat num num

-- checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
-- checkEqNat Z Z = ?checkEqNat_rhs_3
-- checkEqNat Z (S k) = ?checkEqNat_rhs_4
-- checkEqNat (S k) num2 = ?checkEqNat_rhs_2


sameAs : (k: Nat) -> (j: Nat) -> (eq: EqNat k j) -> EqNat (S k) (S j)
sameAs j j (Same j) = Same (S j)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
  Nothing => Nothing
  Just eq => Just (sameAs _ _ eq)

exactLength : (len: Nat) -> (input: Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
            Nothing => Nothing
            Just (Same len) => Just input

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons {xs = []} {ys = []} prf = Refl
same_cons {xs = []} {ys = (x :: xs)} prf = cong prf
same_cons {xs = (x :: xs)} {ys = []} prf = cong prf
same_cons {xs = (x :: xs)} {ys = (y :: ys)} prf = cong prf

same_lists : {xs : List a} -> {ys : List a} ->  (x = y) -> (xs = ys) -> (x :: xs) = (y :: ys)
same_lists {x = x} {y = x} Refl prf1 = cong prf1

data ThreeEq : (x: Nat) -> (y: Nat) -> (z: Nat) -> Type where
  SameThree : (x: Nat) -> ThreeEq x x x

allSameS : (x, y, z: Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS k k k (SameThree k) = SameThree (S k)


myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) = let rev_xs = myReverse xs
                                    result = rev_xs ++ [x] in
                                    rewrite plusCommutative 1 k in result

myReverse1 : Vect n elem -> Vect n elem
myReverse1 [] = []
myReverse1 (x :: xs) = reverseProof (myReverse xs ++ [x]) where
           reverseProof: Vect (len + 1) elem -> Vect (S len) elem
           reverseProof {len} xs = rewrite plusCommutative 1 len in xs

appendnil : (Vect m elem) -> (Vect (plus m 0) elem)
appendnil {m} elem = rewrite plusZeroRightNeutral m in elem


append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append [] ys = appendnil ys
append (x :: xs) ys = ?append_proof (x :: append xs ys)


-- append [] ys = ?append_rhs_1append (x :: xs) ys = ?append_rhs_2

data VElem : (value : a ) -> (xs: Vect k a) -> Type where
  Here: VElem x (x::xs)
  There: (later: VElem x xs) -> VElem x (y::xs)


-- maryInVector : VElem "Mary" ["Peter", "Paul", "Mary"]
-- maryInVector = There (There Here)

Uninhabited (VElem x []) where
  uninhabited x impossible

removeElem : (value: a) -> (xs: Vect (S n) a) -> (prf: VElem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) =  absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

removeElem_auto : (value: a) -> (xs: Vect (S n) a) -> {auto prf: VElem value xs} -> Vect n a
removeElem_auto value (value :: ys) {prf=Here} = ys
removeElem_auto {n = Z} value (y :: []) {prf=There later} =  absurd later
removeElem_auto {n = (S k)} value (y :: ys) {prf=There later} = y :: removeElem_auto value ys
