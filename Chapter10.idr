module Chapter10

import Data.Vect

-- describeList : List Int -> String
-- describeList [] = "Empty"
-- describeList (x::xs) = "Non-empty, tail " ++ show xs

-- data ListLast : List a -> Type where
--   Empty : ListLast []
--   NonEmpty: (xs: List a)-> (x:a) -> ListLast (xs ++ [x])

-- describeHelper : (input: List Int) -> (form: ListLast input) -> String
-- describeHelper [] Empty = ?describeHelper_rhs_1
-- describeHelper (xs ++ [x]) (NonEmpty xs x) = ?describeHelper_rhs_2


-- describeHelper [] form = ?describeHelper_rhs_1
-- describeHelper (_ :: _) Empty impossible
-- describeHelper (_ :: _) (NonEmpty _ _) impossible


--describeHelper [] Empty = "Empty"
--describeHelper (xs ++ [x]) (NonEmpty xs x) = ?hole

-- total
-- listLast : (xs: List a) -> ListLast xs
-- listLast [] = Empty
-- listLast (x :: xs) = case listLast xs of
--   Empty => NonEmpty [] x
--   NonEmpty ys y => NonEmpty (x::ys) y

-- describeListEnd : List Int -> String
-- describeListEnd input with (listLast input)
-- describeListEnd [] | Empty = "test"
-- describeListEnd (xs ++ [x]) | NonEmpty xs x = "test2"

-- recursive views
--data SnocList ty = Empty | Snoc (SnocList ty) ty

--reverseSnoc : SnocList ty -> List ty
--reverseSnoc Empty = []
--reverseSnoc (Snoc xs x) = x :: reverseSnoc xs

data SnocList : List a -> Type where
  Empty: SnocList []
  Snoc: (rec: SnocList xs) -> SnocList (xs ++ [x])


snocListHelp : (snoc: SnocList input) -> (rest: List a) -> SnocList (input ++ rest)
snocListHelp {input = input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input = input} snoc (x :: xs) =
  rewrite appendAssociative input [x] xs in
  snocListHelp (Snoc snoc {x}) xs


snocList : (input : List a) -> SnocList input
snocList xs = snocListHelp Empty xs

myReverseHelper : (input: List a) -> SnocList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

myReverse: List a -> List a
myReverse input = myReverseHelper input (snocList input)


--myReverse : List a -> List a
--myReverse xs = myReverseHelper xs (snocList input)

-- myReverseHelper (xs ++ [x]) (Snoc rec) = ?myReverseHelper_2
