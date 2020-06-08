module Stack

import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push: Integer -> StackCmd () hieght (S hieght)
  Pop: StackCmd Integer (S hieght) hieght
  Top: StackCmd Integer (S hieght) (S hieght)

  Pure: Integer -> StackCmd Integer state state
  (>>=): StackCmd a state1 state2 -> (a -> StackCmd Integer state2 state3) -> StackCmd Integer state1 state3


testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)


runStack : (stack: Vect inH Integer) -> StackCmd ty inH outH -> (ty, Vect outH Integer)
runStack stack (Push x) = ((), x::stack)
runStack (val::xs) Pop = (val, xs)
runStack (val::xs) Top = (val, val::xs)

runStack stack (Pure x) = (x, stack)
runStack stack (x >>= f) = let (res, newStack) = runStack stack x
  in runStack newStack (f res)

readVectLen: Vect n String
readVectLen = ["test", "twenty"]
