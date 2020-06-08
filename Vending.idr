module Vending


data DoorState = DoorClosed | DoorOpen

data DoorCmd : Type -> DoorState -> DoorState -> Type where
  Open: DoorCmd () DoorClosed DoorOpen
  Close: DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () a a
  Do1: DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd a state1 state3
  Pure1: ty -> DoorCmd ty state state


namespace DoorCmdDo
  (>>=) : DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd a state1 state3
  (>>=) = Do1

  Pure: ty -> DoorCmd ty state state
  Pure = Pure1

doorProg: DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              RingBell
              Close
              Pure ()

data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S g) g
  Pure2 : ty -> GuessCmd ty state state
  BindGuess : GuessCmd a state1 state2 -> (a -> GuessCmd b state2 state3) ->  GuessCmd b state1 state3

namespace GuessCmdDo
  (>>=) : GuessCmd a state1 state2 -> (a -> GuessCmd b state2 state3) ->  GuessCmd b state1 state3
  (>>=) = BindGuess

  Pure : ty -> GuessCmd ty state state
  Pure = Pure2

threeGuess : GuessCmd () 0 0
threeGuess = do Try 10
                Pure ()

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
     | VEND
     | CHANGE
     | REFILL Nat

data MachineCmd : Type ->
                  VendState ->
                  VendState -> Type where
     InsertCoin : MachineCmd () (pounds, chocs) (S pounds, chocs)
     Vend: MachineCmd () (S pounds, S chocs) (pounds, chocs)
     GetCoins : MachineCmd () (pounds, chocs) (Z, chocs)
     Refill : (bars: Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)

     Display : String -> MachineCmd () state state
     GetInput : MachineCmd (Maybe Input) state state

     Pure: ty -> MachineCmd ty state state
     (>>=): MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd a state1 state3

data MachineIO : VendState -> Type where
     Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do


mutual
  vend: MachineIO (pounds, chocs)
  vend {chocs = Z} = Display "Out of stock" >>= (\_ => machineLoop)

  vend {pounds = Z} = do Display "InsertCoin"
                         machineLoop
  vend {pounds = (S j)} {chocs = (S k)} = do Vend
                                             Display "Enjoy!"
                                             machineLoop


  refill: (num: Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill _ = do Display "Can't refill"
                machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop =
              do Just x <- GetInput
                      | Nothing => do Display "Invalid Input"
                                      machineLoop
                 case x of
                   COIN => do InsertCoin
                              machineLoop
                   VEND => vend
                   CHANGE => do GetCoins
                                Display "Change returned"
                                machineLoop
                   REFILL num => refill num
