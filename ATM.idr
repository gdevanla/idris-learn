module ATM

import Data.Vect

PIN: Type
PIN = Vect 4 Integer

data ATMState = Ready | CardInserted | Session

data HasCard : ATMState -> Type where
  HasCI : HasCard CardInserted
  HasSession : HasCard Session

data PINCheck = CorrectPIN | IncorrectPIN

data ATMCmd : (ty: Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard: ATMCmd () Ready (const CardInserted)
  EjectCard: {auto prf: HasCard state} -> ATMCmd () state (const Ready)
  GetPIN: ATMCmd PIN CardInserted (const CardInserted)
  CheckPIN: PIN -> ATMCmd PINCheck CardInserted (\check => case check of
                                                              CorrectPIN => Session
                                                              IncorrectPIN => CardInserted)


  GetAmount: ATMCmd Nat state (const state)
  Dispense: (amount: Nat) -> ATMCmd () Session (const Session)

  Message: String -> ATMCmd () state (const state)

  Pure: (res: ty) -> ATMCmd ty (state_fn res) state_fn

  (>>=): ATMCmd a state1 state2_fn -> ((res: a) -> ATMCmd b (state2_fn res) state3_fn) -> ATMCmd b state1 state3_fn

insertEject : ATMCmd () Ready (const Ready)
insertEject = do InsertCard
                 EjectCard

-- atm: ATMCmd () Ready (const Ready)
-- atm = do InsertCard
--          pin <- GetPIN
--          pinOK <- CheckPIN pin
--          case pinOK of
--               CorrectPIN => do cash <- GetAmount
--                                Dispense cash
--                                EjectCard
--               IncorrectPIN => EjectCard

-- runATM: ATMCmd res inState outState_fn -> IO res
-- runATM InsertCard = do putStrLn "Please insert your card"
--                        x <- getLine
--                        pure()
-- runATM EjectCard = putStrLn "Thank you"
-- runATM GetPIN = do putStr "Enter Pin"
--                    pure (the (Vect _ Integer) [1, 2, 3, 4])
-- runATM (CheckPIN pin) = if pin == [1, 2, 3, 4]
--                           then pure CorrectPIN
--                           else pure IncorrectPIN
-- runATM GetAmount = do putStr "How much would you like"
--                       x <- getLine
--                       pure (cast x)
-- runATM (Dispense amount) = putStrLn "Here is the amount"
-- runATM (Message msg) = putStrLn msg
-- runATM (Pure res) = pure res
-- runATM (x >>= f) = do res <- runATM x
--                       runATM (f res)
