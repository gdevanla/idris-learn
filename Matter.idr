module Vending


data DoorState = DoorClosed | DoorOpen

data Matter = Solid | Liquid | Gas

data MatterOperation : Type -> Matter -> Matter -> Type where
    Melt: MatterOperation () Solid Liquid
    Boil: MatterOperation () Liquid Gas
    Condense: MatterOperation () Gas Liquid
    Freeze: MatterOperation () Liquid Solid

    Bind: MatterOperation a state1 state2 -> (a->MatterOperation b state2 state3) -> MatterOperation b state1 state3

(>>=) : MatterOperation a state1 state2 -> (a->MatterOperation b state2 state3) -> MatterOperation b state1 state3
(>>=) = Bind

iceSteam : MatterOperation () Solid Gas
iceSteam = do Melt
              Boil
              Condense
              Freeze
              Melt
              Boil
