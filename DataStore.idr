module Main

import Data.Vect

-- data DataStore: Type -> Type where
--   MkData : (size : Nat) -> (items : Vect size schema) -> DataStore schema

infixr 5 .+.

data Schema = SString
     | SInt
     | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

data DataStore : Type where
  MkData : (schema : Schema) -> (size : Nat) -> (items  : Vect size (SchemaType schema)) -> DataStore

size : DataStore -> Nat
size (MkData schema' size' items') = size'

schema : DataStore -> Schema
schema (MkData schema' _ _) = schema'

items : (store: DataStore) -> Vect (size store) (SchemaType (schema store))
items (MkData _ _ items') = items'

addToStore : (store: DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData schema size items) newitem = MkData schema _ (addToData items) where
  addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
  addToData [] = [newitem]
  addToData (x :: xs) = x :: addToData xs

display: SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (item1, item2) =
  (display item1) ++ ", " ++ (display item2)


parsePrefix : (schema: Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString x = getQuoted (unpack x) where
  getQuoted : List Char -> Maybe (String, String)
  getQuoted ('"':: xs) = case span (/= '"') xs of
    (quoted, '"':: rest) => Just (pack quoted, ltrim (pack rest))
    _ => Nothing
parsePrefix SInt x = case Prelude.Strings.span isDigit x of
  ("", rest) => Nothing
  (num, rest) => Just (cast num, ltrim rest)
parsePrefix (y .+. z) x = do
  (res1, rest) <- parsePrefix y x
  (res2, rest') <- parsePrefix z rest
  pure ((res1, res2), rest')


parseBySchema : (schema: Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema str = case parsePrefix schema str of
  Just (res, "") => Just res
  Just _ => Nothing
  Nothing => Nothing

getEntry : (pos: Integer) -> (store: DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
  case integerToFin pos (size store) of
    Nothing => Just ("out of range\n", store)
    Just id => Just (display (index id store_items), store)

data Command : Schema -> Type where
  Add : (SchemaType schema) -> Command schema
  Get : Integer -> Command a
  Quit: Command a

parseCommand : (schema: Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" str = case parseBySchema schema str of
  Just restok => Just (Add restok)
  Nothing => Nothing
parseCommand schema "get" val = case all isDigit (unpack val) of
  False => Nothing
  True => Just (Get (cast val))
parseCommand schema "quit" _ = Just Quit
parseCommand _ _ _ = Just Quit





-- processCommand : Command schema -> DataStore -> Maybe (String, DataStore)
-- processCommand (Add x) ds = Just (?show_size, addToStore ds x)
-- processCommand (Get x) ds = getEntry x ds
-- processCommand Quit _ = Nothing

-- processInput : DataStore -> String -> Maybe (String, DataStore)
-- processInput ds s = case parse s of
--   Nothing => Just ("Invalid command " ++ s ++ "\n", ds)
--   Just command => processCommand command ds
