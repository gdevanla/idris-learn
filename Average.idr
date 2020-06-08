module Average

average : (str1: String) -> Double
average str =  let
  numWords = Prelude.List.length (words str)
  totalLength = sum (map Prelude.Strings.length (words str))
  in
  cast totalLength / cast numWords
