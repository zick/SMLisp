val kLPar = #"("
val kRPar = #")"
val kQuote = #"'"

datatype obj =
    NIL
  | NUM of int
  | SYM of string
  | ERROR of string
  | CONS of obj * obj
  | SUBR of obj -> obj
  | EXPR of obj * obj * obj

fun safeCar obj =
  case obj of
       CONS(a, d) => a
     | _ => NIL

fun safeCdr obj =
  case obj of
       CONS(a, d) => d
     | _ => NIL

val symTable = ref [("nil", NIL)]
fun lookupSym (_, []) = NONE
  | lookupSym (str1, (str2, sym)::rest) =
      if str1 = str2 then SOME sym
      else lookupSym (str1, rest)
fun makeSym str =
  case lookupSym (str, !symTable) of
       SOME sym => sym
     | NONE =>
         let val ret = SYM str in
           symTable := (str, ret)::(!symTable);
           ret
         end

fun isSpace c =
  c = #"\t" orelse c = #"\r" orelse c = #"\n" orelse c = #" "

fun isDelimiter c =
  c = kLPar orelse c = kRPar orelse c = kQuote orelse isSpace c

fun skipSpaces str =
  implode (foldr (fn(x, y) => if isSpace x then y else x::y) [] (explode str))

fun tryToParseNumChar c =
  if #"0" <= c andalso c <= #"9" then SOME (ord c - ord #"0") else NONE

fun tryToParseNum ([], n) = SOME n
  | tryToParseNum (c::rest, n) =
      case tryToParseNumChar c of
           SOME x => tryToParseNum (rest, x + n * 10)
         | NONE => NONE

fun makeNumOrSym str =
  case explode str of
       c::rest =>
         let
           val lst = if c = #"-" then rest else c::rest
           val sign = if c = #"-" then ~1 else 1
         in
           case tryToParseNum (lst, 0) of
                SOME n => NUM (n * sign)
              | NONE => SYM str
         end
     | _ => NIL

fun position (_, [], _) = NONE
  | position (f, key::rest, n) =
      if (f key) then SOME n else position (f, rest, n + 1)

fun readAtom str =
  case position (isDelimiter, explode str, 0) of
       SOME n =>
         (makeNumOrSym (substring(str, 0, n)), substring(str, n, size str - n))
     | NONE => (makeNumOrSym str, "")

fun read str =
  case explode (skipSpaces str) of
       [] => (ERROR "empty input", "")
     | x::xs =>
         if x = kRPar then (ERROR ("invalid syntax:" ^ str), "")
         else if x = kLPar then (ERROR "noimpl", "")
         else if x = kQuote then (ERROR "noimpl", "")
         else readAtom (implode (x::xs))

fun first (x, y) = x
fun second (x, y) = y

fun repl prompt =
  (TextIO.print prompt;
   case TextIO.inputLine TextIO.stdIn of
        SOME line => (read line; repl prompt)
      | NONE => ())

fun run _ = repl "> "
