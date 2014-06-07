val kLPar = #"("
val kRPar = #")"
val kQuote = #"'"

datatype obj =
    NIL
  | NUM of int
  | SYM of string
  | ERROR of string
  | CONS of (obj ref) * (obj ref)
  | SUBR of obj -> obj
  | EXPR of obj * obj * obj

fun safeCar obj =
  case obj of
       CONS(a, d) => !a
     | _ => NIL

fun safeCdr obj =
  case obj of
       CONS(a, d) => !d
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

fun nreconc lst tail =
  case lst of
       CONS(a, d) =>
         let val tmp = !d in
           d := tail;
           nreconc tmp lst
         end
     | _ => tail
fun nreverse lst =
  nreconc lst NIL

fun isSpace c =
  c = #"\t" orelse c = #"\r" orelse c = #"\n" orelse c = #" "

fun isDelimiter c =
  c = kLPar orelse c = kRPar orelse c = kQuote orelse isSpace c

fun skipSpacesList lst =
  case lst of
       [] => []
     | x::xs => if isSpace(x) then skipSpacesList xs
                else lst
fun skipSpaces str =
  implode (skipSpacesList (explode str))

fun makeNumOrSym str =
  case Int.fromString str of
       SOME n => NUM n
     | NONE => SYM str

fun position (_, [], _) = NONE
  | position (f, key::rest, n) =
      if (f key) then SOME n else position (f, rest, n + 1)

fun readAtom str =
  case position (isDelimiter, explode str, 0) of
       SOME n =>
         (makeNumOrSym (substring(str, 0, n)), substring(str, n, size str - n))
     | NONE => (makeNumOrSym str, "")

fun read str =
  let val str1 = skipSpaces str
  in
    case explode str1 of
         [] => (ERROR "empty input", "")
       | x::xs =>
           if x = kRPar then (ERROR ("invalid syntax:" ^ str1), "")
           else if x = kLPar then
             readList (substring(str1, 1, size str1 - 1)) NIL
           else if x = kQuote then
             readQuote (substring(str1, 1, size str1 - 1))
           else readAtom (implode (x::xs))
  end
and readQuote str =
  case read str of
    (elm, next) => (CONS(ref (SYM "quote"), ref (CONS(ref elm, ref NIL))), next)
and readList str acc =
  case (explode (skipSpaces str)) of
       [] => (ERROR "unfinished parenthesis", "")
     | c::rest =>
         if c = kRPar then (nreverse acc, implode rest)
         else
         case read str of
              (ERROR e, next) => (ERROR e, next)
            | (elm, next) => readList next (CONS(ref elm, ref acc))

fun printObj obj =
  case obj of
       NIL => "nil"
     | NUM n => Int.toString(n)
     | SYM s => s
     | ERROR s => "<error: " ^ s ^ ">"
     | CONS(a, d) => "(" ^ (printList obj "" "") ^ ")"
     | SUBR(_) => "<subr>"
     | EXPR(_, _, _) => "<expr>"
and printList obj delimiter acc =
  case obj of
       CONS(a, d) =>
         printList (!d) " " (acc ^ delimiter ^ printObj (!a))
     | NIL => acc
     | _ => acc ^ " . " ^ printObj obj

fun first (x, y) = x
fun second (x, y) = y

fun repl prompt =
  (TextIO.print prompt;
   case TextIO.inputLine TextIO.stdIn of
        SOME line => (print ((printObj (first(read line))) ^ "\n"); repl prompt)
      | NONE => ())

fun run _ = repl "> "
