val kLPar = #"("
val kRPar = #")"
val kQuote = #"'"

datatype obj =
    NIL
  | NUM of int
  | SYM of string
  | ERROR of string
  | CONS of ((obj ref) * (obj ref)) ref
  | SUBR of obj -> obj
  | EXPR of obj * obj * obj

fun safeCar obj =
  case obj of
       CONS(ref(ref a,  ref d)) => a
     | _ => NIL

fun safeCdr obj =
  case obj of
       CONS(ref(ref a,  ref d)) => d
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

fun makeCons a d = CONS(ref(ref a, ref d))

fun nreconc lst tail =
  case lst of
       CONS(ref(a, d)) =>
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
     | NONE => makeSym str

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
    (elm, next) =>
      (makeCons (makeSym "quote") (makeCons elm NIL), next)
and readList str acc =
  case (explode (skipSpaces str)) of
       [] => (ERROR "unfinished parenthesis", "")
     | c::rest =>
         if c = kRPar then (nreverse acc, implode rest)
         else
         case read str of
              (ERROR e, next) => (ERROR e, next)
            | (elm, next) => readList next (makeCons elm acc)

fun printObj obj =
  case obj of
       NIL => "nil"
     | NUM n => Int.toString(n)
     | SYM s => s
     | ERROR s => "<error: " ^ s ^ ">"
     | CONS _ => "(" ^ (printList obj "" "") ^ ")"
     | SUBR(_) => "<subr>"
     | EXPR(_, _, _) => "<expr>"
and printList obj delimiter acc =
  case obj of
       CONS(ref(ref a, ref d)) =>
         printList d " " (acc ^ delimiter ^ printObj a)
     | NIL => acc
     | _ => acc ^ " . " ^ printObj obj

fun findVarInFrame str alist =
  case safeCar (safeCar alist) of
       SYM k => if k = str then safeCar alist
                else findVarInFrame str (safeCdr alist)
     | _ => NIL

fun findVar sym env =
  case (env, sym) of
       (CONS(ref(ref a, ref d)), SYM str) =>
         (case findVarInFrame str a of
               NIL => findVar sym d
             | pair => pair)
    | _ => NIL

val gEnv = makeCons NIL NIL

fun addToEnv sym value env =
  case env of
       CONS(ref(a, d)) => a := makeCons (makeCons sym value) (!a)
     | _ => ()

fun eval obj env =
  case obj of
       SYM _ =>
         (case findVar obj env of
               NIL => ERROR ((printObj obj) ^ " has no value")
             | pair => safeCdr(pair))
     | CONS _ => ERROR "noimpl"
     | _ => obj

fun first (x, y) = x
fun second (x, y) = y

fun repl prompt =
  (TextIO.print prompt;
   case TextIO.inputLine TextIO.stdIn of
        SOME line =>
          (print ((printObj (eval(first(read line)) gEnv)) ^ "\n");
           repl prompt)
      | NONE => ())

fun run _ = (
  addToEnv (makeSym "t") (makeSym "t") gEnv;
  repl "> ")
