val kLPar = #"("
val kRPar = #")"
val kQuote = #"'"

datatype obj =
    NIL
  | NUM of int
  | SYM of string
  | ERROR of string
  | CONS of ((obj ref) * (obj ref)) ref
  | SUBR of (obj -> obj) ref
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
  | lookupSym (str1 : string, (str2, sym)::rest) =
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

val symQuote = makeSym "quote"
val symIf = makeSym "if"
val symLambda = makeSym "lambda"
val symDefun = makeSym "defun"
val symSetq = makeSym "setq"
val symT = makeSym "t"

fun eqSym x y =
  case (x, y) of
       (SYM s1, SYM s2) => s1 = s2
     | _ => false

fun eqSym2 s1 y =
  case y of
       SYM s2 => s1 = s2
     | _ => false

fun makeCons a d = CONS(ref(ref a, ref d))

fun makeExpr args env = EXPR(safeCar args, safeCdr args, env)

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

fun pairlis lst1 lst2 acc =
  case (lst1, lst2) of
       (CONS(ref(ref a1, ref d1)), CONS(ref(ref a2, ref d2))) =>
         pairlis d1 d2 (makeCons (makeCons a1 a2) acc)
     | _ => nreverse acc

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

fun findVarInFrame sym alist =
  case safeCar (safeCar alist) of
       SYM k => if eqSym2 k sym then safeCar alist
                else findVarInFrame sym (safeCdr alist)
     | _ => NIL

fun findVar sym env =
  case env of
       CONS(ref(ref a, ref d)) =>
         (case findVarInFrame sym a of
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
     | CONS _ => evalCons obj env
     | _ => obj
and evalCons obj env =
  let val opr = safeCar obj
      val args = safeCdr obj
  in
    if eqSym symQuote opr then
      safeCar(args)
    else if eqSym symIf opr then (
      case eval (safeCar args) env of
        NIL => eval (safeCar(safeCdr(safeCdr args))) env
      | _ => eval (safeCar(safeCdr args)) env)
    else if eqSym symLambda opr then
      makeExpr args env
    else if eqSym symDefun opr then (
      addToEnv (safeCar args) (makeExpr (safeCdr args) env) gEnv;
      safeCar args)
    else if eqSym symSetq opr then
      let val value = eval (safeCar (safeCdr args)) env
          val sym = safeCar args
          val bind = findVar sym env
      in
        case bind of
             CONS(ref(a, d)) => d := value
           | _ => addToEnv sym value gEnv;
        value
      end
    else apply (eval opr env) (evlis args env NIL) env
  end
and evlis lst env acc =
  case lst of
    NIL => nreverse acc
  | _ => (
      case eval (safeCar lst) env of
        ERROR m => ERROR m
      | elm => evlis (safeCdr lst) env (makeCons elm acc))
and progn body env acc =
  case body of
       CONS(ref(ref a, ref d)) => progn d env (eval a env)
     | _ => acc
and apply f args env =
case (f, args) of
    ((ERROR m), _) => ERROR m
  | (_, ERROR m) => ERROR m
  | (SUBR(ref f1), _) => f1 args
  | (EXPR(a, b, e), _) => progn b (makeCons (pairlis a args NIL) e) NIL
  | _ => ERROR ((printObj f) ^ " is not function")

fun subrCar args = safeCar (safeCar args)

fun subrCdr args = safeCdr (safeCar args)

fun subrCons args = makeCons (safeCar args) (safeCar (safeCdr args))

fun objEq x y =
  case (x, y) of
       (NIL, NIL) => symT
     | (NUM a, NUM b) => if a = b then symT else NIL
     | (SYM a, SYM b) => if a = b then symT else NIL
     | (ERROR a, ERROR b) => if a = b then symT else NIL
     | (CONS a, CONS b) => if a = b then symT else NIL
     | (SUBR a, SUBR b) => if a = b then symT else NIL
     | (EXPR(a1, b1, c1), EXPR(a2, b2, c2)) => (
         case (objEq a1 a2, objEq b1 b2, objEq c1 c2) of
              (NIL, _, _) => NIL
            | (_, NIL, _) => NIL
            | (_, _, NIL) => NIL
            |  _ => symT)
     | _ => NIL
fun subrEq args = objEq (safeCar args) (safeCar (safeCdr args))

fun subrAtom args =
  case safeCar(args) of
       CONS _ => NIL
     | _ => symT

fun subrNumberp args =
  case safeCar(args) of
       NUM _ => symT
     | _ => NIL

fun subrSymbolp args =
  case safeCar(args) of
       SYM _ => symT
     | _ => NIL

fun subrAddOrMul f initVal =
  let fun doit args acc =
    case args of
         CONS(ref(ref(NUM num), ref rest)) => doit rest (f(acc, num))
       | CONS _ => ERROR "wrong type"
       | _ => NUM acc
  in fn args => doit args initVal end
val subrAdd = subrAddOrMul (fn (x, y) => x + y) 0
val subrMul = subrAddOrMul (fn (x, y) => x * y) 1

fun subrSubOrDivOrMod f =
  fn args =>
    case (safeCar args, safeCar(safeCdr args)) of
      (NUM x, NUM y) => NUM (f(x, y))
    | _ => ERROR "wrong type"
val subrSub = subrSubOrDivOrMod (fn (x, y) => x - y)
val subrDiv = subrSubOrDivOrMod (fn (x, y) => x div y)
val subrMod = subrSubOrDivOrMod (fn (x, y) => x mod y)

fun first (x, y) = x

fun repl prompt =
  (TextIO.print prompt;
   case TextIO.inputLine TextIO.stdIn of
        SOME line =>
          (print ((printObj (eval(first(read line)) gEnv)) ^ "\n");
           repl prompt)
      | NONE => ())

fun run _ = (
  addToEnv (makeSym "car") (SUBR(ref(subrCar))) gEnv;
  addToEnv (makeSym "cdr") (SUBR(ref(subrCdr))) gEnv;
  addToEnv (makeSym "cons") (SUBR(ref(subrCons))) gEnv;
  addToEnv (makeSym "eq") (SUBR(ref(subrEq))) gEnv;
  addToEnv (makeSym "atom") (SUBR(ref(subrAtom))) gEnv;
  addToEnv (makeSym "numberp") (SUBR(ref(subrNumberp))) gEnv;
  addToEnv (makeSym "symbolp") (SUBR(ref(subrSymbolp))) gEnv;
  addToEnv (makeSym "+") (SUBR(ref(subrAdd))) gEnv;
  addToEnv (makeSym "*") (SUBR(ref(subrMul))) gEnv;
  addToEnv (makeSym "-") (SUBR(ref(subrSub))) gEnv;
  addToEnv (makeSym "/") (SUBR(ref(subrDiv))) gEnv;
  addToEnv (makeSym "mod") (SUBR(ref(subrMod))) gEnv;
  addToEnv (makeSym "t") (makeSym "t") gEnv;
  repl "> ")
