structure ThreeCPS = struct
  (* Lexical scope label *)
  type label = int

  (* Stack frame index *)
  type stack_index = int

  (* Heap address *)
  type contour = int

  datatype lifetime = H | S | R

  datatype uvar = UVar of {
    name : string,
    lifetime : lifetime,
    binder : label
  }

  fun unUVar (UVar v) = v

  datatype cvar = CVar of {
    name : string,
    lifetime : lifetime,
    binder : label
  }

  fun unCVar (CVar v) = v

  datatype arg
    = ArgLam of ulam
    | ArgVar of uvar
    | ArgInt of int

  and cont
      = ContLam of clam
      | ContVar of cvar
      | ContHalt

  and ulam = Lambda of label * uvar list * cvar * cvar list * prog
  and clam = Cont of label * uvar * prog

  and prog
    = UApp of arg * arg list * cont * cont list
    | CApp of cont * arg
    | Letrec of label * (uvar * ulam) list * prog

  type hcenv = (label * contour) list
  type scenv = (label * stack_index) list

  datatype value
    = VInt of int
    | VFloat of real
    | VBool of bool
    | VCons of value * value
    | VNil
    | VBox of value ref
    | VClos of proc
    | VCont of contproc

  and proc
    = Primop of ((value list * (value -> result) * (value -> result) list) -> result)
    | Clos of ulam * hcenv * scenv

  and contproc
    = Halt
    | ContClos of clam * hcenv * scenv * int

  and result = Result of value

  type frame = (string * value ref) list

  type machine = {
    gen_contour : int ref,
    registers : frame, (* Register file *)
    stack : frame option DynamicArray.array, (* Frame index to frame *)
    heap : frame DynamicArray.array (* Heap address to frame *)
  }

  exception Eval of string

  fun fresh_contour (machine : machine) =
      let
          val c = !(#gen_contour machine)
          val () = (#gen_contour machine) := c + 1
      in
          c
      end

  fun replaceRegs ({gen_contour = gc, registers = _, stack = s, heap = h}, registers) =
      {gen_contour = gc, registers = registers, stack = s, heap = h}

  fun zip ([], []) = []
    | zip (x :: xs, y :: ys) = (x, y) :: zip (xs, ys)
    | zip _ = raise (Eval "Uneven lists")

  fun lookup ([], var) = raise (Eval "Variable is not found")
    | lookup ((k, v) :: xs, var) =
      if k = var then
          v
      else
          lookup (xs, var)

  fun lookupOpt ([], var) = NONE
    | lookupOpt ((k, v) :: xs, var) =
      if k = var then
          SOME (v, xs)
      else
          case lookupOpt (xs, var)
           of SOME (v', rest) => SOME (v', (k, v) :: rest)
            | NONE => NONE

  fun checkedSub (arr, idx) =
      let val size = DynamicArray.bound arr in
      if idx > DynamicArray.bound arr then
          raise (Eval (String.concat ["Out of bounds ", Int.toString size, " ", Int.toString idx]))
      else
          DynamicArray.sub (arr, idx)
      end

  fun a_u (ArgLam(ulam), beta, gamma, machine : machine) =
      VClos (Clos (ulam, beta, gamma))
    | a_u (ArgVar(UVar v), beta, gamma, machine) =
      (case #lifetime v
       of H =>
          !(lookup (checkedSub (#heap machine, lookup (beta, #binder v)), #name v))
        | S =>
          !(lookup (Option.valOf (DynamicArray.sub (#stack machine, lookup (gamma, #binder v))), #name v))
        | R =>
          !(lookup (#registers machine, #name v)))
    | a_u (ArgInt n, beta, gamma, machine) = VInt n

  fun a_c (ContLam(clam), beta, gamma, machine : machine) =
      VCont (ContClos (clam, beta, gamma, DynamicArray.bound (#stack machine) + 1))
    | a_c (ContVar(CVar v), beta, gamma, machine) =
      (case #lifetime v
        of H =>
           !(lookup (DynamicArray.sub (#heap machine, lookup (beta, #binder v)), #name v))
         | S =>
           !(lookup (Option.valOf (DynamicArray.sub (#stack machine, lookup (gamma, #binder v))), #name v))
         | R =>
           !(lookup (#registers machine, #name v)))
    | a_c (ContHalt, beta, gamma, machine) = VCont Halt

  fun stackIdx (ContClos(_, _, _, idx)) = idx
    | stackIdx Halt = 0

  fun stackTrim (stack, c1, cs) =
      let
          val len = List.foldl (fn(c, acc) => Int.max (stackIdx c, acc)) (stackIdx c1) cs
      in
          DynamicArray.truncate (stack, len)
      end

  fun assert_clos (VClos clos) = clos
    | assert_clos _ = raise (Eval "")

  fun assert_cont (VCont cont) = cont
    | assert_cont _ = raise (Eval "")

  fun makeUFrame pred (xs, args, k, ks, c, cs) =
      let
          val ks = k :: ks
          val cs = c :: cs
          val conts = zip (ks, cs)
          val conts = List.filter (fn (k, _) => pred (#lifetime (unCVar k))) conts
          val conts = List.map (fn (k, c) => (#name (unCVar k), ref (VCont c))) conts
          val users = zip (xs, args)
          val users = List.filter (fn (x, _) => pred (#lifetime (unUVar x))) users
          val users = List.map (fn (x, arg) => (#name (unUVar x), ref arg)) users
      in
          users @ conts
      end

  fun overwriteFrame ([], new) = new
    | overwriteFrame ((var, value) :: xs, new) =
      case lookupOpt (new, var)
       of NONE => (var, value) :: overwriteFrame (xs, new)
        | SOME (value', new) => (var, value') :: overwriteFrame (xs, new)

  fun eval (UApp(f, xs, q1, qs), beta, gamma, machine) =
    let
        val proc = assert_clos (a_u (f, beta, gamma, machine))
        val args = List.map (fn x => a_u (x, beta, gamma, machine)) xs
        val c = assert_cont (a_c (q1, beta, gamma, machine))
        val cs = List.map (fn c => assert_cont (a_c (c, beta, gamma, machine))) qs
        val () = stackTrim (#stack machine, c, cs)
    in
      apply_user (proc, args, c, cs, machine)
    end
    | eval (CApp(f, x), beta, gamma, machine) =
      let
          val c = assert_cont (a_c (f, beta, gamma, machine))
          val arg = a_u (x, beta, gamma, machine)
          val () = stackTrim (#stack machine, c, [])
      in
          apply_cont (c, arg, machine)
      end
    | eval (Letrec(l, bindings, tail), beta, gamma, machine) =
      let
          val contour = fresh_contour machine
          val toUpdate = List.map (fn (v, rhs) => (v, ref VNil, rhs)) bindings
          fun splitHSR [] = ([], [], [])
            | splitHSR ((tup as (v, refcell, rhs)) :: xs) =
              let
                  val (h, s, r) = splitHSR xs
              in
                  case #lifetime (unUVar v)
                   of H => (tup :: h, s, r)
                    | S => (h, tup :: s, r)
                    | R => (h, s, tup :: r)
              end
          val (h, s, r) = splitHSR toUpdate
          val hframe = List.map (fn (v, r, _) => (#name (unUVar v), r)) h
          val beta = (l, contour) :: beta
          val () = DynamicArray.update(#heap machine, contour, hframe)
          val sframe = List.map (fn (v, r, _) => (#name (unUVar v), r)) s
          val sz = DynamicArray.bound (#stack machine) + 1
          val () = DynamicArray.update (#stack machine, sz, SOME sframe)
          val gamma = (l, sz) :: gamma
          val regs =
              overwriteFrame
                  (#registers machine,
                   List.map (fn (v, r, _) => (#name (unUVar v), r)) r)
          fun update [] = ()
            | update ((_, r, ulam) :: xs) =
              let
                  val () = (r := VClos (Clos (ulam, beta, gamma)))
              in
                  update xs
              end
          val () = update toUpdate
      in
          eval (tail, beta, gamma, replaceRegs(machine, regs))
      end

  and apply_user (Clos(Lambda(l, xs, k, ks, pr), beta, gamma), args, c, cs, machine) =
      let
          val contour = fresh_contour machine
          val hframe = makeUFrame (fn H => true | _ => false) (xs, args, k, ks, c, cs)
          val beta = (l, contour) :: beta
          val () = DynamicArray.update(#heap machine, contour, hframe)
          val sframe = makeUFrame (fn S => true | _ => false) (xs, args, k, ks, c, cs)
          val sz = DynamicArray.bound (#stack machine) + 1
          val () = DynamicArray.update (#stack machine, sz, SOME sframe)
          val gamma = (l, sz) :: gamma
          val regs =
              overwriteFrame
                  (#registers machine,
                   makeUFrame (fn R => true | _ => false) (xs, args, k, ks, c, cs))
      in
          eval (pr, beta, gamma, replaceRegs (machine, regs))
      end
    | apply_user (Primop f, args, c, cs, machine) =
      f (args,
         fn v => apply_cont (c, v, machine),
         List.map (fn c => fn v => apply_cont (c, v, machine)) cs)

  and apply_cont (ContClos(Cont(l, x, pr), beta, gamma, tos), arg, machine) =
      let
          val contour = fresh_contour machine
          val hframe =
              case #lifetime (unUVar x)
               of H => [(#name (unUVar x), ref arg)]
                | _ => []
          val beta = (l, contour) :: beta
          val () = DynamicArray.update(#heap machine, contour, hframe)
          val sframe =
              case #lifetime (unUVar x)
               of S => [(#name (unUVar x), ref arg)]
                | _ => []
          val () = DynamicArray.update (#stack machine, tos, SOME sframe)
          val gamma = (l, tos) :: gamma
          val regs =
              case #lifetime (unUVar x)
               of R => [(#name (unUVar x), ref arg)]
                | _ => []
      in
          eval (pr, beta, gamma, replaceRegs (machine, regs))
      end
    | apply_cont (Halt, arg, machine) = Result arg

  val prelude =
      let
          fun arithOp f _ ([VInt i, VInt j], c, _) = c (VInt (f (i, j)))
            | arithOp _ f ([VFloat m, VFloat n], c, _) = c (VFloat (f (m, n)))
            | arithOp _ f ([VInt i, VFloat n], c, _) = c (VFloat (f (Real.fromInt i, n)))
            | arithOp _ f ([VFloat n, VInt i], c, _) = c (VFloat (f (n, Real.fromInt i)))
            | arithOp _ _ ([_, _], _, _) =
              raise (Eval "Wrong type, expected int * int")
            | arithOp _ _ _ = raise (Eval "Arity mismatch")

          fun divOp ([VInt i, VInt j], c, _) = c (VFloat (Real.fromInt i / Real.fromInt j))
            | divOp ([VFloat m, VFloat n], c, _) = c (VFloat (m / n))
            | divOp ([VInt i, VFloat n], c, _) = c (VFloat (Real.fromInt i / n))
            | divOp ([VFloat n, VInt i], c, _) = c (VFloat (n / Real.fromInt i))
            | divOp ([_, _], _, _) =
              raise (Eval "Wrong type, expected int * int")
            | divOp _ = raise (Eval "Arity mismatch")

          fun carOp ([VCons (x, _)], c, _) = c x
            | carOp ([_], _, _) = raise (Eval "Wrong type, expected cons")
            | carOp _ = raise (Eval "Arity mismatch")
          fun cdrOp ([VCons (_, xs)], c, _) = c xs
            | cdrOp ([_], _, _) = raise (Eval "Wrong type, expected cons")
            | cdrOp _ = raise (Eval "Arity mismatch")
          fun consOp ([x, xs], c, _) = c (VCons (x, xs))
            | consOp _ = raise (Eval "Arity mismatch")
          fun eqOp ([VInt i, VInt j], c, _) = c (VBool (i = j))
            | eqOp ([_, _], c, _) = c (VBool false)
            | eqOp _ = raise (Eval "Arity mismatch")
          fun nilPredOp ([VNil], c, _) = c (VBool true)
            | nilPredOp ([_], c, _) = c (VBool false)
            | nilPredOp _ = raise (Eval "Arity mismatch")

          fun ifOp ([VBool true], c, _) = c VNil
            | ifOp ([VBool false], _, [c]) = c VNil
            | ifOp _ = raise (Eval "Arity mismatch")
      in
          List.map (fn (name, f) => (name, ref (VClos (Primop f)))) [
            ("+", arithOp op+ op+),
            ("-", arithOp op- op-),
            ("*", arithOp op* op*),
            ("/", divOp),
            ("car", carOp),
            ("cdr", cdrOp),
            ("cons", consOp),
            ("=", eqOp),
            ("nil?", nilPredOp),
            ("if", ifOp)
          ]
      end

  fun evalPrelude prog =
      let
          val beta = [(~1, 0)]
          val gamma = []
          val machine =
              {
                gen_contour = ref 1,
                registers = [],
                stack = DynamicArray.fromList ([], NONE),
                heap = DynamicArray.fromList ([prelude], [])
              }
      in
          eval (prog, beta, gamma, machine)
      end
end
