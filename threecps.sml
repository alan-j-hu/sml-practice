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

  datatype ('lam, 'var) exp = Lam of 'lam | Var of 'var

  datatype ulam = Lambda of label * uvar * cvar * cvar list * prog
  and clam = Cont of label * uvar * prog

  and prog
    = UApp of (ulam, uvar) exp * (ulam, uvar) exp * (clam, cvar) exp * (clam, cvar) exp list
    | CApp of (clam, cvar) exp * (ulam, uvar) exp
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
    | VClos of ulam * hcenv * scenv
    | VCont of clam * hcenv * scenv * int

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

  fun a_u (Lam(ulam), beta, gamma, machine : machine) =
      VClos (ulam, beta, gamma)
    | a_u (Var(UVar v), beta, gamma, machine) =
      case #lifetime v
       of H =>
          !(lookup (DynamicArray.sub (#heap machine, lookup (beta, #binder v)), #name v))
        | S =>
          !(lookup (Option.valOf (DynamicArray.sub (#stack machine, lookup (gamma, #binder v))), #name v))
        | R =>
          !(lookup (#registers machine, #name v))

  fun a_c (Lam(clam), beta, gamma, machine : machine) =
      VCont (clam, beta, gamma, DynamicArray.bound (#stack machine) + 1)
    | a_c (Var(CVar v), beta, gamma, machine) =
      case #lifetime v
       of H =>
          !(lookup (DynamicArray.sub (#heap machine, lookup (beta, #binder v)), #name v))
        | S =>
          !(lookup (Option.valOf (DynamicArray.sub (#stack machine, lookup (gamma, #binder v))), #name v))
        | R =>
          !(lookup (#registers machine, #name v))

  fun stackIdx (_, _, _, idx) = idx

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

  fun makeUFrame pred (x, arg, k, ks, c, cs) =
      let
          val ks = k :: ks
          val cs = c :: cs
          val pairs = zip (ks, cs)
          val pairs = List.filter (fn (k, _) => pred (#lifetime (unCVar k))) pairs
          val pairs = List.map (fn (k, c) => (#name (unCVar k), ref (VCont c))) pairs
      in
          if pred (#lifetime (unUVar x)) then
              (#name (unUVar x), ref arg) :: pairs
          else
              pairs
      end

  fun overwriteFrame ([], new) = new
    | overwriteFrame ((var, value) :: xs, new) =
      case lookupOpt (new, var)
       of NONE => (var, value) :: overwriteFrame (xs, new)
        | SOME (value', new) => (var, value') :: overwriteFrame (xs, new)

  fun eval (UApp(f, x, q1, qs), beta, gamma, machine) =
    let
        val proc = assert_clos (a_u (f, beta, gamma, machine))
        val arg = a_u (x, beta, gamma, machine)
        val c = assert_cont (a_c (q1, beta, gamma, machine))
        val cs = List.map (fn c => assert_cont (a_c (c, beta, gamma, machine))) qs
        val () = stackTrim (#stack machine, c, cs)
    in
      apply_user (proc, arg, c, cs, machine)
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
                  val () = (r := VClos (ulam, beta, gamma))
              in
                  update xs
              end
          val () = update toUpdate
      in
          eval (tail, beta, gamma, replaceRegs(machine, regs))
      end

  and apply_user ((Lambda(l, x, k, ks, pr), beta, gamma), arg, c, cs, machine) =
      let
          val contour = fresh_contour machine
          val hframe = makeUFrame (fn H => true | _ => false) (x, arg, k, ks, c, cs)
          val beta = (l, contour) :: beta
          val () = DynamicArray.update(#heap machine, contour, hframe)
          val sframe = makeUFrame (fn S => true | _ => false) (x, arg, k, ks, c, cs)
          val sz = DynamicArray.bound (#stack machine) + 1
          val () = DynamicArray.update (#stack machine, sz, SOME sframe)
          val gamma = (l, sz) :: gamma
          val regs =
              overwriteFrame
                  (#registers machine,
                   makeUFrame (fn R => true | _ => false) (x, arg, k, ks, c, cs))
      in
          eval (pr, beta, gamma, replaceRegs (machine, regs))
      end

  and apply_cont ((Cont(l, x, pr), beta, gamma, tos), arg, machine) =
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
end
