structure Direct = struct
  datatype hexp
    = Int of int
    | Float of real
    | Bool of bool
    | Cons of hexp * hexp
    | Nil
    | Var of string
    | Fun of string list * hexp
    | If of hexp * hexp * hexp
    | Apply of hexp * hexp list
    | Letrec of (string * hexp) list * hexp

  datatype value
    = VInt of int
    | VFloat of real
    | VBool of bool
    | VCons of value * value
    | VNil
    | VBox of value ref
    | Procedure of procedure

  and procedure
    = Closure of string list * hexp * (string * value ref) list
    | Primop of (value list -> value)

  exception Eval of string

  fun zip ([], []) = []
    | zip (x :: xs, y :: ys) = (x, y) :: zip (xs, ys)
    | zip _ = raise (Eval "Uneven lists")

  fun lookup ([], var) = raise (Eval "Variable is not found")
    | lookup ((k, v) :: xs, var) =
      if k = var then
          !v
      else
          lookup (xs, var)

  fun eval (Int n, _) = VInt n
    | eval (Float n, _) = VFloat n
    | eval (Bool b, _) = VBool b
    | eval (Cons (x, xs), env) =
      let
          val x = eval (x, env)
          val xs = eval (xs, env)
      in
          VCons (x, xs)
      end
    | eval (Nil, _) = VNil
    | eval (Var name, env) = lookup (env, name)
    | eval (Fun (params, exp), env) = Procedure (Closure (params, exp, env))
    | eval (If (p, t, e), env) =
      let
          val b = eval (p, env)
      in
          case b
           of VBool true => eval (t, env)
            | _ => eval (e, env)
      end
    | eval (Apply (f, args), env) =
      let
          val f = eval (f, env)
          val args =  List.map (fn arg => eval (arg, env)) args
      in
          case f
           of Procedure procedure => apply (procedure, args)
            | _ => raise (Eval "Not a procedure")
      end
    | eval (Letrec (bindings, hexp), env) =
      let
          val toUpdate =
              List.map (fn (var, exp) => (var, ref VNil, exp)) bindings
          val appendEnv = List.map (fn (var, r, _) => (var, r)) toUpdate
          val env = List.revAppend (appendEnv, env)
          fun updateAll [] = ()
            | updateAll ((var, r, exp) :: xs) =
              let
                  val () = (r := eval (exp, env))
              in
                  updateAll xs
              end
          val () = updateAll toUpdate
      in
          eval (hexp, env)
      end

  and apply (Closure (params, body, env), args) =
      eval (body, zip (params, List.map ref args) @ env)
    | apply (Primop f, args) = f args

  val prelude =
      let
          fun arithOp f _ [VInt i, VInt j] = VInt (f (i, j))
            | arithOp _ f [VFloat m, VFloat n] = VFloat (f (m, n))
            | arithOp _ f [VInt i, VFloat n] = VFloat (f (Real.fromInt i, n))
            | arithOp _ f [VFloat n, VInt i] = VFloat (f (n, Real.fromInt i))
            | arithOp _ _ [_, _] =
              raise (Eval "Wrong type, expected int * int")
            | arithOp _ _ _ = raise (Eval "Arity mismatch")

          fun divOp [VInt i, VInt j] = VFloat (Real.fromInt i / Real.fromInt j)
            | divOp [VFloat m, VFloat n] = VFloat (m / n)
            | divOp [VInt i, VFloat n] = VFloat (Real.fromInt i / n)
            | divOp [VFloat n, VInt i] = VFloat (n / Real.fromInt i)
            | divOp [_, _] =
              raise (Eval "Wrong type, expected int * int")
            | divOp _ = raise (Eval "Arity mismatch")

          fun carOp [VCons (x, _)] = x
            | carOp [_] = raise (Eval "Wrong type, expected cons")
            | carOp _ = raise (Eval "Arity mismatch")
          fun cdrOp [VCons (_, xs)] = xs
            | cdrOp [_] = raise (Eval "Wrong type, expected cons")
            | cdrOp _ = raise (Eval "Arity mismatch")
          fun consOp [x, xs] = VCons (x, xs)
            | consOp _ = raise (Eval "Arity mismatch")
          fun eqOp [VInt i, VInt j] = VBool (i = j)
            | eqOp [_, _] = VBool false
            | eqOp _ = raise (Eval "Arity mismatch")
          fun nilPredOp [VNil] = VBool true
            | nilPredOp [_] = VBool false
            | nilPredOp _ = raise (Eval "Arity mismatch")
      in
          List.map (fn (name, f) => (name, ref (Procedure (Primop f)))) [
            ("+", arithOp op+ op+),
            ("-", arithOp op- op-),
            ("*", arithOp op* op*),
            ("/", divOp),
            ("car", carOp),
            ("cdr", cdrOp),
            ("cons", consOp),
            ("=", eqOp),
            ("nil?", nilPredOp)
          ]
      end

  fun evalPrelude exp = eval (exp, prelude)
end
