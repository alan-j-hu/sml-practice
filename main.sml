structure Main =
  struct
    structure Di = Direct
    structure Cps = ThreeCPS
    fun main (_, _) =
        let
            val res =
                Di.evalPrelude (
                    Di.Letrec(
                        [("fac",
                          Di.Fun(
                              ["n"],
                              Di.If(
                                  Di.Apply(Di.Var "=", [Di.Var "n", Di.Int 0]),
                                  Di.Int 1,
                                  Di.Apply(
                                      Di.Var "*",
                                      [Di.Var "n",
                                       Di.Apply(
                                           Di.Var "fac",
                                           [Di.Apply(
                                                 Di.Var "-",
                                                 [Di.Var "n",
                                                  Di.Int 1])])])
                        )))],
                        Di.Apply(Di.Var "fac", [Di.Int 5]))
                )
        in
            case res
             of Di.VInt 120 => (print "Ok"; OS.Process.success)
              | _ => (print "Bad"; OS.Process.failure)
        end
        handle Di.Eval msg =>
               (print msg;
                OS.Process.failure)

      fun main2 (_, _) =
        let
            val sub = Cps.UVar {name = "-", lifetime = Cps.H, binder = ~1}
            val mul = Cps.UVar {name = "*", lifetime = Cps.H, binder = ~1}
            val n = Cps.UVar {name = "n", lifetime = Cps.H, binder = 1}
            val k = Cps.CVar {name = "k", lifetime = Cps.H, binder = 1}
            val b = Cps.UVar {name = "b", lifetime = Cps.H, binder = 2}
            val n' = Cps.UVar {name = "n'", lifetime = Cps.H, binder = 5}
            val facn' = Cps.UVar {name = "facn'", lifetime = Cps.H, binder = 6}
            val fac = Cps.UVar {name = "fac", lifetime = Cps.H, binder = 0}
            val res =
                Cps.evalPrelude (
                    Cps.Letrec(
                        0,
                        [(fac,
                          Cps.Lambda(
                              1,
                              [n],
                              k,
                              [],
                              Cps.UApp(
                                  Cps.ArgVar (Cps.UVar {name = "=", lifetime = Cps.H, binder = ~1}),
                                  [Cps.ArgVar n,
                                   Cps.ArgInt 0],
                                  Cps.ContLam(
                                      Cps.Cont(
                                          2,
                                          b,
                                          Cps.UApp(
                                              Cps.ArgVar (Cps.UVar {name = "if", lifetime = Cps.H, binder = ~1}),
                                              [Cps.ArgVar b],
                                              Cps.ContLam(
                                                  Cps.Cont(
                                                      3,
                                                      Cps.UVar {name = "_", lifetime = Cps.S, binder = 3},
                                                      Cps.CApp(
                                                          Cps.ContVar (
                                                              Cps.CVar {name = "k", lifetime = Cps.H, binder = 1}
                                                          ),
                                                          Cps.ArgInt 1
                                                      )
                                                  )
                                              ),
                                              [Cps.ContLam(
                                                  Cps.Cont(
                                                      4,
                                                      Cps.UVar {name = "_", lifetime = Cps.S, binder = 4},
                                                      Cps.UApp(
                                                          Cps.ArgVar sub,
                                                          [Cps.ArgVar n,
                                                           Cps.ArgInt 1],
                                                          Cps.ContLam(
                                                              Cps.Cont(
                                                                  5,
                                                                  n',
                                                                  Cps.UApp(
                                                                      Cps.ArgVar fac,
                                                                      [Cps.ArgVar n'],
                                                                      Cps.ContLam(
                                                                          Cps.Cont(
                                                                              6,
                                                                              facn',
                                                                              Cps.UApp(
                                                                                  Cps.ArgVar mul,
                                                                                  [Cps.ArgVar n,
                                                                                   Cps.ArgVar facn'],
                                                                                  Cps.ContVar k,
                                                                                  []
                                                                              )
                                                                          )
                                                                      ),
                                                                      []
                                                                  )
                                                              )
                                                          ),
                                                          []
                                                      )
                                                  )
                                              )]
                                          )
                                      )
                                  ),
                                  []
                              )
                        ))],
                        Cps.UApp(Cps.ArgVar fac, [Cps.ArgInt 5], Cps.ContHalt, []))
                )
        in
            case res
             of Cps.Result (Cps.VInt 120) => (print "Ok2"; OS.Process.success)
              | _ => (print "Bad2"; OS.Process.failure)
        end
        handle Cps.Eval msg =>
               (print msg;
                OS.Process.failure)
             | Subscript =>
               (print "Sub";
                OS.Process.failure)
             | Size =>
               (print "Size";
                OS.Process.failure)
             | ex =>
               (print (exnName ex);
                OS.Process.failure)
  end
