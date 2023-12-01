structure Main =
  struct
    structure Di = Direct
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
  end
