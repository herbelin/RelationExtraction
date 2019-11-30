
let rec print_expr = function
  | Imp.VSucc e -> "VSucc (" ^ print_expr e ^ ")"
  | Imp.VZero -> "VZero"
  | Imp.VTrue -> "VTrue"
  | Imp.VFalse -> "VFalse"

let res =
  let test_func _ =
    (* Addition of natural numbers *)
    assert (Add.add12 (Add.Succ (Add.Succ Add.Zero)) (Add.Succ Add.Zero) = 
      (Add.Succ (Add.Succ (Add.Succ Add.Zero))));
    assert (Add.add12 Add.Zero Add.Zero = Add.Zero);
    assert (Add.add12 Add.Zero (Add.Succ Add.Zero) = (Add.Succ Add.Zero));
    assert (Add.add_full Add.Zero (Add.Succ Add.Zero) (Add.Succ Add.Zero) = true);
    assert (Add.add_full (Add.Succ Add.Zero) Add.Zero (Add.Succ Add.Zero) = true);
    assert (Add.add_full (Add.Succ Add.Zero) (Add.Succ Add.Zero) 
      (Add.Succ (Add.Succ Add.Zero)) = true);
    assert (Add.add_full (Add.Succ Add.Zero) Add.Zero Add.Zero = false);
    assert (Add.add_full Add.Zero Add.Zero (Add.Succ Add.Zero) = false);

    (* Simple imperative language *)
    let prog = Imp.Sequ (Imp.Affect (Imp.A, Imp.ESucc Imp.EZero),
               Imp.Sequ (Imp.Affect (Imp.B, Imp.ETrue),
               Imp.Boucle ((Imp.EVar Imp.B), Imp.Sequ (Imp.Affect (Imp.A, 
                 Imp.ESucc ( Imp.EVar Imp.A)), Imp.Affect (Imp.B, Imp.EFalse)))
    )) in
    let res = Imp.exec12 prog Imp.empty_env in
    assert (Imp.get_var Imp.A res = Imp.Some (Imp.VSucc (Imp.VSucc Imp.VZero)));
    assert (Imp.typecheck12 Imp.EnvtEmpty (Imp.ESucc Imp.EZero) = Imp.TInt);
    assert (Imp.typecheck12 Imp.EnvtEmpty Imp.EFalse = Imp.TBool); 

    (* Fibonacci *)
    assert (Fibo.fibo1 (Fibo.S (Fibo.S (Fibo.S (Fibo.S Fibo.O)))) = 
      Fibo.S (Fibo.S (Fibo.S (Fibo.S (Fibo.S Fibo.O)))));
    assert (Fibo.fibo1 Fibo.O = Fibo.S Fibo.O);

    (* Simple ordering *)
    assert (So.test12 So.A So.B = So.C);
    assert (So.test12 So.A So.C = So.B);
    assert (So.test12 So.B So.C = So.A);
    assert (So.test12 So.B So.A = So.D);

    (* Mutual induction *)
    assert (Odd.even_full (Odd.S (Odd.S Odd.O)) = true);
    assert (Odd.even_full (Odd.S Odd.O) = false);
    assert (Odd.odd_full (Odd.S Odd.O) = true);
    assert (Odd.odd_full (Odd.S (Odd.S Odd.O)) = false);

    (* Names in extraction commands *)
    assert (Extrcommand.ev (Extrcommand.S (Extrcommand.S Extrcommand.O)) = true);
    assert (Extrcommand.ev (Extrcommand.S Extrcommand.O) = false);
    assert (Extrcommand.od (Extrcommand.S Extrcommand.O) = true);
    assert (Extrcommand.od (Extrcommand.S (Extrcommand.S Extrcommand.O)) = false);

    (* Output tuples *)
    assert (Tuples.eval12 (Tuples.EInc Tuples.A) 
      (Tuples.Env (Tuples.A, Tuples.VZero, Tuples.EnvEmpty)) = 
      (Tuples.VZero, Tuples.Env 
        (Tuples.A, (Tuples.VSucc Tuples.VZero), Tuples.EnvEmpty))); 

    Printf.printf "test OK!\n"
in test_func ()
