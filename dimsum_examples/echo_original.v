From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import rec asm rec_to_asm print.
From dimsum.examples.compiler Require Import compiler.

Local Open Scope Z_scope.

Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Section getc.

  Definition getc_spec : spec rec_event Z void :=
    Spec.forever(
    (* Incoming call of getc *)
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    (* There is a current position of the buffer *)
    v ← TGet;
    TPut (v + 1);;
    (* Return old position *)
    TVis (Outgoing, ERReturn (ValNum v) h)).

End getc.

Section echo.

  Definition echo_rec : fndef := {|
    fd_args := [];
    fd_static_vars := [];
    fd_vars := [];
    fd_body := LetE "c" (rec.Call (Val (ValFn "getc")) []) $
              LetE "_" (rec.Call (Val (ValFn "putc")) [Var "c"]) $
              rec.Call (Val (ValFn "echo")) [];
    fd_static := I
  |}.

  Definition echo_prog : gmap string fndef :=
    <["echo" := echo_rec]> $ ∅.

  (* Call with direct return *)
  Definition TCallRet {S} (f : string) (vs : list val) (h : heap_state) :
    spec rec_event S (val * heap_state) :=
    TVis (Outgoing, ERCall f vs h);;
    e ← TExist _;
    TVis (Incoming, e);;
    if e is ERReturn v h' then
      TRet (v, h')
    else
      TUb.

  Definition combined_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h');;
    TUb.

End echo.

Section link.

  Lemma echo_getc_sim :
    trefines (rec_link {["echo"]} {["getc"]}
                (rec_mod echo_prog) (spec_mod getc_spec 0))
            (spec_mod combined_spec 0).
  Proof.
    apply: tsim_implies_trefines => n0 /=.
    tstep_i => *. case_match; destruct!/=.
    go_s. eexists (_, _, _). go.
    go_s. split!. go.
    go_s => ?. go. go_s => ?. go. simplify_eq. rewrite bool_decide_true; [|done].
    tstep_i. split! => ???? Hf ?. unfold echo_prog in Hf. simplify_map_eq.
    tstep_i. split! => ? Hf. unfold echo_prog in Hf. simplify_map_eq. split!.
    tstep_i => *. destruct!/=. split; [by repeat econs|].
    tstep_i. rewrite {1}/echo_prog. split!=> *. case_match; destruct!/=.
    rewrite bool_decide_true; [|done].
    go_i. go_i. intros [[? ?] ?]. go.
    go_i => ?. destruct!/=. go.
    tstep_i. split!. go.
    tstep_i. split!. go.
    go_i. go_i. go_i => *. go. destruct!/=.
    go_i. split! => *. destruct!/=.
    go_i. go_i. split! => *. destruct!/=. rewrite bool_decide_false; [|done].
    go_s. go_s. go_s. eexists. go. go_s. split!. go.
    go_i => e *. destruct!/=. destruct e; destruct!/=.
    { go_s. split!. go. go_s. split!. go. go_s. exact I. }
    go_s. split!. go. go_s. split!. go. go_s => ?. go.
    by go_s.
Qed.

End link.
