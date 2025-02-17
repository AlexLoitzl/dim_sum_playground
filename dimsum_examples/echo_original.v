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

  Definition combined_spec_body : spec rec_event Z unit :=
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h').

  Definition combined_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    Spec.forever combined_spec_body.

End echo.

Section link.

  Lemma echo_getc_sim v:
    trefines (rec_link {["echo"]} {["getc"]}
                (rec_mod echo_prog) (spec_mod getc_spec v))
            (spec_mod combined_spec v).
  Proof.
    apply: tsim_implies_trefines => n0 /=.
    (* apply tsim_remember_all. *)
    (* intros ?? IH ? => /=. simpl. *)
    tstep_i => *. case_match; destruct!/=.
    go_s. eexists (_, _, _). go.
    go_s. split!. go.
    go_s => ?. go. go_s => ?. intros ?->. simplify_eq. rewrite bool_decide_true; [|done].
    tstep_i. split! => ???? Hf ?. unfold echo_prog in Hf. simplify_map_eq.

    unshelve eapply tsim_remember. { simpl. exact (λ _ '(_, _, (Rec e _ f), (t1, v1)) '(t2, v2),
      (* TODO: How does Michael think about this, I guess typically I would phrase an induction hypothesis *)
    (*     using an arbitrary kontext here *)
      exists K v,
      t1 ≡ getc_spec ∧
      e = expr_fill K ((Call (Val (ValFn "echo"))) (Val <$> [])) ∧
      f = echo_prog ∧
      t2 ≡ Spec.forever combined_spec_body ∧
      v1 ≡ v ∧
      v2 ≡ v). }
    { eexists [ReturnExtCtx false]. split!. } { done. }
    move => n _ Hloop a b c.
    destruct a as [[[aa ab] [ac ac2]] a2].
    destruct b as [? ?].
    destruct!/=.

    Compute m_state (rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z)).
    move => n _ Hloop [????]. destruct!/=.

    intros ?? IH ??? => /=.
    revert v.
    apply tsim_remember_all.
    intros ?? IH ? => /=.

    tstep_i. split! => ? Hf. unfold echo_prog in Hf. simplify_map_eq.
    split!. tstep_i => *. destruct!/=. split!.
    tstep_i. rewrite {1}/echo_prog. split!=> *. case_match; destruct!/=.
    rewrite bool_decide_true; [|done].
    go_i. go_i. intros [[? ?] ?]. go.
    go_i => ?. destruct!/=. go.
    tstep_i. split!. go.
    tstep_i. split!. go.
    go_i. go_i. go_i => *. intros ? Hs.  destruct!/=.
    go_i. split! => *. destruct!/=.
    go_i. go_i. split! => *. destruct!/=. rewrite bool_decide_false; [|done].
    go_s. go_s. go_s. go_s. eexists. go. go_s. split!. go.
    go_i => e *. destruct!/=. destruct e; destruct!/=.
    { go_s. split!. go. go_s. split!. go. go_s. exact I. }
    go_s. split!. go. go_s. split!. go. go_s => ?. go.
    tstep_s. intros ?->  => /=.
    tstep_i. split!. intros. tstep_i. simplify_eq.
    rewrite -unfold_forever => /=. rewrite -/getc_spec in Hs.

    eapply IH.
    set HIDE := (X in FreeA _ X).
    eapply tstep_i_generic.
    apply IH.


    go_s. simplify_eq.
    go_i. split!. intros. go_i. simplify_eq.

    apply IH.
    done.
    tstep
  Qed.

End link.
