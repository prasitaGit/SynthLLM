Require VC.Preface.  (* Check for the right version of VST *)

Require Import VST.floyd.proofauto.
Require Import VC.swap.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)

(*frame*)
Lemma prove_frame: forall P Q R,
  Q |-- R ->
  P * Q |-- P * R.
Proof.
  intros. apply sepcon_derives. auto. assumption.
Qed.

(*emp*)
Lemma prove_emp: emp |-- emp.
Proof. auto. Qed. 

(*swap specification*)
Definition swap_spec : ident * funspec :=
  DECLARE _swap
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr a)) y).

(*swap-skip specification - point to the same variable*)
Definition swapskip_spec : ident * funspec :=
  DECLARE _swapskip
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y).

(*varspec: global variables
  funspec: set of functions (Gprog)
  function: function should be a member of funspec
  ident * funspec: specification
*)

(*Read: introduce a new temp. variable; 
 semax Delta P c Q -> semax Delta P' c Q.
 P and Q: PROP, LOCAL and SEP; 
 Read: Add stuff to LOCAL*)

Definition Gprog := [swapskip_spec; swap_spec].

 (*no ltacs used*)
Lemma body_swapskip: semax_body Vprog Gprog f_swapskip swapskip_spec.
Proof.
  start_function. unfold POSTCONDITION. unfold abbreviate.
  unfold stackframe_of. simpl map. rewrite fold_right_nil.
  rewrite sepcon_emp.
  eapply semax_post. 5:{ eapply semax_skip. }
  apply derives_ENTAIL. eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). simpl. 
  intros. entailer!.
  apply derives_ENTAIL.
  simpl. intros. entailer!.
  simpl. intros. entailer!. simpl. intros. entailer!.
  Qed.


  (*very limited ltacs*)
Lemma body_swaplimltac: semax_body Vprog Gprog f_swap swap_spec.
  Proof.
    start_function. unfold POSTCONDITION. unfold abbreviate.
    eapply semax_seq'.
    (*first read*)
    apply semax_later_trivial. 
    match goal with
    | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
     let T1 := fresh "T1" in evar (T1: PTree.t val);
     let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
     let G := fresh "GV" in evar (G: option globals);
     let LOCAL2PTREE := fresh "LOCAL2PTREE" in
     assert (local2ptree Q = (T1, T2, nil, G)) as LOCAL2PTREE;
     [subst T1 T2 G; prove_local2ptree |];
     first [ load_tac_with_hint LOCAL2PTREE | load_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e R | hint_msg LOCAL2PTREE Delta e];
     clear T1 T2 G LOCAL2PTREE
    end.
    unfold MORE_COMMANDS. unfold abbreviate. 
    (*semax_seq -> read again*)
    eapply semax_seq'. simpl. apply semax_later_trivial. 
    match goal with
    | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
     let T1 := fresh "T1" in evar (T1: PTree.t val);
     let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
     let G := fresh "GV" in evar (G: option globals);
     let LOCAL2PTREE := fresh "LOCAL2PTREE" in
     assert (local2ptree Q = (T1, T2, nil, G)) as LOCAL2PTREE;
     [subst T1 T2 G; prove_local2ptree |];
     first [ load_tac_with_hint LOCAL2PTREE | load_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e R | hint_msg LOCAL2PTREE Delta e];
     clear T1 T2 G LOCAL2PTREE
    end.
    (*semax seq -> write*)
    eapply semax_seq'. simpl. apply semax_later_trivial.
    (*store tac*) 
    match goal with
    | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e1 ?e2) _ =>
     check_expression_by_value e1;
     let T1 := fresh "T1" in evar (T1: PTree.t val);
     let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
     let G := fresh "GV" in evar (G: option globals);
     let LOCAL2PTREE := fresh "LOCAL2PTREE" in
     assert (local2ptree Q = (T1, T2, nil, G)) as LOCAL2PTREE;
     [subst T1 T2 G; prove_local2ptree |];
     first [ store_tac_with_hint LOCAL2PTREE | store_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e1 R | hint_msg LOCAL2PTREE Delta e1];
     clear T1 T2 LOCAL2PTREE
    end.
    (*skip and sequence and write*)
    apply semax_seq_skip.  eapply semax_seq'. simpl.
    apply semax_later_trivial; 
    (*store tac*)
    match goal with
    | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e1 ?e2) _ =>
     check_expression_by_value e1;
     let T1 := fresh "T1" in evar (T1: PTree.t val);
     let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
     let G := fresh "GV" in evar (G: option globals);
     let LOCAL2PTREE := fresh "LOCAL2PTREE" in
     assert (local2ptree Q = (T1, T2, nil, G)) as LOCAL2PTREE;
     [subst T1 T2 G; prove_local2ptree |];
     first [ store_tac_with_hint LOCAL2PTREE | store_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e1 R | hint_msg LOCAL2PTREE Delta e1];
     clear T1 T2 LOCAL2PTREE
    end.
    (*skip part*)
    unfold stackframe_of. simpl map. rewrite fold_right_nil.
    rewrite sepcon_emp. simpl.
    eapply semax_post. 5:{ eapply semax_skip. }
    apply derives_ENTAIL. eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O).
    eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). simpl. 
    intros. entailer!.
    apply derives_ENTAIL.
    simpl. intros. entailer!.
    simpl. intros. entailer!. simpl. intros. entailer!.
  Qed.

  (*limited ltacs*)
Lemma body_swapnoltac: semax_body Vprog Gprog f_swap swap_spec.
   Proof.
    start_function.
    unfold abbreviate in POSTCONDITION.
    unfold POSTCONDITION. unfold abbreviate.
    eapply semax_seq'.
     (*first read*)
    apply semax_later_trivial. load_tac.
    unfold MORE_COMMANDS. unfold abbreviate. 
    (*semax_seq -> read again*)
    eapply semax_seq'. simpl. apply semax_later_trivial; load_tac.
    (*semax seq -> write*)
    eapply semax_seq'. simpl. apply semax_later_trivial; store_tac.
    (*read again*)
    apply semax_seq_skip.  eapply semax_seq'. simpl.
    apply semax_later_trivial; store_tac. 
    (*skip part*)
    unfold stackframe_of. simpl map. rewrite fold_right_nil.
    rewrite sepcon_emp. simpl.
    eapply semax_post. 5:{ eapply semax_skip. }
    apply derives_ENTAIL. eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O).
    eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). simpl. 
    intros. entailer!.
    apply derives_ENTAIL.
    simpl. intros. entailer!.
    simpl. intros. entailer!. simpl. intros. entailer!.
   Qed.
 
(*explicit - forward.*)
Lemma body_swapexplicit: semax_body Vprog Gprog f_swap swap_spec.
Proof.
  start_function.
  assert (
  forall s,
    (semax Delta 
    (
      PROP ( )
      LOCAL (temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    s
    POSTCONDITION) -> 
    (semax Delta 
    (
      PROP ( )
      LOCAL (temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    (
      Ssequence (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)) s
    )
    POSTCONDITION)
  ). { intros. forward. assumption. }
  forward.
  (*second read*)
  assert (
    forall s,
      (semax Delta 
      (
        PROP ( )
        LOCAL (temp _b2 (Vint (Int.repr b));
        temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
        SEP (data_at sh1 tint (Vint (Int.repr a)) x;
        data_at sh2 tint (Vint (Int.repr b)) y)
      )
      s
      POSTCONDITION) -> 
      (semax Delta 
      (
        PROP ( )
        LOCAL (temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
        SEP (data_at sh1 tint (Vint (Int.repr a)) x;
        data_at sh2 tint (Vint (Int.repr b)) y)
      )
      ( (*(Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))*)
        Ssequence (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint)) s
      )
      POSTCONDITION)
  ). { intros. forward. assumption. }
  forward.
  (*write y: *)
  assert (
    forall s,
      (semax Delta 
      (
        PROP ( )
        LOCAL (temp _b2 (Vint (Int.repr b));
        temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
        SEP (data_at sh1 tint (Vint (Int.repr a)) x;
        data_at sh2 tint (Vint (Int.repr a)) y)
      )
      s
      POSTCONDITION) -> 
      (semax Delta 
      (
        PROP ( )
        LOCAL (temp _b2 (Vint (Int.repr b));
          temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
        SEP (data_at sh1 tint (Vint (Int.repr a)) x;
        data_at sh2 tint (Vint (Int.repr b)) y)
      )
      ( (*(Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))*)
        Ssequence (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint)) s
      )
      POSTCONDITION)
  ). { intros. forward. assumption. }
  forward.
  (*write x*)
  assert (
    forall s,
      (semax Delta 
      (
        PROP ( )
        LOCAL (temp _b2 (Vint (Int.repr b));
        temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
        SEP (data_at sh1 tint (Vint (Int.repr b)) x;
        data_at sh2 tint (Vint (Int.repr a)) y)
      )
      s
      POSTCONDITION) -> 
      (semax Delta 
      (
        PROP ( )
        LOCAL (temp _b2 (Vint (Int.repr b));
          temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
        SEP (data_at sh1 tint (Vint (Int.repr a)) x;
        data_at sh2 tint (Vint (Int.repr a)) y)
      )
      ( (*(Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))*)
        Ssequence (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)) s
      )
      POSTCONDITION)
  ). { intros. forward. assumption. }
  unfold abbreviate in POSTCONDITION.
  forward. entailer!.
Qed.


Definition f_swap (s : statement) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
  fn_body :=
          s
|}.
      
(*constructing program on the fly*)
Fixpoint constructstatement (l : list statement) : statement :=
  match l with
  | nil => Sskip
  | h :: nil => h 
  | h :: t => (Ssequence h (constructstatement t))
  end.


(*kinda synthesis*)
Lemma body_swapsynthesis: semax_body Vprog Gprog (f_swap Sskip)  swap_spec.
  Proof.
    start_function.
    unfold abbreviate in POSTCONDITION.

    (*go through series of semax Delta P statement P'; till semax Delta P' Sskip POSTC can be proved*)
    (*whole proof: synthesize + lemma with typeconext*)
    assert (exists s, semax Delta 
    (
      PROP ( )
      LOCAL (temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    s 
    POSTCONDITION). {
      eexists. 
      (*read*)
      eapply semax_seq' with (c1 := (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))). 
      apply semax_later_trivial. load_tac. simpl.
      (*second read*)
      eapply semax_seq' with (c1 := (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))).
      apply semax_later_trivial. load_tac. simpl.
      (*first write*)
      eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))).
      apply semax_later_trivial. store_tac. simpl.
      (*second write*)
      eapply semax_seq' with (c1 := (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)))(c2 := Sskip).
      apply semax_later_trivial. store_tac. simpl.
      (*Skip*)
      unfold POSTCONDITION. unfold abbreviate.
      unfold stackframe_of. simpl map. rewrite fold_right_nil.
      rewrite sepcon_emp. simpl.
      eapply semax_post. 5:{ eapply semax_skip. }
      apply derives_ENTAIL. eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O).
      eapply drop_LOCAL'' with (n := O). eapply drop_LOCAL'' with (n := O). simpl. 
      intros. entailer!.
      apply derives_ENTAIL.
      simpl. intros. entailer!.
      simpl. intros. entailer!. simpl. intros. entailer!. 
    }
  Admitted.

