Require VC.Preface.  (* Check for the right version of VST *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.floyd.SeparationLogicAsLogic.
Require Import VC.swap.
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.


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

Check f_swap.

Compute (check_norm_stmt (fn_body f_swapskip)).
Compute (fn_body f_swapskip).
Compute (fn_callconv f_swapskip).
Locate fn_body.
Print fn_body.
Check f_swapskip.
Print fn_body.
Check check_norm_stmt.

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

  Require Import VST.floyd.local2ptree_denote.
  Require Import VST.floyd.local2ptree_eval.
  Import compcert.lib.Maps.
  (*very limited ltacs*)
  Lemma body_swaplimltac: semax_body Vprog Gprog f_swap swap_spec.
  Proof.
    start_function. unfold POSTCONDITION. unfold abbreviate.
    eapply semax_seq'.
    (*first read*)
   apply semax_later_trivial. 
   Print Ltac load_tac. Locate load_tac.
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
    Locate start_function.
     start_function. unfold POSTCONDITION. unfold abbreviate.
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
  Check temp. Check data_at.
  start_function.
  Check [temp _a2 (Vint (Int.repr a));temp _x x; temp _y y].
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

(*read x - these shouldn't be required*)
Definition swap_readspecx : ident * funspec :=
  DECLARE _swap
    WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z, a2: reptype tint
    PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    PARAMS (x; y)
    SEP (data_at sh1 tint a2 x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ] 
    PROP () RETURN ()
    SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint a2 y).

(*writex - these shouldn't be required*)
Definition swap_writespecx : ident * funspec :=
  DECLARE _swap
    WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
    PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    PARAMS (x; y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
    POST [ tvoid ]
    PROP () RETURN ()
      SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr b)) y).


      Definition f_swap (s : statement) := {|
        fn_return := tvoid;
        fn_callconv := cc_default;
        fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
        fn_vars := nil;
        fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
        fn_body :=
          s
      |}.
      
      Definition s := (Ssequence
      (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))
      (Ssequence
        (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))
        (Ssequence
          (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))
          (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint))))).

  
      (*with the exact sequence*)
  Lemma body_swapsynth: exists s, semax_body Vprog Gprog (f_swap s)  swap_spec.
  Proof.
    eexists. 
    (*partial start function - eliminating fswaps*)
    leaf_function.
    lazymatch goal with |- @semax_body ?V ?G ?cs ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_funspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_funspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ _ _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (@semax_body V G cs F s); subst s;
   unfold NDmk_funspec'
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec; 
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>

   split3; [check_parameter_types' | check_return_type | ];
    match Pre with
   | (fun _ => convertPre _ _ (fun i => _)) =>  intros Espec DependedTypeList i
   | (fun _ x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun _ i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 try match goal with |- semax _ (fun rho => ?A rho * ?B rho) _ _ =>
     change (fun rho => ?A rho * ?B rho) with (A * B)
  end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 rewrite_old_main_pre;
 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
             destruct p as [a b]
 | |- semax _ (close_precondition _
                                                (fun ae => !! (Datatypes.length (snd ae) = ?A) && ?B
                                                      (make_args ?C (snd ae) (mkEnviron (fst ae) _ _))) * _) _ _ =>
          match B with match ?p with (a,b) => _ end => destruct p as [a b] end
       end;
(* this speeds things up, but only in the very rare case where it applies,
   so maybe not worth it ...
  repeat match goal with H: reptype _ |- _ => progress hnf in H; simpl in H; idtac "reduced a reptype" end;
*)
 try start_func_convert_precondition.
 Check compute_close_precondition_eq.
 Check close_precondition_main.
(*start_function2 does not do anything*)
 first [ try erewrite compute_close_precondition_eq; [ | reflexivity | reflexivity]
        | try rewrite close_precondition_main ].
 (*start function 3.*)
 simpl app.
 simplify_func_tycontext.
 Check mk_funspec.
Admitted.

Definition lstatement := [Sskip].
Check lstatement.
Definition ls2 := lstatement ++ [Sskip].
Check ls2.
Print ls2.


Definition ssynth := Ssequence
  (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))
  (Ssequence
    (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))
    (Ssequence
      (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))
      (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)))).

Definition lsequence := [(Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)); (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint));
(Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint)); (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint))].
Check lsequence.

Fixpoint constructstatement (l : list statement) : statement :=
  match l with
  | nil => Sskip
  | h :: nil => h 
  | h :: t => (Ssequence h (constructstatement t))
  end.

Definition stmt := (constructstatement lsequence).


(*kinda synthesis*)
Lemma body_swapsynthesis: semax_body Vprog Gprog (f_swap Sskip)  swap_spec.
  Proof.
    start_function.
    (*go through series of semax Delta P statement P'; till semax Delta P' Sskip POSTC can be proved*)
    (*first read*)
    assert(semax Delta 
    (
      PROP ( )
      LOCAL (temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))
    (overridePost (
      PROP ( )
      LOCAL (temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    ) POSTCONDITION)). { forward. entailer!. }
    (*first read stored*)
    Definition l1 := (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)).
    (*second read*)
    assert(semax Delta 
    (
      PROP ( )
      LOCAL (temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))
    (overridePost (
      PROP ( )
      LOCAL (temp _b2 (Vint (Int.repr b));temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    ) POSTCONDITION)). { forward. entailer!. }
    Definition list2 := l1 :: [(Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))].
    (*first write*)
    assert(semax Delta 
    (
      PROP ( )
      LOCAL (temp _b2 (Vint (Int.repr b));temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))
    (overridePost (
      PROP ( )
      LOCAL (temp _b2 (Vint (Int.repr b));temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr a)) y)
    ) POSTCONDITION)). { forward. entailer!. }
    (*append list2 to another list: list3*)
    Definition list3 := list2 ++ [(Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))].
    (*last write x points to b*)
    assert(semax Delta 
    (
      PROP ( )
      LOCAL (temp _b2 (Vint (Int.repr b));temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr a)) y)
    )
    (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint))
    (overridePost (
      PROP ( )
      LOCAL (temp _b2 (Vint (Int.repr b));temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr b)) x;
      data_at sh2 tint (Vint (Int.repr a)) y)
    ) POSTCONDITION)). { forward. entailer!. }
    (*append list3 to another list: list4*)
    Definition list4 := list3 ++ [(Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint))].
    (*Prove Sskip -> POSTC from the established POST in the previous step*)
    assert(semax Delta 
    (
      PROP ( )
      LOCAL (temp _b2 (Vint (Int.repr b));temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr b)) x;
      data_at sh2 tint (Vint (Int.repr a)) y)
    )
    Sskip
    POSTCONDITION). { unfold POSTCONDITION. unfold abbreviate. forward. entailer!. }
    (*establsihed; convert list to statement - which is the synthesized program*)
    Definition synthProg := (constructstatement list4).
    assert (semax Delta 
    (
      PROP ( )
      LOCAL (temp _x x; temp _y y)
      SEP (data_at sh1 tint (Vint (Int.repr a)) x;
      data_at sh2 tint (Vint (Int.repr b)) y)
    )
    synthProg
    POSTCONDITION
    ). {
      unfold synthProg. simpl. unfold l1. unfold POSTCONDITION. unfold abbreviate.
      fastforward.  entailer!.
    }
  Admitted.

