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

(*varspec: global variables
  funspec: set of functions (Gprog)
  function: function should be a member of funspec
  ident * funspec: specification
*)

(*Read: introduce a new temp. variable; 
 semax Delta P c Q -> semax Delta P' c Q.
 P and Q: PROP, LOCAL and SEP; 
 Read: Add stuff to LOCAL*)

Definition Gprog := [swap_spec].


Lemma body_swap: semax_body Vprog Gprog f_swap swap_spec.
Proof.
  start_function.
  eapply semax_seq with (Q := PROP ( )
  LOCAL (temp _a2 (Vint (Int.repr a));temp _x x; temp _y y)
  SEP (data_at sh1 tint (Vint (Int.repr a)) x;
  data_at sh2 tint (Vint (Int.repr b)) y)). 
  Print load_tac.
  (*unable to apply load_tac and semax_SC_set*) 
  (*eapply semax_SC_set.
  Print semax_seq.



  unfold POSTCONDITION. unfold abbreviate.

  try unfold stackframe_of. simpl fn_vars. simpl map.
      simple eapply canonicalize_stackframe.
  unfold stackframe_of. simpl map. simpl. s
  
  Search fold_right nil.
  rewrite fold_right_nil. Print emp_sepcon. Search emp. 
  Print frame_ret_assert. Search normal_ret_assert emp.
  Print emp_sepcon. rewrite <- emp_sepcon.
  
  rewrite frame_ret_assert_emp.

  forward. unfold stackframe_of. simpl. simpl.
  apply sepcon_derives.

  eapply semax_skip.

  
  
  unfold abbreviate in POSTCONDITION.
  Check normal_ret_assert. unfold normal_ret_assert in POSTCONDITION.
  Check RA_normal. Check RA_break.
  Check POSTCONDITION.(RA_normal). *)

Admitted.

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

(*generic swap function template*)
Definition f_swap (s : statement) := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a2, tint) :: (_b2, tint) :: nil);
  fn_body :=
    s
|}.

(* Packaging the API specs all together. *)
Definition GprogThree := [swap_spec; swap_readspecx; swap_writespecx].

Definition c : statement := (Ssequence
(Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)) Sskip).

Definition cr : statement := (Ssequence
(Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)) Sskip).
Check Sset.
Definition cx : statement := 
(Ssequence
  (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))
  (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint))
).


Lemma body_swapmain: semax_body Vprog GprogThree (f_swap c) swap_spec.
Proof.
Admitted.
