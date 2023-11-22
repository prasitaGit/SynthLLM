Require VC.Preface.  (* Check for the right version of VST *)

Require Import VST.floyd.proofauto.
Require Import VC.swap.
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)

(*type mpred*)
Check emp.
Check data_at.

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

(*define map for write - may need to store val*)
Definition val_map := string -> val.
(*update - have a map from string rep. of val to val*)
Definition t_update {A : Type} (m : val_map)
                    (x: string) (v : val) :=
  fun x' => if String.eqb x x' then v else m x'.

(*swap specification*)
Definition swap_spec : ident * funspec :=
  DECLARE _swap
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr b)) x; data_at sh2 tint (Vint (Int.repr a)) y).

(*read x*)
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
(*swap sequence*)
(*(Ssequence
  (Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint))
  (Ssequence
    (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))
    (Ssequence
      (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a2 tint))
      (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint)))))
     
*)
(* Packaging the API specs all together. *)
Definition Gprog := [swap_spec; swap_readspecx; swap_writespecx].

Definition _a2 : ident := $"a2".
Definition _b2 : ident := $"b2".

Definition c : statement := (Ssequence
(Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)) Sskip).

Definition cr : statement := (Ssequence
(Sset _a2 (Ederef (Etempvar _x (tptr tint)) tint)) Sskip).

Definition cx : statement := 
(Ssequence
  (Sset _b2 (Ederef (Etempvar _y (tptr tint)) tint))
  (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b2 tint))
).

(*Define Hoare triples explicitly?*)
Lemma body_readx: semax_body Vprog Gprog (f_swap cr) swap_readspecx.
Proof. start_function.
unfold cr. forward. entailer!. 
Admitted. 


Lemma body_writex: semax_body Vprog Gprog (f_swap cx) swap_writespecx.
Proof. 
  start_function. unfold cx.
  fastforward. entailer!.
Qed.


Lemma body_swap: semax_body Vprog Gprog (f_swap c) swap_spec.
Proof.
  start_function. unfold c.
  unfold POSTCONDITION. unfold abbreviate.
  Check ret_assert. unfold normal_ret_assert.
  unfold Delta. unfold abbreviate.
Admitted.
