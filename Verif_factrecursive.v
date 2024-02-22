Require VC.Preface.  (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VC.swap.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined. (*Global variable*)
Require Import ZArith.


Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.


Definition factcomp_spec : ident * funspec :=
  DECLARE _factcomp
   WITH n : Z
   PRE [ tuint ]
    PROP  (0 <= n <= Int.max_unsigned)
    PARAMS (Vint (Int.repr n))
    SEP (TT)
   POST [ tuint ]
    PROP () 
    RETURN (Vint (Int.repr (Z.of_nat (factorial (Z.to_nat n)))))
    SEP (TT).

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


(*math - x is assigned to y + 1*)
Definition swapmath_spec : ident * funspec :=
  DECLARE _swapmath
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (readable_share sh1; writable_share sh2; 
    Int.min_signed <= Int.signed (Int.repr a) * Int.signed (Int.repr 2) <= Int.max_signed)
    (*LOCAL (temp _x x; temp _y y)*)
    PARAMS (x; y)
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN ()
    (*SEP(emp)*)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr (a * 2))) y). 

(*if spec: *)
Definition swapif_spec : ident * funspec :=
  DECLARE _swapif
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= a <= Int.max_signed; Int.min_signed <= b <= Int.max_signed;
    Int.min_signed <= (a + 1) <= Int.max_signed; Int.min_signed <= (b + 1) <= Int.max_signed)
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN () 
    (SEPx(
      if Z_lt_ge_dec a b then 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr (a + 1))) y :: nil)) 
      else 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr (b + 1))) y :: nil))
      )
    ).


(*if call spec: *)
Definition swapifcall_spec : ident * funspec :=
  DECLARE _swapifcall
   WITH x: val, y: val, sh1 : share, sh2 : share, a : Z, b : Z
   PRE [ tptr tint, tptr tint ]
    PROP  (writable_share sh1; writable_share sh2; 
    Int.min_signed <= a <= Int.max_signed; Int.min_signed <= b <= Int.max_signed;
    Int.min_signed <= (a + 1) <= Int.max_signed; Int.min_signed <= (b + 1) <= Int.max_signed)
    PARAMS (x; y)
    SEP (data_at sh1 tint (Vint (Int.repr a)) x; data_at sh2 tint (Vint (Int.repr b)) y)
   POST [ tvoid ]
    PROP () RETURN () 
    (SEPx(
      if Z_lt_ge_dec a b then 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr (a + 1))) y :: nil)) 
      else 
      (data_at sh1 tint (Vint (Int.repr b)) x :: (data_at sh2 tint (Vint (Int.repr (b + 1))) y :: nil))
      )
    ). 

Definition sumcomp_spec : ident * funspec :=
  DECLARE _sumcomp
    WITH n : Z
      PRE [ tuint ]
      PROP  (0 <= n <= Int.max_unsigned(*; 0 <= n - 1 <= Int.max_unsigned*))
      PARAMS (Vint (Int.repr n))
      SEP (TT)
      POST [ tuint ]
      PROP () 
      RETURN (Vint (Int.repr (n * (n + 1)/2)))
      SEP (TT).

Ltac autoltac :=
  match goal with
  | |- semax _ _ (Sifthenelse _ _ _)  _ => forward_if; autoltac
  | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _)  _ => apply semax_if_seq; autoltac
  | |- semax _ _ (Scall _ _ _)  _ => forward_call
  | |- semax _ _ (Ssequence (Scall _ _ _) _) _ => forward_call; autoltac
  | |- semax _ _ _ _ => forward; autoltac
  | |- ?Pr |-- ?Po => try entailer!
  | |- _ => idtac "Ooops! can't solve it."
  end.

(*Pack APIs together*)
Definition Gprog := [swapskip_spec; swap_spec; swapmath_spec; swapif_spec; swapifcall_spec; factcomp_spec; sumcomp_spec].

(*swap only*)
Lemma swapSynthAuto: semax_body Vprog Gprog f_swap swap_spec.
Proof.
  start_function. autoltac.
Qed.

(*swap math: swapmath_spec*)
Lemma swapmathSynthAuto: semax_body Vprog Gprog f_swapmath swapmath_spec.
Proof.
  start_function. autoltac.
Qed.

(*swap - if: swapif_spec*)
Lemma swapifSynthAuto: semax_body Vprog Gprog f_swapif swapif_spec.
Proof.
  start_function. autoltac.
Admitted.

(*swap - if with call to swap: swapifcall_spec*)
Lemma swapifCallSynthAuto: semax_body Vprog Gprog f_swapifcall swapifcall_spec.
Proof.
  start_function. autoltac.
Admitted.

(*verify sumcomp_spec - from here*)
Lemma body_verifysumfuncauto: semax_body Vprog Gprog f_sumcomp sumcomp_spec.
Proof. 
  start_function. autoltac.
Admitted.

(*verify sumcomp_spec - from here*)
Lemma body_verifysumfunc: semax_body Vprog Gprog f_sumcomp sumcomp_spec.
Proof. 
  start_function. forward_if. forward. forward_call.
  apply not_Zeq_inf in H0. destruct H0 as [? | ?]. 
  destruct H.  apply Z.le_ge in H. contradiction. 
  apply Z.lt_gt in l. destruct H.  split. apply Zgt_0_le_0_pred in l. 
  assumption. apply Z.le_le_pred in H0. assumption. forward. 
  replace (n - 1 + 1) with n by lia. f_equal. f_equal.
  replace (n + 1) with ((n - 1) + 2) by lia. rewrite Z.mul_add_distr_l.
  rewrite Z_div_plus. simpl. rewrite Z.add_comm. f_equal. 
  rewrite Z.mul_comm. reflexivity. lia.
Qed.

(*verify fun_spec - from here*)
Lemma body_verifyfuncfact: semax_body Vprog Gprog f_factcomp factcomp_spec.
Proof. 
  start_function. forward_if.
  forward. 
  forward_call (n - 1).  forward.
  f_equal. f_equal. Search Z.to_nat. assert (n > 0) by lia. replace n with (n - 0) by lia. 
  rewrite <- arith_aux01.
  destruct n.
  (*case 0*) contradiction.
  (*case positive*) Search Z.to_nat Z.pos. rewrite Z2Nat.inj_pos. 
  Search Z.pos. rewrite Z.sub_1_r.  Search Z.to_nat Z.pred. rewrite Z2Nat.inj_pred.
  rewrite Z2Nat.inj_pos. destruct (factorial (Pos.to_nat p)). 

Admitted.