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

Check Forall.

(*Zeroing all contents of an array*)
Definition setarray_spec : ident * funspec :=
  DECLARE _setarray
    WITH a: val, sh : share, contents : list Z, size: Z, i : Z
      PRE [ tptr tint, tint ]
        PROP  (writable_share sh; 1 <= size <= Int.max_signed;
        0 <= i < size; Zlength contents = size; 
        Forall (fun x => x = 0) (sublist (i + 1) size contents);
        Forall (fun x => 0 <= x <= Int.max_signed) contents)
        PARAMS (a;  Vint (Int.repr i))
        SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)
      POST [ tvoid ]
        EX contents_l:list Z,
        PROP (Forall (fun x => x = 0) contents_l) 
        RETURN ()
        SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents_l)) a). 

(*weakend*)
Definition linsearch_spec : ident * funspec :=
  DECLARE _linsearch
    WITH a: val, sh : share, contents : list Z, size: Z, e : Z, ind : Z
      PRE [ tptr tint, tint, tint ]
      PROP  (readable_share sh;  0 <= size <= Int.max_signed; -1 <= ind < size; 
      (*~In e (sublist (ind + 1) size contents); *)
      Zlength contents = size; Int.min_signed <= e <= Int.max_signed;
      Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
      PARAMS (a;  Vint (Int.repr ind);  Vint (Int.repr e))
      SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)
      POST [ tint ]
       EX i:Z, 
        PROP ((*if in_dec Z.eq_dec e contents then Znth i contents = e else i = -1*))
        (*PROP (~ Z.eq_dec ind (-1) => Znth ind contents = e)*)
        RETURN (Vint (Int.repr (i)))
        SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a). 

Definition maxelem_spec : ident * funspec :=
  DECLARE _maxelem
    WITH a: val, sh : share, contents : list Z, size: Z, m : Z, ind : Z
      PRE [ tptr tint, tint, tint ]
        PROP  (readable_share sh;  0 <= size <= Int.max_signed; -1 <= ind < size;  
              Zlength contents = size; Int.min_signed <= m <= Int.max_signed;
              Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
              Forall (fun x => x <= m) (sublist (ind + 1) size contents)
              )
        PARAMS (a;  Vint (Int.repr ind);  Vint (Int.repr m))
        SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)
      POST [ tint ]
        EX ma : Z,
        PROP (Forall (fun x => x <= ma) (sublist (ind + 1) size contents))
        RETURN (Vint (Int.repr (ma)))
        SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a). 


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
Definition Gprog := [swapskip_spec; swap_spec; swapmath_spec; swapif_spec; swapifcall_spec; factcomp_spec; sumcomp_spec; setarray_spec; linsearch_spec; maxelem_spec].

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


Lemma body_verifylinearsearch: semax_body Vprog Gprog f_linsearch linsearch_spec.
Proof.
  start_function. forward_if. forward.
  Exists (-1). entailer!!.
  (*other part*)
  forward. forward_if. forward. Exists ind. entailer!!.
  forward_call. lia. Intros vret.
  forward. Exists vret. entailer!!.
Qed.

Lemma body_verifylinearsearch: semax_body Vprog Gprog f_linsearch linsearch_spec.
Proof.
  start_function. forward_if. forward.  
  (*empty list*) 
  assert (ind = -1) by lia. rewrite H8 in H1. simpl in H1. 
  rewrite sublist_same in H1 by reflexivity.
  destruct (in_dec Z.eq_dec e contents) eqn:Hrm. contradiction.
  Exists (-1). entailer!!. 
  (*ind >= 0*)
  forward. forward_if. forward. apply repr_inj_signed in H6.
  destruct (in_dec Z.eq_dec e contents) eqn:Hrm. 
  Exists ind. entailer!!. exfalso. unfold not in n. apply n. 
  rewrite <- H6. apply Znth_In. lia. unfold repable_signed. 
  rewrite Forall_forall in H4. apply H4. apply Znth_In; lia.
  unfold repable_signed; assumption. 
  forward_call.
  (*prove recursive part*)
  split. lia. replace (ind - 1 + 1) with ind by lia. 
  rewrite sublist_split with (lo := ind)(mid := ind + 1)(hi := size). 
  unfold not; intros. apply in_app in H7. destruct H7 as [? | ?]. 
  rewrite sublist_len_1 in H7. apply In_Znth in H7. 
  inversion H7. inversion H8. 
  assert (Zlength [Znth ind contents] = 1). { eauto. }
  rewrite H11 in H9. assert (x = 0) by lia. rewrite H12 in H10. 
  rewrite Znth_0_cons in H10. unfold not in H6. apply H6. f_equal.
  assumption. lia. contradiction. lia. lia. Intros vret. 
  forward. destruct (in_dec Z.eq_dec e contents) eqn:Hrm. Exists vret. entailer!!.  
  Exists (-1). entailer!!. 
Qed.

Lemma body_verifymaxelem: semax_body Vprog Gprog f_maxelem maxelem_spec.
Proof.
  start_function. apply semax_if_seq. forward_if. forward. Exists m. entailer!!.
  forward. 
  apply semax_if_seq. forward_if. forward. forward_call. split. lia. 
  split. rewrite Forall_forall in H3. apply H3. apply Znth_In; lia. replace (ind - 1 + 1) with ind by lia. 
  (*split sublist*) rewrite sublist_split with (lo := ind)(mid := ind + 1)(hi := size). 
  apply Forall_app. split. rewrite sublist_len_1 by lia. 
  apply Forall_cons. lia.  apply Forall_nil. rewrite Int.signed_repr in H6. 
  assert (m <= Znth ind contents) by lia. rewrite Forall_forall. intros. rewrite Forall_forall in H4. apply H4 in H8.
  lia.  rewrite Forall_forall in H3. apply H3. apply Znth_In; lia. lia. lia. Intros vret. forward. 
  do 2 rewrite Int.unsigned_repr in H7.
  replace (ind - 1 + 1) with ind in H7 by lia. Exists vret. entailer!!.
  rewrite sublist_split with (lo := ind)(mid := ind + 1)(hi := (Zlength contents)) in H7. 
  apply Forall_app in H7. destruct H7 as [? ?]. assumption. lia. lia. 
  compute. split; intros; discriminate. split. lia. destruct H0.
  destruct H.  apply Z.lt_le_incl in H10. 
  eapply Z.le_trans. eassumption.
  assert (Int.max_signed < Int.max_unsigned). { apply Int.max_signed_unsigned. }
  apply Z.lt_le_incl in H12. lia.
  destruct H0.
  destruct H.  apply Z.lt_le_incl in H10. split. lia.
  eapply Z.le_trans. eassumption.
  assert (Int.max_signed < Int.max_unsigned). { apply Int.max_signed_unsigned. }
  apply Z.lt_le_incl in H12. lia.
  forward_call. split. lia. replace (ind - 1 + 1) with ind by lia. rewrite sublist_split with (lo := ind)(mid := (ind + 1))(hi := size).
  apply Forall_app. split. rewrite sublist_len_1 by lia. apply Forall_Znth. 
  assert (Zlength [Znth ind contents] = 1) by eauto. rewrite H7; intros. assert (i = 0)  by lia. rewrite H9; simpl. 
  rewrite Znth_0_cons. rewrite Int.signed_repr in H6. lia. rewrite Forall_forall in H3.
  apply H3. apply Znth_In; lia. assumption. lia. lia. Intros vret.  do 2 rewrite Int.unsigned_repr in H7. 
  replace (ind - 1 + 1) with ind in H7 by lia. forward. Exists vret. entailer!!. 
  rewrite sublist_split with (lo := ind)(mid := (ind + 1))(hi := (Zlength contents)) in H7 by lia. 
  apply Forall_app in H7. destruct H7 as [? ?]. assumption. compute; split; intros; discriminate.
  (*same proof to be repeated for both cases*)
  destruct H, H0. assert (ind <= Int.max_signed) by lia. assert (Int.max_signed < Int.max_unsigned). { apply Int.max_signed_unsigned. }
  split; lia. 
  destruct H, H0. assert (ind <= Int.max_signed) by lia. assert (Int.max_signed < Int.max_unsigned). { apply Int.max_signed_unsigned. }
  split; lia.   
Qed.

Lemma body_verifysetarray: semax_body Vprog Gprog f_setarray setarray_spec.
Proof.
  start_function. forward. forward_if.
  forward_call(a, sh, upd_Znth i contents 0, size, i - 1).  
  simpl. unfold Frame. entailer!. simpl.
Admitted.

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