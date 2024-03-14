Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.minOfThreeNums.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(*if number is a perfect square: returns true*)
Definition minOfThreeNums_spec : ident * funspec :=
    DECLARE _minOfThreeNums
      WITH a : Z, b : Z, c :Z
       PRE [ tint, tint, tint ]
        PROP  (Int.min_signed <= a <= Int.max_signed; 
        Int.min_signed <= b <= Int.max_signed; Int.min_signed <= c <= Int.max_signed)
        PARAMS ( Vint (Int.repr a); Vint (Int.repr b);  Vint (Int.repr c))
        SEP (TT)
       POST [ tint ]
        PROP ()
        RETURN (Vint (Int.repr (Z.min a (Z.min b c))))
        SEP(TT).

Definition Gprog := [ minOfThreeNums_spec].

Lemma proj_sumbool_false:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = false -> Q.
Proof.
  intros P Q a. destruct a; simpl. intros. inversion H. intros. assumption.
Qed.

Lemma spec_proof: semax_body Vprog Gprog f_minOfThreeNums minOfThreeNums_spec.
Proof.
  start_function. apply semax_if_seq. forward_if. forward. forward_if. 
  unfold zlt in H3. apply proj_sumbool_false in H3. forward. f_equal. f_equal.
  Search Z.min. destruct (b <=? c) eqn:Hbc. assert (b <= c) by lia. rewrite Z.min_l.
  reflexivity. rewrite Z.min_l. lia. lia. assert (b > c) by lia. 
  pattern (Z.min b c). rewrite Z.min_r.  rewrite Z.min_l. reflexivity. lia. lia. 
  apply proj_sumbool_true in H3. apply semax_if_seq. forward_if. assert (a = b) by lia. subst. 
  forward. forward_if. unfold zlt in H5. apply proj_sumbool_false in H5. contradiction.
  forward.  f_equal. f_equal. pattern (Z.min b c). rewrite Z.min_r by lia. rewrite Z.min_r by lia. reflexivity.
  assert (c < b) by lia. forward. forward_if. unfold not in H6'. destruct H6'. reflexivity. 
  forward. f_equal. f_equal. pattern (Z.min b c). rewrite Z.min_r by lia. rewrite Z.min_r by lia. reflexivity.
  forward. forward_if. unfold not in H3'. destruct H3'. reflexivity. apply semax_if_seq.
  forward_if.  forward. forward_if. apply proj_sumbool_false in H5. forward. f_equal. f_equal. 
  pattern (Z.min b c). rewrite Z.min_l by lia. rewrite Z.min_r by lia.  reflexivity.
  apply proj_sumbool_true in H5. assert (c < a) by lia. forward. f_equal. f_equal.
  pattern (Z.min b c). rewrite Z.min_r by lia. rewrite Z.min_r by lia.  reflexivity.
  apply Z.lt_gt in H2. inversion H2. inversion H4. rewrite H6 in H7. inversion H7. 
Qed.




