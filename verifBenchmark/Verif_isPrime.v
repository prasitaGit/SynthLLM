Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.isPrime.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Lemma elevenRange : 0 < 11 <= Int.max_signed.
Proof.
    split. lia. 
    compute. intros. inversion H.
Qed.

Search Z.modulo.
(*if number is prime, return true else false*)
Definition isPrime_spec : ident * funspec :=
    DECLARE _isPrime
      WITH n : Z, div : Z
       PRE [ tint, tint ]
        PROP  (0 <= n <= Int.max_signed; 2 <= div <= n;
        0 <= Z.modulo n div <= Int.max_signed)
        PARAMS ( Vint (Int.repr n); Vint (Int.repr div))
        SEP (TT)
       POST [ tbool ]
        EX b : bool,
        PROP (if (n =? 2) then b = true else if (n =? 3) then b = true 
         else if (div >=? n) then b = true else b = false)
        RETURN (bool2val b)
        SEP(TT).

Definition Gprog := [ isPrime_spec].
(*define my own stuff for the proof*)

(*add this lemma to compcert?*)
Lemma proj_sumbool_false:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = false -> Q.
Proof.
  intros P Q a. destruct a; simpl. intros. inversion H. intros. assumption.
Qed.

Lemma spec_proof: semax_body Vprog Gprog f_isPrime isPrime_spec.
Proof.
  start_function. apply semax_if_seq. forward_if. forward. forward_if.
  forward. Exists true. rewrite Z.eqb_refl. entailer!!. 
  forward_if. inversion H3. inversion H3. forward.
  forward_if.  unfold zeq in H3. apply proj_sumbool_true in H3.
  forward. apply Z.eqb_neq in H2. rewrite H2. rewrite Z.eqb_refl. Exists true. entailer!!.
  rewrite H3. forward_if. forward. 
  unfold zeq in H3. apply proj_sumbool_false in H3. apply Z.eqb_neq in H2, H3. 
  rewrite H2, H3. Search ( _ >=? _ = true). apply Z.geb_ge in H4. rewrite H4. 
  Exists true. entailer!!.
  unfold zeq in H3. apply proj_sumbool_false in H3. 
  forward_if. split. unfold not. intros. apply repr_inj_signed in H6.
  destruct H0. rewrite H6 in H0. destruct H0. simpl. reflexivity.
  unfold repable_signed. destruct H0, H1. split. assert (Int.min_signed <= 2). { compute. intros. inversion H9. }
  eapply Z.le_trans. eassumption. assumption. lia. unfold repable_signed.
  compute. split; intros. inversion H. inversion H7. inversion H7. unfold not.
  intros. destruct H6 as [? ?]. Search Int.mone. apply repr_inj_signed in H6. 
  rewrite H6 in H. destruct H. assert (Int.min_signed < 0). {
    compute. reflexivity.
  }
  apply Z.le_ge in H. contradiction. unfold repable_signed. destruct H.
  split. assert (Int.min_signed <= 0). { compute. intros. inversion H9. }
  eapply Z.le_trans. eassumption. assumption. lia. unfold repable_signed. split.
  lia. compute. intros. inversion H8. forward. apply Z.eqb_neq in H2, H3. 
  Search (_ >=? _). destruct (div >=? n) eqn:Hdiv. assert (div >= n) by lia. 
  contradiction. rewrite H2, H3. Exists false. entailer!!. 
  forward_call. 
Admitted.




