Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.getKthElement.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*kth index in a one-indexed array: return a[k - 1] if possible*)
Definition getkthElement_spec : ident * funspec :=
    DECLARE _getkthElement
      WITH a : val, sh : share, k : Z, length : Z, contents : list Z
       PRE [ tptr tuint, tint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned;  Int.min_signed <= k <= Int.max_signed;
        Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
        PARAMS (a; Vint (Int.repr k); Vint (Int.repr length))
        SEP (data_at sh (tarray tuint length) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
        EX kt : Z, EX i: Z,
        (*PROP (if (Z_lt_dec kt 1) then i = -1 else if (Z_gt_dec kt length) then i = -1 
             else i = (Znth (kt - 1) contents))*)
       PROP (if (kt <? 1) then i = -1 else if (kt >? length) then i = -1 
             else i = (Znth (kt - 1) contents))
        RETURN (Vint (Int.repr i))
        SEP(data_at sh (tarray tuint length) (map Vint (map Int.repr contents)) a).

Definition Gprog := [ getkthElement_spec].

Lemma proj_sumbool_false:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = false -> Q.
Proof.
  intros P Q a. destruct a; simpl. intros. inversion H. intros. assumption.
Qed.

Lemma spec_proof: semax_body Vprog Gprog f_getkthElement getkthElement_spec.
Proof. 
  start_function. apply semax_if_seq. forward_if. forward. forward_if. forward.
  Exists k. Exists (-1). destruct (k <? 1) eqn:Hltd. entailer!!. 
  Search (_ <? _) false. apply Z.ltb_ge in Hltd. apply Z.le_ge in Hltd. contradiction.
  inversion H4. forward. forward_if. forward. unfold zlt in H4. apply proj_sumbool_true in H4.
  Exists k. Search (_ <? _). apply Z.ge_le in H3. apply Zaux.Zlt_bool_false in H3. apply Zaux.Zlt_bool_true in H4.
  rewrite Z.gtb_ltb. rewrite H3, H4. Exists (-1). entailer!!. apply proj_sumbool_false in H4. 
  assert (k - 1 >= 0) by lia. assert (k - 1 < length) by lia. 
  forward. forward. Exists k. Search (_ <? _). apply Z.ge_le in H3.
  apply Zaux.Zlt_bool_false in H3. apply Z.ge_le in H4.
  apply Zaux.Zlt_bool_false in H4.  Search (_ >? _). rewrite <- Z.gtb_ltb in H4.
  rewrite H3, H4. Exists (Znth (k - 1) contents). entailer!!.
Qed.


