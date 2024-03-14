Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.isEven.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*if number is even, return true else false*)
Definition isEven_spec : ident * funspec :=
    DECLARE _isEven
      WITH n : Z
       PRE [ tint ]
        PROP  (0 <= n <= Int.max_signed; 0 <= Z.modulo n 2 <= Int.max_signed)
        PARAMS ( Vint (Int.repr n))
        SEP (TT)
       POST [ tbool ]
        EX b : bool,
        PROP (if (Z.modulo n 2 =? 0) then b = true else b = false)
        RETURN (bool2val b)
        SEP(TT).

Definition Gprog := [ isEven_spec].

Lemma spec_proof: semax_body Vprog Gprog f_isEven isEven_spec.
Proof.
  start_function. forward_if. destruct H2 as [? ?]. inversion H3. 
  rewrite mods_repr in H1. forward. apply repr_inj_signed in H1. rewrite H1.
  rewrite Z.eqb_refl. Exists true. entailer!!. unfold repable_signed. 
  destruct H0. split. assert (Int.min_signed <= 0). { compute. intros. inversion H3. }
  Search (_ <= _). eapply Z.le_trans. eassumption. assumption.
  lia. unfold repable_signed. compute. split. intros. inversion H2. intros. inversion H2. 
  lia. split. lia. compute. intros. inversion H2. forward. rewrite mods_repr in H1.
  apply repr_neq_e in H1. Search (_ =? _ = false). apply Z.eqb_neq in H1. rewrite H1. 
  Exists false. entailer!!. lia. split. lia. compute. intros. inversion H2.
Qed.




