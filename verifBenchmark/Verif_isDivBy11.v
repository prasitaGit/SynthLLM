Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.isDivby11.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.
(*Require Import Arith.Even.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Lemma elevenRange : 0 < 11 <= Int.max_signed.
Proof.
    split. lia. 
    compute. intros. inversion H.
Qed.

(*if number is div by 11, return true else false*)
Definition isDivBy11_spec : ident * funspec :=
    DECLARE _isDivBy11
      WITH n : Z
       PRE [ tint ]
        PROP  (0 <= n <= Int.max_signed; 0 <= Z.modulo n 11 <= Int.max_signed)
        PARAMS ( Vint (Int.repr n))
        SEP (TT)
       POST [ tbool ]
        EX b : bool,
        PROP (if (Z.modulo n 11 =? 0) then b = true else b = false)
        RETURN (bool2val b)
        SEP(TT).

Definition Gprog := [ isDivBy11_spec].

Lemma spec_proof: semax_body Vprog Gprog f_isDivBy11 isDivBy11_spec.
Proof.
  start_function. forward_if. destruct H2 as [? ?]. inversion H3. 
  rewrite mods_repr in H1. forward. apply repr_inj_signed in H1. rewrite H1.
  rewrite Z.eqb_refl. Exists true. entailer!!. unfold repable_signed. 
  destruct H0. split. assert (Int.min_signed <= 0). { compute. intros. inversion H3. }
  eapply Z.le_trans. eassumption. assumption.
  lia. unfold repable_signed. compute. split. intros. inversion H2. intros. inversion H2. 
  lia. apply elevenRange. forward. rewrite mods_repr in H1.
  apply repr_neq_e in H1.  apply Z.eqb_neq in H1. rewrite H1. 
  Exists false. entailer!!. lia. apply elevenRange.
Qed.




