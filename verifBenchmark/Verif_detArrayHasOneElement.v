Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.detArrayHasOnlyOneElement.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(*product of the first even and odd number in an array*)
Definition detArrayHasOnlyOneElement_spec : ident * funspec :=
    DECLARE _detArrayHasOnlyOneElement
      WITH a : val, sh : share, ind : Z, length : Z, contents : list Z
       PRE [ tptr tint, tuint, tuint ]
        PROP  (readable_share sh; Zlength contents = length; 
        0 <= length <= Int.max_unsigned; 0 <= ind < length;
        Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
        PARAMS (a; Vint (Int.repr ind); Vint (Int.repr length))
        SEP (data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a)
       POST [ tbool ]
        EX b : bool, EX i : Z,
        PROP (if (Z.eq_dec i (length - 1)) then b = true else b = false)
        RETURN (bool2val b)
        SEP(data_at sh (tarray tint length) (map Vint (map Int.repr contents)) a).

(*only has one element - returns true*)
Definition Gprog := [ detArrayHasOnlyOneElement_spec].

Lemma spec_proof: semax_body Vprog Gprog f_detArrayHasOnlyOneElement detArrayHasOnlyOneElement_spec.
Proof.
    start_function. forward_if. forward. Search Int.repr. apply repr_inj_unsigned in H3.
    Exists true. Exists ind. subst. destruct (Z.eq_dec (Zlength contents - 1) (Zlength contents - 1)) eqn:Hcon. entailer!!.
    unfold not in n. destruct n. reflexivity. destruct H0, H1. split. lia. 
    lia.  destruct H0, H1. lia. forward. Search Int.sub Int.repr. rewrite sub_repr in H3.
    Search Int.repr. apply repr_neq_e in H3. assert (ind < length - 1) by lia. forward. forward_if.
    forward. Exists false. Exists ind. destruct (Z.eq_dec ind (Zlength contents - 1)) eqn:Hedec. contradiction.
    entailer!!. forward_call. lia. Intros vret. forward. Exists (fst vret). Exists (snd vret).
    destruct (Z.eq_dec (snd vret) (Zlength contents - 1)) eqn:hl. entailer!!. rewrite H6. simpl. reflexivity.
    entailer!!. rewrite H6. simpl. reflexivity.
Qed.


