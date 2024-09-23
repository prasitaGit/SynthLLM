Require VC.Preface.
Require Import VST.floyd.proofauto.
Require Import LLMSynth.treelistdef.
Require Import LLMSynth.bstFunctionalProofs.


 #[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined. 

Definition t_list := Tstruct _sll noattr.
Definition t_struct_tree := Tstruct _tree noattr.

Fixpoint listrep (sigma: list Z) (p: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, !! (Int.min_signed <= h <= Int.max_signed) && 
      data_at Tsh t_list (Vint (Int.repr h),y) p  *  listrep hs y
 | nil => 
    !! (p = nullval) && emp
 end.

 (*sllbox - pointer to a list*)
 Definition sllbox_rep (t: list Z) (b: val) :=
 EX p: val, data_at Tsh (tptr t_list) p b * listrep t p.

Lemma listrep_local_facts:
 forall sigma p,
  listrep sigma p |--
  !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
 induction sigma; intros. 
 unfold listrep; fold listrep. entailer!!. 
 split; intros; reflexivity. 
 unfold listrep; fold listrep. entailer.
 entailer!. split; intro. subst.
 eapply field_compatible_nullval; eauto. inversion H3.
Qed.

Lemma listrep_local_nonullfacts:
 forall sigma p,
  p <> nullval ->
  listrep sigma p |-- !! (sigma <> nil).
Proof.
 induction sigma; intros. 
 unfold listrep; fold listrep.  entailer!.
 apply IHsigma in H. unfold listrep; fold listrep. Intros y.
 entailer!.
Qed.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 unfold listrep.
 destruct sigma; simpl.
- 
  hint.
  entailer!.
- (**  The cons case *)
  Intros y.
  auto with valid_pointer.
Qed.

#[export] Hint Resolve listrep_local_facts : saturate_local. (*pure propositional facts*)
#[export] Hint Resolve listrep_local_nonullfacts : saturate_nonlocal. (*pure propositional facts*)
#[export] Hint Resolve listrep_valid_pointer : valid_pointer. (*valid pointers*)

Lemma listrep_null: forall contents x,
  x = nullval ->
  listrep contents x = !! (contents=nil) && emp.
Proof.
  intros. apply pred_ext. entailer. assert (nullval = nullval) by reflexivity. 
  apply H0 in H. subst. unfold listrep; fold listrep. entailer!!.
  subst. entailer. unfold listrep; fold listrep. entailer!!.
Qed.

Lemma listrep_nonnull: forall contents x,
  x <> nullval ->
  listrep contents x =
    EX h: Z, EX hs: list Z, EX y:val,
      !! (contents = h :: hs) && !! (Int.min_signed <= h <= Int.max_signed) && 
      data_at Tsh t_list (Vint (Int.repr h), y) x * listrep hs y.
Proof.
  intros. apply pred_ext. entailer. destruct contents eqn:Hcon.
  assert ((@nil Z) = (@nil Z)) by list_solve. apply H0 in H1. contradiction. 
  Exists z l. unfold listrep at 1; fold listrep. Intros y. Exists y. entailer!.
  entailer. unfold listrep at 2; fold listrep. Exists y. entailer!.
Qed. 

Lemma nullContradiction: forall sh t v, data_at sh t v nullval = FF. 
Proof.
  intros; apply pred_ext; entailer. 
  eapply field_compatible_nullval1 in H. contradiction.
Qed.

(*Trees*)

Fixpoint tree_rep (t: tree) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ Int.min_signed <= v <= Int.max_signed) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(Vint (Int.repr v),(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.

Definition treebox_rep (t: tree) (b: val) :=
    EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.
   
Lemma tree_rep_saturate_local:
    forall t p, tree_rep t p |-- !! is_pointer_or_null p.
Proof.
   destruct t; simpl; intros.
   entailer!!.
   Intros pa pb. entailer!.
Qed.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; Intros; try Intros pa pb; subst; auto with valid_pointer.
Qed.

Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

#[export] Hint Resolve tree_rep_saturate_local: saturate_local.
#[export] Hint Resolve tree_rep_valid_pointer: valid_pointer.
#[export] Hint Resolve treebox_rep_saturate_local: saturate_local.

Lemma tree_contradict: forall k v t1 t2, 
!! (T t1 k v t2 = E) = FF.
Proof.
 intros. apply pred_ext. entailer. inversion H. entailer.
Qed.

Lemma tree_rep_null: forall t x,
  x = nullval -> 
  tree_rep t x = !! (t = E) && emp.
Proof.
  intros. rewrite H. apply pred_ext. 
  destruct t; [entailer!! |]. simpl tree_rep. entailer!!.
  unfold tree_rep; fold tree_rep. Intros pa pb. rewrite nullContradiction. 
  rewrite tree_contradict. entailer. 
  entailer. unfold tree_rep. entailer!!. 
Qed.

Lemma tree_rep_notnull: forall t x,
  x <> nullval ->
  tree_rep t x = EX k: Z, EX v: Z, EX a: tree, EX b: tree, EX pa:val, EX pb:val,
               !! (t = T a k v b) &&  !! (Int.min_signed <= k <= Int.max_signed /\ Int.min_signed <= v <= Int.max_signed) &&
    data_at Tsh t_struct_tree (Vint (Int.repr k),(Vint (Int.repr v),(pa,pb))) x *
    tree_rep a pa * tree_rep b pb.
Proof.
  intros. apply pred_ext. 
  destruct t eqn:Ht. unfold tree_rep at 1. entailer!!. 
  unfold tree_rep at 1; fold tree_rep. Intros pa pb. Exists k v t0_1 t0_2 pa pb. 
  entailer!!.
  Intros k v a b pa pb. entailer!!. unfold tree_rep at 3; fold tree_rep. 
  Exists pa pb. entailer!!.
Qed.

#[export] Hint Resolve tree_rep_null: saturate_local. 
#[export] Hint Resolve tree_rep_notnull: saturate_local.

Lemma treebox_rep_leaf: forall x p b v,
Int.min_signed <= v <= Int.max_signed ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (Vint (Int.repr v), (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!!.
Qed.

Lemma typed_true_semcastCeq_eq:
  forall x y : val, typed_true tint 
  match sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y)) with 
  | Some v' => v'
  | None => Vundef
  end -> x = y.
Proof.
  intros. hnf in H.  
  unfold sem_cmp_pp, Val.cmplu_bool, Val.cmpu_bool in *.
  destruct Archi.ptr64; simpl in H;
  destruct x, y; inv H; try congruence; simpl in *; f_equal;
  try solve [destruct (andb _ _) in H1; inv H1].
  pose proof (Int64.eq_spec i i0); destruct (Int64.eq i i0); auto; inv H1.
  destruct (eq_block b b0); auto; inv H1.
  pose proof (Ptrofs.eq_spec i i0); destruct (Ptrofs.eq i i0); auto; inv H1.
  destruct (eq_block b b0); auto; inv H2.
  pose proof (Int.eq_spec i i0); destruct (Int.eq i i0); auto; inv H1.
  destruct (eq_block b b0); auto; inv H1. 
  destruct (eq_block b b0); auto; inv H1.
  pose proof (Ptrofs.eq_spec i i0); destruct (Ptrofs.eq i i0); auto; inv H0.
Qed.

Lemma typed_false_semcastCeq_eq:
  forall x y : val, typed_false tint 
  match sem_cast_i2bool (force_val (sem_cmp_pp Ceq x y)) with 
  | Some v' => v'
  | None => Vundef
  end -> x <> y.
Proof.
  intros. hnf in H. 
  unfold sem_cmp_pp, Val.cmplu_bool, Val.cmpu_bool in *.
  destruct Archi.ptr64; simpl in H;
  destruct x, y; inv H; try congruence; simpl in *; f_equal;
  try solve [destruct (andb _ _) in H1; inv H1];
  intro Hx; inv Hx.
  -  rewrite Int64.eq_true in H1. inv H1.
  -  destruct (eq_block b0 b0); try contradiction. inv H1.
     rewrite Ptrofs.eq_true in H0; inv H0.
  - rewrite Int.eq_true in H1. inv H1.
  - destruct (eq_block b0 b0); try contradiction. inv H1.
     rewrite Ptrofs.eq_true in H0; inv H0.
Qed.   





