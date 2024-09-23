Require Import VST.floyd.proofauto.

Definition key := Z.
Definition value := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> value -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : Z :=
  match t with
  | E => (-1)
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint lookupn (x: key) (t : tree) : bool :=
  match t with
  | E => false
  | T tl k v tr => if x <? k then lookupn x tl
                           else if k <? x then lookupn x tr
                           else true
  end.

Fixpoint isSkewed (t : tree) : bool :=
  match t with
  | E => true
  | T tl k v tr => match (tl, tr) with 
                   | (E, _) => isSkewed tr 
                   | (_, E) => isSkewed tl 
                   | (_, _) => false 
                  end 
  end.

Fixpoint insert (x: key) (v: Z) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint inorderSuccessor (t: tree) : tree :=
  match t with
  | E => t
  | T lt k v rt => match lt with 
                   | E => t 
                   | _ => inorderSuccessor lt 
                   end
  end.

Fixpoint inorderSuccessorKey (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match lt with 
                    | E => k 
                    | _ => inorderSuccessorKey lt 
                    end
  end.

Fixpoint inorderSuccessorValue (t: tree) : Z :=
  match t with
  | E => -1
  | T lt k v rt => match lt with 
                   | E => v 
                   | _ => inorderSuccessorValue lt 
                   end
  end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else (match (a, b) with 
                             | (E, _) => b 
                             | (_, E) => a 
                             | (_, _) => let k' := inorderSuccessorKey b in 
                                        (let v'' := inorderSuccessorValue b in 
                                          T a k' v'' (delete k' b)
                                        )
                            end)
 end.

Fixpoint deleteWand (x: key) (s: tree) : tree :=
  match s with
  | E => E
  | T a y v' b => if  x <? y then T (deleteWand x a) y v' b
                         else if y <? x then T a y v' (deleteWand x b)
                         else (match (a, b) with 
                              | (E, _) => b 
                              | (_, E) => a 
                              | (_, _) => let xn := inorderSuccessor b in 
                                           match xn with 
                                           | E => b
                                           | T lt key v rt => T a key v (deleteWand key b)
                                           end  
                             end)
  end.

Fixpoint ForallS (t: tree) : Prop :=
  match t with
  | E => True
  | T l k v r => ((l = E) \/ (r = E)) /\ ForallS l /\ ForallS r
  end. 
  
Fixpoint ForallLookup (k' : key) (t: tree) : Prop :=
  match t with
  | E => False
  | T l k v r => (k = k') \/ ( k' < k /\ ForallLookup k' l) \/ (k' > k /\ ForallLookup k' r)
  end. 
  
Fixpoint ForallT (P: key -> Prop) (t: tree) : Prop :=
  match t with
  | E => True
  | T l k v r => P k /\ ForallT P l /\ ForallT P r
  end.

Inductive BST : tree -> Prop :=
  | BST_E : BST E
  | BST_T : forall l x v r,
      ForallT (fun y => y < x) l ->
      ForallT (fun y => y > x) r ->
      BST l ->
      BST r ->
      BST (T l x v r).  


Lemma nullIsBST:  BST E.
Proof.
  constructor.
Qed.

Lemma leafIsBST: forall k v, BST (T E k v E).
Proof.
  intros. constructor. simpl. auto. 
  simpl. auto. constructor. constructor.
Qed.

Lemma lookupCorrectness: forall k t, BST t -> (lookupn k t = true <-> ForallLookup k t).
Proof. 
  induction t; intros; simpl. 
  split; intros. inversion H0. inversion H0. 
  split; intros. destruct (k =? k0) eqn:Hkk0. assert (k = k0) by lia; subst. 
  left. reflexivity. destruct (k <? k0) eqn:Hkl. assert (k < k0) by lia. 
  right. left. split. lia. apply IHt1. inversion H; subst. assumption. assumption. 
  assert (k > k0) by lia. right. right. apply Z.gt_lt in H1. apply Z.ltb_lt in H1. 
  rewrite H1 in H0. split. lia. apply IHt2. inversion H; subst. assumption. assumption. 
  destruct H0 as [? | ?]. subst. rewrite Z.ltb_irrefl. reflexivity. 
  destruct H0 as [? | ?]. destruct H0 as [? ?]. apply Z.ltb_lt in H0. rewrite H0. 
  apply IHt1 in H1. assumption. inversion H; subst. assumption. 
  destruct H0 as [? ?]. assert (~ k < k0) by lia. 
  apply Z.ltb_nlt in H2. rewrite H2. apply Z.gt_lt in H0. apply Z.ltb_lt in H0. 
  rewrite H0. apply IHt2 in H1. assumption. inversion H; subst. assumption.
Qed.

Lemma skewedCorrectness: forall t, (isSkewed t = true <-> ForallS t).
Proof. 
  induction t; split; intros. 
  simpl. auto. 
  simpl. reflexivity. 
  simpl. inversion H; subst. destruct t1 eqn: Ht1. 
  split. left. reflexivity. split. simpl. auto. apply IHt2. assumption. 
  destruct t2 eqn:Ht2. split. right. reflexivity. split. apply IHt1. 
  assumption. simpl. auto. inversion H1. 
  inversion H; subst. destruct H1 as [? ?]. destruct H0 as [? | ?]. 
  subst. simpl. apply IHt2. assumption. 
  subst. simpl. destruct t1 eqn:Ht1. reflexivity. apply IHt1 in H1. assumption.
Qed.

Lemma insertUBFacts: forall t x k v, 
ForallT (fun y => y < x) t -> k < x ->
ForallT (fun y => y < x) (insert k v t).
Proof. 
  induction t; intros; simpl. 
  split. assumption. auto. 
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  inversion H. destruct H3 as [? ?]. constructor. assumption. 
  split. specialize IHt1 with x k0 v0. apply IHt1 in H3. assumption. 
  lia. assumption. assert (k0 >= k) by lia. apply Z.ge_le in H1. 
  destruct (k <? k0) eqn:Hkk0. assert (k < k0) by lia. constructor. lia. 
  inversion H; subst. destruct H4 as [? ?]. split. assumption. 
  specialize IHt2 with x k0 v0. apply IHt2 in H5. assumption. lia. 
  constructor. lia. inversion H; subst. assumption.
Qed.

Lemma insertLBFacts: forall t x k v, 
ForallT (fun y => y > x) t -> k > x ->
ForallT (fun y => y > x) (insert k v t).
Proof. 
  induction t; intros; simpl. 
  split. assumption. auto. 
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  inversion H. destruct H3 as [? ?]. constructor. assumption. 
  split. specialize IHt1 with x k0 v0. apply IHt1 in H3. assumption. 
  lia. assumption. assert (k0 >= k) by lia. apply Z.ge_le in H1. 
  destruct (k <? k0) eqn:Hkk0. assert (k < k0) by lia. inversion H; subst. 
  constructor. lia. destruct H4 as [? ?]. split.  assumption. 
  specialize IHt2 with x k0 v0. apply IHt2 in H5. assumption. lia. 
  constructor. lia. inversion H; subst. assumption.
Qed.

Lemma inorderSuccBaseCase: forall k v lr, inorderSuccessorKey (T E k v lr) = k.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma inSuccLemma: forall k v lr lt' k' v' lr', inorderSuccessorKey (T (T lt' k' v' lr') k v lr) = inorderSuccessorKey (T lt' k' v' lr').
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma inSuccNodeLemma: forall k v lr lt' k' v' lr', inorderSuccessor (T (T lt' k' v' lr') k v lr) = inorderSuccessor (T lt' k' v' lr').
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma forallLessThanProperty: forall t x, ForallT (fun y => y < x) t -> ForallT (fun y => y <= x) t.
Proof.
  induction t; intros.
  simpl. auto. 
  inversion H; subst. destruct H1 as [? ?]. simpl. split. 
  lia. split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma forallGreaterThanProperty: forall t x, ForallT (fun y => y > x) t -> ForallT (fun y => y >= x) t.
Proof.
  induction t; intros.
  simpl. auto. 
  inversion H; subst. destruct H1 as [? ?]. simpl. split. 
  lia. split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma succHelper: forall lt k v lr,  BST (T lt k v lr) -> (lt <> E) -> k > inorderSuccessorKey lt.
Proof.
  induction lt; intros. 
  contradiction. 
  destruct lt1 eqn:Hlt1. simpl. inversion H; subst. 
  inversion H5; subst. lia. 
  rewrite inSuccLemma. apply IHlt1 with v0 lr. constructor.
  inversion H; subst.  inversion H5; subst. destruct H2 as [? ?]. 
  assumption. inversion H; subst. assumption. 
  inversion H; subst. inversion H7; subst. assumption. 
  inversion H; subst. assumption. unfold not. intros. inversion H1. 
Qed.

Lemma forallTProperty: forall t x k, x > k -> ForallT (fun y => y > x) t -> ForallT (fun y => y > k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H0; subst. destruct H2 as [? ?]. split. lia. 
  split. apply IHt1 with x. lia. assumption. 
  apply IHt2 with x. lia. assumption.
Qed.

Lemma forallTLtProperty: forall t x k, x < k -> ForallT (fun y => y < x) t -> ForallT (fun y => y < k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H0; subst. destruct H2 as [? ?]. split. lia. 
  split. apply IHt1 with x. lia. assumption. 
  apply IHt2 with x. lia. assumption.
Qed.

Lemma forallTGtNotProperty: forall t k, ForallT (fun y => y > k) t -> ForallT (fun y => y <> k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H; subst. destruct H1 as [? ?]. split. lia. 
  split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma forallTNotLtGtProperty: forall t k, ForallT (fun y => y <> k) t <-> ForallT (fun y => y < k \/ y > k) t. 
Proof.
  induction t; split; intros. 
  simpl. auto. simpl. auto. 
  inversion H; subst. destruct H1 as [? ?].  
  simpl. split. lia. split. apply IHt1. assumption.
  apply IHt2. assumption. simpl. inversion H; subst. 
  split. lia. split. apply IHt1. destruct H1 as [? ?]. 
  assumption. apply IHt2. destruct H1 as [? ?]. 
  assumption. 
Qed.

Lemma forallTLtNotProperty: forall t k, ForallT (fun y => y < k) t -> ForallT (fun y => y <> k) t.
Proof.
  induction t; intros; simpl. 
  auto. 
  inversion H; subst. destruct H1 as [? ?]. split. lia. 
  split. apply IHt1. assumption. 
  apply IHt2. assumption.
Qed.

Lemma inorderSuccRange: forall t lo hi, BST t -> t <> E -> ForallT (fun y => y > lo) t -> ForallT (fun y => y < hi) t -> 
lo < inorderSuccessorKey t < hi.
Proof.
  induction t; intros. contradiction.  
  destruct t1 eqn:Ht1. simpl. 
  inversion H1; subst. inversion H2; subst. lia. 
  rewrite inSuccLemma. apply IHt1.
  inversion H; subst. assumption. unfold not. intros. inversion H3. 
  inversion H1; subst. destruct H4 as [? ?]. assumption. 
  inversion H2; subst. destruct H4 as [? ?]. assumption.
Qed.

Lemma inorderSuccHi: forall t hi, BST t -> t <> E ->  ForallT (fun y => y < hi) t -> 
inorderSuccessorKey t < hi.
Proof.
  induction t; intros. contradiction.   
  destruct t1 eqn:Ht1. simpl. 
  inversion H1; subst. lia.  
  rewrite inSuccLemma. apply IHt1. 
  inversion H; subst. assumption. unfold not. intros. inversion H2. 
  inversion H1; subst. destruct H3 as [? ?]. assumption. 
Qed.

Lemma inorderSuccLo: forall t lo, BST t -> t <> E ->  ForallT (fun y => y > lo) t -> 
inorderSuccessorKey t > lo.
Proof.
  induction t; intros. contradiction.   
  destruct t1 eqn:Ht1. simpl. 
  inversion H1; subst. lia.  
  rewrite inSuccLemma. apply IHt1. 
  inversion H; subst. assumption. unfold not. intros. inversion H2. 
  inversion H1; subst. destruct H3 as [? ?]. assumption. 
Qed.

Lemma inorderSuccHelperRoot: forall lt k v lr,
BST (T lt k v lr) -> lt <> E -> inorderSuccessorKey (T lt k v lr) < k.
Proof.
  induction lt; intros. contradiction.  
  inversion H; subst. inversion H5; subst. 
  destruct lt1 eqn:Hlt1. simpl. lia. 
  apply IHlt1 with k v lt2 in H7. rewrite inSuccLemma. lia. 
  unfold not. intros. inversion H3.
Qed.

Lemma inorderSuccProperty: forall lr lt k v, BST (T lt k v lr) -> (lr <> E) ->
ForallT (fun y => y >= (inorderSuccessorKey lr)) lr /\ (k < (inorderSuccessorKey lr)).
Proof.
  induction lr; intros. 
  contradiction. 
  inversion H; subst. destruct lr1 eqn:Hlr1. split. 
  rewrite inorderSuccBaseCase. simpl. split. lia. split. 
  auto. inversion H8; subst. apply forallGreaterThanProperty. assumption. 
  simpl. inversion H6; subst. lia.  rewrite inSuccLemma.
  assert (T t1 k1 v1 t2 <> E). unfold not. intros. inversion H1. 
  apply IHlr1 with lt k0 v in H1. destruct H1 as [? ?].  split. 
  split.  inversion H8; subst. inversion H6; subst. destruct H4 as [? ?]. 
  apply inorderSuccRange with (T t1 k1 v1 t2) k0 k in H13. lia. 
  unfold not. intros. inversion H10. assumption. assumption.  
  split. assumption. apply forallGreaterThanProperty.  
  inversion H8; subst. apply inorderSuccRange with (T t1 k1 v1 t2) k0 k in H13. 
  apply forallTProperty with k. lia. assumption. unfold not. intros. inversion H3. 
  inversion H6; subst. destruct H4 as [? ?]. assumption. assumption. assumption.
  constructor. assumption. inversion H6; subst. destruct H3 as [? ?]. 
  assumption. assumption. inversion H8; subst. assumption. 
Qed.

Lemma deleteUBFacts: forall t x k, 
BST t -> 
ForallT (fun y => y < x) t ->
ForallT (fun y => y < x) (delete k t).
Proof. 
  induction t; intros; simpl. auto.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  simpl. inversion H0; subst. destruct H3 as [? ?].
  split. lia. split. apply IHt1. inversion H; subst. assumption. assumption. assumption. 
  assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0. 
  assert (k < k0) by lia. simpl. inversion H0; subst. destruct H4 as [? ?]. 
  split. lia. split. assumption. apply IHt2. inversion H; subst. assumption.  assumption.
  assert (k = k0) by lia. subst. clear Hkk0. clear Hk0k.  
  inversion H0; subst. destruct H3 as [? ?]. destruct t2 eqn:Ht2. 
  destruct t1 eqn:Ht1. simpl. auto. assumption. 
  destruct t1 eqn:Ht1. assumption. split. apply inorderSuccHi. inversion H; subst. 
  assumption. unfold not. intros. inversion H5. assumption. split. assumption. 
  apply IHt2. inversion H; subst. assumption. assumption.
Qed.

Lemma deleteLBFacts: forall t x k, 
BST t -> 
ForallT (fun y => y > x) t ->
ForallT (fun y => y > x) (delete k t).
Proof. 
  induction t; intros; simpl. auto.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  simpl. inversion H0; subst. destruct H3 as [? ?].
  split. lia. split. apply IHt1. inversion H; subst. assumption. assumption. assumption. 
  assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0. 
  assert (k < k0) by lia. simpl. inversion H0; subst. destruct H4 as [? ?]. 
  split. lia. split. assumption. apply IHt2. inversion H; subst. assumption.  assumption.
  assert (k = k0) by lia. subst. clear Hkk0. clear Hk0k.  
  inversion H0; subst. destruct H3 as [? ?]. destruct t2 eqn:Ht2. 
  destruct t1 eqn:Ht1. simpl. auto. assumption. 
  destruct t1 eqn:Ht1. assumption. split. apply inorderSuccLo. inversion H; subst. 
  assumption. unfold not. intros. inversion H5. assumption. split. assumption. 
  apply IHt2. inversion H; subst. assumption. assumption.
Qed.

Lemma deleteNoDup: forall t k, BST t -> ForallT (fun y => y <> k) (delete k t).
Proof.
  induction t; intros. simpl. auto. 
  simpl. inversion H; subst.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.  
  simpl. split. lia. split. apply IHt1. assumption. apply Z.lt_gt in H0. 
  apply forallTProperty with t2 k k0 in H0. apply forallTGtNotProperty. assumption. 
  assumption. assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0.  assert (k < k0) by lia.
  simpl.  split. lia. split. apply forallTLtProperty with t1 k k0 in H1. 
  apply forallTLtNotProperty. assumption. assumption. 
  apply IHt2. assumption. assert (k = k0) by lia. subst. 
  clear Hkk0. clear Hk0k. destruct t1 eqn:Ht1. apply forallTGtNotProperty. 
  assumption. destruct t2 eqn:Ht2. apply forallTLtNotProperty. assumption. 
  split. inversion H; subst. apply inorderSuccProperty in H. 
  lia. unfold not. intros. inversion H1. split. apply forallTLtNotProperty. 
  assumption. apply forallTGtNotProperty. apply deleteLBFacts. 
  assumption. assumption.
Qed.

Lemma insertPreservesBST: forall t k v, BST t -> BST (insert k v t).
Proof. 
  induction t; intros; simpl. 
  apply leafIsBST. 
  destruct (k0 <? k) eqn:Hkk0.  assert (k0 < k) by lia.  constructor. 
  eapply insertUBFacts. inversion H; subst. assumption. lia. inversion H; subst. assumption. 
  inversion H; subst. apply IHt1; try assumption. inversion H; subst. assumption. 
  assert (k0 >= k) by lia. apply Z.ge_le in H0. destruct (k <? k0)  eqn:Hk0k. 
  assert (k < k0) by lia. constructor. inversion H; subst.  assumption. 
  apply insertLBFacts. inversion H; subst. assumption. lia. inversion H; subst. assumption. 
  apply IHt2. inversion H; subst. assumption. assert (k = k0) by lia. subst. 
  inversion H; subst. constructor; try assumption.
Qed.

Lemma forallTContradiction: forall t x, t <> E -> ForallT (fun y => y >= x) t -> ~ (ForallT (fun y => y < x) t). 
Proof.
  induction t; intros. contradiction. 
  unfold not. intros. inversion H0; subst. 
  inversion H1; subst. contradiction.
Qed.

Lemma delKeyProperty: forall t k, BST t -> ForallT (fun y => y >= k) t -> ForallT (fun y => y > k) (delete k t).
Proof.
  induction t; intros. 
  simpl. auto.  
  destruct (k =? k0) eqn:Hkk0. assert (k = k0) by lia. subst. 
  simpl. rewrite Z.ltb_irrefl. destruct t1 eqn:Ht1. inversion H; subst. assumption. 
  inversion H0; subst. destruct H2 as [? ?]. 
  inversion H; subst.  apply forallTContradiction in H2. contradiction. unfold not. 
  intros. inversion H4. destruct (k <? k0) eqn:Hkk. assert (k < k0) by lia.  
  inversion H0; subst. contradiction. assert (k0 < k) by lia. simpl.
  apply Z.ltb_lt in H1. rewrite H1. inversion H0; subst. assert (k0 < k) by lia. constructor. 
  lia. inversion H; subst. destruct H3 as [? ?]. split. apply IHt1. assumption. assumption. 
  apply Z.lt_gt in H4. apply forallTProperty with t2 k k0 in H4. assumption. assumption. 
Qed.


Lemma deletePreservesBST: forall t k, BST t -> BST (delete k t).
Proof. 
  induction t; intros. 
  simpl. constructor.  
  simpl. inversion H; subst.
  destruct (k0 <? k) eqn:Hk0k. assert (k0 < k) by lia.   
  constructor. apply deleteUBFacts. assumption. assumption. assumption. 
  apply IHt1. assumption. assumption.
  assert (k0 >= k) by lia. destruct (k <? k0) eqn:Hkk0. 
  constructor. assumption. apply deleteLBFacts. assumption. assumption. 
  assumption. auto. 
  assert (k = k0) by lia. subst. clear Hkk0. clear Hk0k.
  (*destruct t1: E case -> discharged; else destruct t2*)
  destruct t1 eqn:Ht1. assumption. 
  (*destruct t2: E case -> resolved; else -> problemmatic*)
  destruct t2 eqn:Ht2. assumption. constructor. 
  apply inorderSuccProperty in H. destruct H as [? ?]. 
  apply forallTLtProperty with (T t3 k v0 t4) k0 (inorderSuccessorKey (T t5 k1 v1 t6)) in H1. 
  assumption. assumption. unfold not. intros. inversion H1. apply inorderSuccProperty in H. 
  destruct H as [? ?]. apply delKeyProperty. assumption. assumption. unfold not. intros. 
  inversion H1. assumption. apply IHt2. assumption.
  Qed.