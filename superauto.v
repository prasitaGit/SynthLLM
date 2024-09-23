Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import LLMSynth.sllProof.
Require Import LLMSynth.treelistdef.
Require Import LLMSynth.bstFunctionalProofs.

(*queried ltac: first stage*)
(*
Dealing with the comparison operators: =, <>, <, >, <=, >=,
arithmetic operators: +, -, *, /, %
Types: Z, bool, strings, signed and unsigned supported, some double
Data structures: arrays, linked lists, trees)
C programs recognized by verified compiler Compcert
*)
(*Receive in parameters - spec and everything*)
(*Lemma for nested unfolding*)

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).


Lemma proj_sumbool_false:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = false -> Q.
Proof.
  intros P Q a. destruct a; simpl. intros. inversion H. intros. assumption.
Qed.

Lemma forceval_cast: forall b, force_val (sem_cast_i2bool (bool2val b)) = bool2val b. 
Proof.
  destruct b; simpl; reflexivity.
Qed.

Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, (P |-- Q) -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Ltac try_forward n :=
  match n with
  | S ?n' =>  try (try_forward n')
  | (0)%nat => forward
  end.

Ltac clearMatch H :=
  repeat match goal with
  | [ H' : ?g |- _ ] => progress (tryif (unify H g) then clear H' else idtac )
  end.  

Ltac unifyLeft H g :=
  repeat match goal with
  | [ H' : ?h |- g ] => progress (tryif (unify H h) then left; assumption else idtac)
  end.  

Ltac unifyRight H g :=
  repeat match goal with
  | [ H' : ?h |- g ] => progress (tryif (unify H h) then right; assumption else idtac )
  end. 

(*analyze fail forward wrt Int.repr: *)
Ltac failForward g :=
  match goal with
  | [X: Int.repr _ <> Int.repr _ |- g] =>  apply repr_neq_e in X; failForward g
  | [X: Int.repr ?a = Int.repr _ |- g] =>  (tryif (assert (repable_signed a) by first[list_solve | rep_lia]) then clearMatch (repable_signed a); apply repr_inj_signed in X else apply repr_inj_unsigned in X); 
                                           try solve[rep_lia | list_solve]; failForward g
  | [X: Int.repr ?a = Int.add (Int.repr _) (Int.repr _) |- g] => rewrite add_repr in X; failForward g
  | [X: Int.repr ?a = Int.sub (Int.repr _) (Int.repr _) |- g] => rewrite sub_repr in X; failForward g
  | [X: Int.repr ?a = Int.mul (Int.repr _) (Int.repr _) |- g] => rewrite mul_repr in X; failForward g
  | [X: Int.repr _ <> Int.add (Int.repr _) (Int.repr _) |- g] => rewrite add_repr in X; apply repr_neq_e in X; failForward g
  | [X: Int.repr _ <> Int.sub (Int.repr _) (Int.repr _) |- g] => rewrite sub_repr in X; apply repr_neq_e in X; failForward g
  | [X: Int.repr _ <> Int.mul (Int.repr _) (Int.repr _) |- g] => rewrite mul_repr in X; apply repr_neq_e in X; failForward g
  | [X: _ /\ Int.repr _ = Int.mone |- g] => destruct X; failForward g
  | [X: Int.repr _ = Int.mone /\ _ |- g] =>  destruct X; failForward g
  | [X: ?h |- g] => match h with 
                    | context [Int.signed (Int.repr _)] => rewrite !Int.signed_repr in X by first[list_solve | rep_lia] ; failForward g
                    | context [Int.unsigned (Int.repr _)] => rewrite !Int.unsigned_repr in X by first[list_solve | rep_lia] ; failForward g
                    end
  | [X: ?t = false |- g] => match t with 
                            | context[zeq _ _] => apply proj_sumbool_false in X; failForward g
                            | context[zle _ _] => apply proj_sumbool_false in X; failForward g
                            | context[zlt _ _] => apply proj_sumbool_false in X; failForward g
                            end 
  | [X: ?t = true |- g] => match t with 
                           | context[zeq _ _] => apply proj_sumbool_true in X; failForward g
                           | context[zle _ _] => apply proj_sumbool_true in X; failForward g
                           | context[zlt _ _] => apply proj_sumbool_true in X; failForward g
                           end 
  | [X: Int.repr _ = Int.mone |- g] => inversion X
  | [X: Int.repr _ = Int.repr _ |- g] => inversion X 
  | [X: Int.repr _ = _ |- g] => inversion X 
  | [X: true = false |- g] => inversion X
  | [X: false = true |- g] => inversion X
  | [X: False |- g] => inversion X
  | [X: _ <> _ |- g] => inversion X
  | [X: _ |- g] => idtac g
  | [X: _ |- ?g'] => idtac g'
  end.

Ltac matchTreeAndSubstitute := 
  repeat match goal with 
  | [X: T ?lt ?k ?v ?lr = ?ot |- _] => progress (match ot with 
                                       | T lt k v lr => idtac
                                       | T _ _ _ _ => inversion X; subst 
                                      end)
  end.

Ltac matchListAndSubstitute := 
  repeat match goal with 
  | [X: ?h :: ?hs = ?ot |- _] => progress (match ot with 
                                         | h :: hs => idtac
                                         | _ :: _ => inversion X; subst
                                         | _ => subst 
                                        end)
  | [X: _ = _ :: _ |- _] => subst
  end.
  
Ltac rewriteWrapperInGoal := 
  match goal with 
  | |- ?g => match g with 
             | context[Int.unsigned (Int.repr _)] => rewrite !Int.unsigned_repr by first[rep_lia | list_solve]
             | context[Int.signed (Int.repr _)] => rewrite !Int.signed_repr by first[rep_lia | list_solve]
             | _ => idtac g
             end
  end.

Ltac matchAndrewrite G tac g :=
  repeat match goal with 
  | [X: ?h |- g ] => progress (tryif (unify G h) then apply tac in X; rewrite X; clear X else idtac) 
  end. 

Ltac checkOperatorDischarge2 op o1 o2 g := 
  match op with
  | Z.eqb => match o1 with
              | o2 => rewrite Z.eqb_refl; first[progress entailer! | entailer!!]
              | _ =>  tryif (assert (o1 = o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 = o2) Z.eqb_eq g 
                      else (tryif (assert (o1 <> o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 <> o2) Z.eqb_neq g 
                      else (destruct (o1 =? o2); [ assert (o1 = o2) by lia; matchAndrewrite (o1 = o2) Z.eqb_eq g | 
                      assert (o1 <> o2) by lia; matchAndrewrite (o1 <> o2) Z.eqb_neq g])) 
              end
  | Z.ltb =>  tryif (assert (o1 < o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 < o2) Z.ltb_lt g 
              else (tryif (assert (o2 <= o1) by first[rep_lia | list_solve]) then matchAndrewrite (o2 <= o1) Z.ltb_ge g 
              else (destruct (o1 <? o2); [ assert (o1 < o2) by lia; matchAndrewrite (o1 < o2) Z.ltb_lt g | 
              assert (o2 <= o1) by lia; matchAndrewrite (o2 <= o1) Z.ltb_ge g]))
  | Z.leb => tryif (assert (o1 <= o2) by first[rep_lia | list_solve]) then matchAndrewrite (o1 <= o2) Z.leb_le g 
             else (tryif (assert (o2 < o1) by first[rep_lia | list_solve]) then matchAndrewrite (o2 < o1) Z.leb_gt g 
             else (destruct (o1 <=? o2); [ assert (o1 <= o2) by lia; matchAndrewrite (o1 <= o2) Z.leb_le g | 
             assert (o2 < o1) by lia; matchAndrewrite (o2 < o1) Z.leb_gt g])) 
  | Z.gtb => rewrite Z.gtb_ltb; checkOperatorDischarge2 Z.ltb o2 o1 g
  | Z.geb => rewrite Z.geb_leb; checkOperatorDischarge2 Z.leb o2 o1 g  
end. 

Ltac matchModulo a b Op o g :=
  match goal with
  | [X: ?o' (Int.repr (Z.modulo a b)) (Int.repr o) |- g] => checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: not (?o' (Int.repr (Z.modulo a b)) (Int.repr o)) |- g] => checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: ?o' (Int.mods (Int.repr a) (Int.repr b)) (Int.repr o) |- g] => rewrite mods_repr in X; try rep_lia; apply repr_inj_signed in X; try rep_lia; checkOperatorDischarge2 Op (Z.modulo a b) o g
  | [X: not (?o' (Int.mods (Int.repr a) (Int.repr b)) (Int.repr o)) |- g] => rewrite mods_repr in X; try rep_lia; apply repr_neq_e in X; checkOperatorDischarge2 Op (Z.modulo a b) o g
  end.

Ltac assignandRewrite arg v :=
  match goal with
  | [X:  malloc_compatible ?n v |- _] => assert (sizeof arg = n) as Hszassert by reflexivity; rewrite <- Hszassert
  end.

Ltac fireTreeOrListNotNull sx ind := 
  match sx with
  | nil => idtac
  | tree_rep _ ind :: _ => rewrite (tree_rep_notnull _ ind) by auto;
                           match goal with 
                           | |- context [EX (k : _) (v : _) (a : _) (b : _) (pa : _) (pb : _), _] => 
                              let hkv := fresh k in (let hvv := fresh v in (let hav := fresh a in (let hbv := fresh b in 
                              (let hpav := fresh pa in (let hpbv := fresh pb in Intros hkv hvv hav hbv hpav hpbv)))))
                           end 
  | listrep _ ind :: _ => rewrite (listrep_nonnull _ ind) by auto;
                          match goal with 
                          | |- context [EX (h : _) (hs : _) (y : _), _] => 
                            let hvv := fresh h in (let hsv := fresh hs in (let hyv := fresh y in Intros hvv hsv hyv))
                          end
  | _ :: ?sx' => fireTreeOrListNotNull sx' ind 
  end.
  
Ltac fireTreeOrListNull sx ind := 
  match sx with
  | nil => idtac
  | tree_rep _ ind :: _ => rewrite (tree_rep_null _ ind) by auto 
  (*| listrep _ ind :: _ => rewrite (listrep_null _ ind) by auto *)
  | _ :: ?sx' => fireTreeOrListNull sx' ind 
  end.
  
Ltac triggerNullNoNullTreeOrList sx g :=
  repeat match goal with
  | [X: ?ind <> nullval |- g] => progress (fireTreeOrListNotNull sx ind)
  | [X: ?ind = nullval |- g] => progress(fireTreeOrListNull sx ind)  
  end.
  
Ltac triggerNullNoNullMatch g :=
  match g with 
  | semax _ (PROPx _ (LOCALx _ (SEPx ?sx))) _ _ => triggerNullNoNullTreeOrList sx g 
  end. 
  
(* null check lemma *) 
Ltac triggerNullList :=
 match goal with
 | [X : nullval = nullval <-> ?l = [] |- _] => progress (assert (l = (@nil Z)) by (apply X; reflexivity); subst; clear X)
 end.
 
Ltac doForwardCall l :=
   match l with
   | nil => false
   | (Esizeof ?arg _) :: _ => arg   
   | _ :: ?l' => doForwardCall l'
   end.

Ltac is_var_in_hyps var :=
  match goal with
  | [ H: context[var] |- _ ] => true
  | _ => false
  end. 
  
Ltac sepListMatch sx h :=
  match sx with 
  | nil => constr:((tt))
  | (data_at ?sh _ (Vint (Int.repr ?a)) h) :: _ =>  let x := (is_var_in_hyps sh) in (match x with 
                                                          | true => constr:((sh, a)) 
                                                          | false => constr:((a, tt))
                                                          end)
  | (data_at ?sh _ (Vbyte ?a) h) :: _ =>  let x := (is_var_in_hyps sh) in (match x with 
                                                | true => constr:((sh, a)) 
                                                | false => constr:((a, tt))
                                                end)
  | (data_at ?sh _ (map Vbyte ?a) h) :: _ =>  let x := (is_var_in_hyps sh) in (match x with 
                                                    | true => constr:((sh, a)) 
                                                    | false => constr:((a, tt))
                                                    end)
  | (data_at ?sh _ (map Vint (map Int.repr ?a)) h) :: _ =>  let x := (is_var_in_hyps sh) in (match x with 
                                                                  | true => constr:((sh, a)) 
                                                                  | false => constr:((a, tt))
                                                                  end) 
  | (data_at ?sh _ (Vint (Int.repr ?h), nullval) h) :: _ => let x := (is_var_in_hyps sh) in (match x with 
                                                                  | true => constr:((sh, [h])) 
                                                                  | false => constr:(([h], tt))
                                                                  end)
  | (data_at ?sh _ (Vint (Int.repr ?h), ?h0) h) :: _ =>  let x := (is_var_in_hyps sh) in (let x' :=  sepListMatch sx h0 in 
                                                                  match x with 
                                                                  | true => match x' with 
                                                                            | (?v,tt) => constr:((sh, h :: v))
                                                                            end 
                                                                  | false => match x' with 
                                                                             | (?v,tt) => constr:((h :: v, tt))
                                                                            end               
                                                                  end)
  | (data_at ?sh t_struct_tree (Vint (Int.repr ?keyv), (Vint (Int.repr ?valv), (?pladd, ?pradd))) h) :: _ => 
                let x := (is_var_in_hyps sh) in (let xl := sepListMatch sx pladd in 
                (let xr := sepListMatch sx pradd in   
                 match x with 
                 | true => match xl with 
                           | (?tl,tt) => match xr with 
                                         | (?tr,tt) => constr:((sh, T tl keyv valv tr))
                                         end
                           end 
                 | false => match xl with 
                            | (?tl,tt) => match xr with 
                                          | (?tr,tt) => constr:((T tl keyv valv tr, tt))
                                          end
                            end               
                end))
  | (data_at ?sh _  ?h0 h) :: _ =>  sepListMatch sx h0
  | listrep ?l h :: _ =>  constr:((l,tt))
  | tree_rep ?a h :: _ => constr:((a,tt))
  | sllbox_rep ?l h :: _ => constr:((l,tt))
  | memory_block _ ?n h :: _ => constr:((n,tt))
  | _ :: ?sx' => sepListMatch sx' h
  end.
  
Ltac listMatchReturn lx sx h :=
  match lx with
  | nil => constr:((h,tt))
  | temp h (Vint (Int.repr ?v)) :: _ => constr:((v,tt))
  | temp h (Vbyte ?v) :: _ => constr:((v,tt))
  | temp h ?v :: _ => let x := sepListMatch sx v in constr:((v, x)) (*value,share,variable*)
  | _ :: ?lx' => listMatchReturn lx' sx h
  end.

Ltac listMatchReturnVariable lx h :=
  match lx with
  | nil => h
  | temp h (Vint (Int.repr ?v)) :: _ => v
  | temp h (Vbyte ?v) :: _ => v
  | temp h ?v :: _ => v
  | _ :: ?lx' => listMatchReturnVariable lx' h
  end.  

Ltac returnMatchOperand o lx :=
  match o with
  | (Econst_int (Int.repr ?h) tint) => h 
  | (Etempvar ?p _) => listMatchReturnVariable lx p
  end.
  
Ltac listTravIdtac l lx sx :=
  match l with
  | nil => constr:((tt))
  | (Etempvar ?p _) :: ?l' => let x := (listMatchReturn lx sx p) in (let x' := listTravIdtac l' lx sx in 
                                                                       match x with 
                                                                       | (?v,tt) => constr:((v,x'))
                                                                       | (?v,(?a,tt)) => constr:((v,(a,x')))
                                                                       | (?v,(?sh,?a)) => constr:((v,(sh,(a,x'))))
                                                                       end)
  | (Econst_int (Int.repr ?h) tint) :: ?l' => let x := listTravIdtac l' lx sx in constr:((h,x))
  | (Ebinop Oadd ?o1 ?o2 _) :: ?l' =>  let x := listTravIdtac l' lx sx in (let ro1 := returnMatchOperand o1 lx in 
                                       (let ro2 := returnMatchOperand o2 lx in constr:((ro1 + ro2,x))))
  | (Ebinop Osub ?o1 ?o2 _) :: ?l' =>  let x := listTravIdtac l' lx sx in (let ro1 := returnMatchOperand o1 lx in 
                                       (let ro2 := returnMatchOperand o2 lx in constr:((ro1 - ro2,x))))                                     
  | ?h :: ?l' => let x := listTravIdtac l' lx sx in constr:((h,x))
  end.  
  
Ltac forwardCallExplicit tup := 
  match tup with
  | (?a',tt) => forward_call(a')
  | (?a',(?b',tt)) => forward_call(a',b')
  | (?a',(?b',(?c',tt))) => forward_call(a',b',c')
  | (?a',(?b',(?c',(?d',tt)))) => forward_call(a',b',c',d')
  | (?a',(?b',(?c',(?d',(?e',tt))))) => forward_call(a',b',c',d',e')
  | (?a', (?b', (?c', (?d', (?e', (?f', tt)))))) => forward_call(a',b',c',d',e',f')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',tt))))))) => forward_call(a',b',c',d',e',f',g')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',(?h',tt)))))))) => forward_call(a',b',c',d',e',f',g',h')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',(?h',(?i',tt))))))))) => forward_call(a',b',c',d',e',f',g',h',i')
  | (?a', (?b', (?c', (?d', (?e', (?f', (?g',(?h',(?i',(?j',tt)))))))))) => forward_call(a',b',c',d',e',f',g',h',i',j')
  end.

 Ltac fireFailForward :=
  match goal with
  | |- ?g => failForward g
  end. 

Ltac checkPresenceConclusion H :=
  repeat match goal with
  | [ H' : ?a <-> ?b |- H ] => progress (tryif (unify H b) then apply H' 
                               else (tryif (unify H a) then apply H' else idtac ))
  | [ H' : ?a -> ?b |- H ] => progress (tryif (unify H b) then apply H' else idtac )
  end.

Ltac applyPresentHypothesis H h g :=
  repeat match goal with
  | [ H' : ?a <-> ?b |- g ] => progress (tryif (unify h b) then apply H' in H; clear H'
                               else (tryif (unify h a) then apply H' in H; clear H' else idtac))
  | [ H' : ?a -> ?b |- g ] => progress (tryif (unify h a) then apply H' in H; clear H' else idtac )
  end.

Ltac is_hypothesis_present H g :=
  match goal with
  | [ H' : ?h |- g ] => tryif (unify H H') then applyPresentHypothesis H' h g else idtac
  | [H' : _ |- _] => idtac
  end.

Ltac conjunctHypothesis :=
  match goal with
  | [ H' : _ /\ _ <-> _ |- _ ] => idtac 
  | [ H' : _ <-> _ /\ _ |- _ ] => idtac 
  | [ H' : Forall _ (_ :: _) |- _] => apply Forall_cons_iff in H'; destruct H' as [? ?]; conjunctHypothesis
  | [ H' : Forall2 _ (_ :: _) (_ :: _) |- _] => apply Forall2_cons_iff in H'; destruct H' as [? ?]; conjunctHypothesis
  | [ H' : _ /\ _ |- _ ] => destruct H' as [? ?]; conjunctHypothesis
  | [H' :  _ |- _] => idtac "No conjunctions present"
  end.

Ltac disjunctHypothesis :=
  repeat match goal with
  | [ H' : _ \/ _ |- _ ] => destruct H' as [? | ?]
  | _ => idtac "No further disjunctions present"
  end.

Ltac disjunctHypothesisFname H' :=
  repeat match goal with
  | [ H : _ \/ _ |- _ ] => progress (tryif (unify H H') then destruct H as [H | H] else idtac ) 
  end.

Ltac fireAppropriateMatch H :=
  match goal with
  | |- ?g => first[progress (checkPresenceConclusion g) |  try move H at bottom; is_hypothesis_present H g]
  end.

Ltac fireAppropriateConclusion := (*used for others*)
  match goal with 
  | |- ?g => checkPresenceConclusion g
  end.

Ltac fireAppropriateHypothesis H := (*used for lists*)
  match goal with 
  | |- ?g => try move H at bottom; is_hypothesis_present H g
  end.  

Ltac checkPresenceForall H' :=
  match goal with
  | [H : Forall2 _ (sublist ?lo1 ?hi1 ?l1) (sublist ?lo2 ?hi2 ?l2) |- ?g] => tryif (unify H H') then  
                                                                                match g with 
                                                                                | Forall2 _ (sublist ?lo1' hi1 l1) (sublist ?lo2' hi2 l2) => 
                                                                                  tryif (assert (lo1 = lo1' + 1 /\ lo2 = lo2' + 1) by lia) then clearMatch (lo1 = lo1' + 1 /\ lo2 = lo2' + 1);
                                                                                  rewrite sublist_split with lo1' (lo1' + 1) hi1 l1 by list_solve; rewrite sublist_split with lo2' (lo2' + 1) hi2 l2 by list_solve; 
                                                                                  apply Forall2_app; try rewrite !sublist_one by list_solve
                                                                                  else (tryif (assert (lo1 + 1 = lo1' /\ lo2 + 1 = lo2') by lia) then clearMatch (lo1 + 1 = lo1' /\ lo2 + 1 = lo2'); 
                                                                                  rewrite sublist_split with lo1 (lo1 + 1) hi1 l1 in H by list_solve; rewrite sublist_split with lo2 (lo2 + 1) hi2 l2 in H by list_solve; apply Forall2_app_inv in H; 
                                                                                  try (destruct H as [Hf1 Hf2]; rewrite !sublist_one in Hf1 by list_solve; apply Forall2_cons_iff in Hf1; destruct Hf1 as [? ?])
                                                                                  else (tryif (assert (lo1' > lo1 /\ lo2' > lo2) by lia) then clearMatch (lo1' > lo1 /\ lo2' > lo2); 
                                                                                  rewrite sublist_split with lo1 lo1' hi1 l1 in H by list_solve;  
                                                                                  rewrite sublist_split with lo2 lo2' hi2 l2 in H by list_solve; apply Forall2_app_inv in H; (*splits*)
                                                                                  try (destruct H as [? ?]) 
                                                                                  else (tryif (assert (lo1' < lo1 /\ lo2' < lo2) by lia) then clearMatch (lo1' < lo1 /\ lo2' < lo2);
                                                                                  rewrite sublist_split with lo1' lo1 hi1 l1 by list_solve; rewrite sublist_split with lo2' lo2 hi2 l2 by list_solve; 
                                                                                  apply Forall2_app else idtac )))
                                                                                end else idtac "Not unified"                                                         
  | [H : In _ (sublist ?lo ?hi ?l) |- ?g] => tryif (unify H H') then  
                                             match g with 
                                             | In _ (sublist ?lo' hi l) => tryif (assert (lo = lo' + 1) by lia) then clearMatch (lo = lo' + 1);
                                               rewrite sublist_split with lo' (lo' + 1) hi l by list_solve; 
                                               rewrite !sublist_len_1 by list_solve; simpl
                                               else (tryif (assert (lo + 1 = lo') by lia) then clearMatch (lo + 1 = lo');
                                               rewrite sublist_split with lo (lo + 1) hi l in H by list_solve;
                                               rewrite !sublist_len_1 in H by list_solve; simpl in H; destruct H
                                               else (tryif (assert (lo' > lo) by lia) then clearMatch (lo' > lo); 
                                               rewrite sublist_split with lo lo' hi l in H by list_solve;  apply in_app_iff in H (*disjunction*)
                                               else (tryif (assert (lo > lo') by lia) then clearMatch (lo > lo'); 
                                               rewrite sublist_split with lo' lo hi l by list_solve; apply in_app_iff else idtac)))(*disjuction*)
                                             end else idtac "Not unified"

  | [H : Forall _ (sublist ?lo ?hi ?l) |- ?g] => tryif (unify H H') then 
                                                 match g with 
                                                 | Forall _ (sublist ?lo' hi l) => tryif (assert (lo = lo' + 1) by lia) then clearMatch (lo = lo' + 1);
                                                   rewrite sublist_split with lo' (lo' + 1) hi l by list_solve; apply Forall_app; 
                                                   split; try rewrite !sublist_one by list_solve
                                                   else (tryif (assert (lo' = lo + 1) by lia) then clearMatch (lo' = lo + 1); 
                                                   rewrite sublist_split with lo (lo + 1) hi l in H by list_solve; apply Forall_app in H; 
                                                   destruct H as [Hf11 Hf12]; rewrite !sublist_one in Hf11 by list_solve; 
                                                   apply Forall_cons_iff in Hf11; destruct Hf11 as [? ?]
                                                   else (tryif (assert (lo' > lo) by lia) then clearMatch (lo' > lo); 
                                                   rewrite sublist_split with lo lo' hi l in H by list_solve; apply Forall_app in H; destruct H as [? ?](*splits - conjunction*)
                                                   else (tryif (assert (lo > lo') by lia) then clearMatch (lo > lo'); 
                                                   rewrite sublist_split with lo' lo hi l by list_solve; apply Forall_app; split else idtac)))
                                                 end else idtac "Not unified"
  
  | [ H : _ |- _ ] => idtac "Not matched with any of the above"
  end.

Ltac substituteIndValue val := 
  match goal with
  | [H : _ = val |- _ ] => rewrite <- H
  | [H : val = _ |- _ ] => rewrite H
  | [H : _ |- _] => idtac "No rewrite equality found for In" 
  end.
  
Ltac fireHypothesisOnSublist fname := 
  match goal with 
  | |- ?g => match g with 
             | context[sublist ?lo ?hi _] => tryif (assert (hi = lo) by lia) then clearMatch (hi = lo); rewrite !sublist_nil' by list_solve 
                                             else (tryif (assert (hi = lo + 1) by lia) then clearMatch (hi = lo + 1); rewrite !sublist_one by list_solve 
                                             else checkPresenceForall fname; try solve[list_solve])
             | _ =>  checkPresenceForall fname; try solve[list_solve]                                                                           
            end
  end.

Ltac matchMin g :=
  match g with
  | Z.min ?aa ?bb => match bb with 
                      | Z.min _ _ => matchMin bb
                      | _ =>  tryif (assert (aa <= bb) by first[rep_lia | list_solve]) then rewrite Z.min_l by lia; clearMatch (aa <= bb) 
                              else (tryif (assert (bb <= aa) by first[rep_lia | list_solve]) then rewrite Z.min_r by lia; clearMatch (bb <= aa) 
                              else destruct (aa <=? bb); [ assert (aa <= bb) by lia; rewrite Z.min_l by lia | 
                              assert (bb <= aa) by lia; rewrite Z.min_r by lia]) 
                      end
  end.
  
Ltac fireMinTactic := 
  match goal with 
  | |- ?g => match g with 
             | context [Z.min ?aa ?bb] => matchMin (Z.min aa bb)
            end
  end.

Ltac forwardCallExplicitList := 
  try rewrite !add_repr; try rewrite !sub_repr; try rewrite !mul_repr; 
  try rewrite !upd_Znth_map; 
  match goal with 
  | |- semax _ (PROPx ?px' (LOCALx ?lx' (SEPx ?sx'))) (Scall _ (Evar ?n' _) ?l') _ => let x := listTravIdtac l' lx' sx' in forwardCallExplicit x
  | |- semax _ (PROPx ?px' (LOCALx ?lx' (SEPx ?sx'))) (Ssequence (Scall _ (Evar ?n' _) ?l') _) _ => let x := listTravIdtac l' lx' sx' in forwardCallExplicit x
  end.


Ltac forwardFollowMalloc l :=  let x := doForwardCall l in  
  match x with 
   | false =>  idtac
   | _ =>  match goal with 
           | |- ?t => match t with 
                      | semax _ (EX v : _, _ _ _) _ _ =>  let fv := fresh v in (Intros fv; assignandRewrite x fv;
                               rewrite memory_block_data_at_ by auto)
                      | context[memory_block _ ?v _] => assert (sizeof x = v) as Hszassert by reflexivity; rewrite <- Hszassert; entailer!; 
                               rewrite memory_block_data_at_ by auto; entailer!
                      | _ => idtac
                      end
           end
  end.

Ltac simplifyLists := 
  match goal with 
  | |- context [ Zlength []] => rewrite Zlength_nil; simplifyLists
  | |- context [ Zlength (_ :: _)] => rewrite Zlength_cons; simplifyLists
  | |- context [sublist _ _ []] => rewrite sublist_of_nil; simplifyLists 
  | |- ?g => idtac "reached but not matched: "g
  end.

  
Ltac tryInstantiateExistsValue Qr := 
  match Qr with
  | context [ !! (?v = ?a)] => idtac 
  | context [ !! (_ = ?a)] => Exists a; first[progress entailer! | entailer!!]
  | context [ !! (?v = _)] => Exists v; first[progress entailer! | entailer!!]  
  end.

Ltac freeLocalParameterInference lx h := 
  match lx with
  | nil => false
  | temp h ?v :: _ => v
  | _ :: ?lx' =>  freeLocalParameterInference lx' h 
  end.
  
Ltac freeForwardCall lx l :=
  match l with 
  | Etempvar ?h (tptr ?sof) :: nil => let x := freeLocalParameterInference lx h in forward_call(x, sizeof sof)
  end. 

Ltac simplifyEntailment P Q :=  
  match Q with
  | context [EX _: _, _]  => first[ 
                              progress (
                                match Q with 
                                | context [data_at ?sh _ (Vint (Int.repr ?k), (?v, (?lt, ?lr))) ?r] => first[progress entailer! | entailer!!] 
                                | context [data_at ?sh _ (Vint (Int.repr ?k), (?v, (_, _))) ?r] =>
                                  match P with 
                                  | context [data_at sh _ (Vint (Int.repr k), (v, (?lt', ?lr'))) r] => Exists lt' lr'; entailer!! 
                                  | context [data_at sh _ (Vint (Int.repr ?k0), (v, (?lt', ?lr'))) r] => tryif (assert (k = k0) by lia) then subst; Exists lt' lr'; entailer!! else idtac
                                  end
                                | context [data_at ?sh _ (Vint (Int.repr ?k), ?padd) ?r] => first [progress entailer! | entailer!!] 
                                | context [data_at ?sh _ (Vint (Int.repr ?k), _) ?r] => 
                                  match P with 
                                  | context [data_at sh _ (Vint (Int.repr k), ?padd') r] => Exists padd'; entailer!! 
                                  | context [data_at sh _ (Vint (Int.repr ?k0), ?padd') r] => tryif (assert (k = k0) by lia) then subst; Exists padd'; entailer!! else idtac
                                  end
                                | context [data_at ?sh _ ?padd ?padd2] => first [progress entailer! | entailer!!] 
                                | context [data_at ?sh _ _ ?padd2] => 
                                  match P with 
                                  | context [data_at sh _ ?padd' padd2] => Exists padd'; entailer!! 
                                  end
                               end) | tryInstantiateExistsValue Q]
  | context [ !! ?f ] => first[progress entailer! | entailer!!] 
  | context G [tree_rep (T ?a ?b ?c ?d) ?r] =>
                              let x := eval unfold tree_rep in (tree_rep (T a b c d) r) in 
                              let x := eval fold tree_rep in x in
                              let y := context G[x] in change y
  | context [tree_rep (?f ?t') ?r] => simpl
  | context G [sllbox_rep ?l' ?r] =>
            let x := eval simpl in (sllbox_rep l' r) in
            let x' := eval unfold sllbox_rep in x in 
            let x' := eval fold sllbox_rep in x' in
            let y := context G[x'] in change y
  | context G [listrep (?v :: ?l') ?r] =>
            let x := eval unfold listrep in (listrep (v :: l') r) in 
            let x := eval fold listrep in x in
            let y := context G[x] in change y
  | context [listrep (?f ?l') ?r] => simpl
  | _ =>  first [progress entailer! | progress entailer!! | simpl]
  end.   

Ltac progltac g' fname freefuncName :=
  match goal with
  | |- ?g => match g' with 
             | g => tryif (progress (disjunctHypothesisFname fname)) then progltac false fname freefuncName
                    else ( tryif (progress fireMinTactic) then progltac false fname freefuncName
                    else idtac "Aborting, same goal: "g" and: "g')
             | _ => try (triggerNullNoNullMatch g); try triggerNullList; try (disjunctHypothesisFname fname); try matchTreeAndSubstitute; try matchListAndSubstitute;
                    try contradiction; fireFailForward; conjunctHypothesis; rewriteWrapperInGoal; 
  match g with 
  | semax _ _ (Ssequence (Ssequence _ _) _)  _ => apply seq_assoc1; progltac g fname freefuncName
  | semax _ _ (Sloop _)  _ => fail "Error - loops not supported"
  | semax _ _ (Ssequence (Sloop _) _)  _ => fail "Error - loops not supported"
  | semax _ (EX v : _, _ _ _) _ _ =>  let fv := fresh v in (Intros fv; progltac g fname freefuncName)
  | semax _ _ (Sifthenelse _ _ _)  _ => forward_if; progltac g fname freefuncName
  | semax _ _ (Ssequence (Sifthenelse _ _ _) _)  _ => apply semax_if_seq; progltac g fname freefuncName
  | semax _ (PROPx ?px (LOCALx ?lx (SEPx ?sx))) (Ssequence (Scall _ (Evar ?n _) ?l) _)  _ => match n with 
                                                                                             | freefuncName => first[freeForwardCall lx l; try (entailer!; rewrite memory_block_data_at_ by auto; entailer!); progltac g fname freefuncName  | idtac "Unable to infer forward call witness for free"]
                                                                                             | _ => first[ first[forward_call | forwardCallExplicitList]; try (forwardFollowMalloc l); progltac g fname freefuncName |  idtac "Error - Failed to infer forward call witness - Please provide them"]
                                                                                             end
  | semax _ (PROPx ?px (LOCALx ?lx (SEPx ?sx))) (Scall _ (Evar ?n _) ?l) _ =>  match n with        
                                                                               | freefuncName => first[freeForwardCall lx l; try(entailer!; rewrite memory_block_data_at_ by auto; entailer!); progltac g fname freefuncName  | idtac "Unable to infer forward call witness for free"]
                                                                               | _ => first[ first[forward_call | forwardCallExplicitList]; try (forwardFollowMalloc l); progltac g fname freefuncName |  idtac "Error - Failed to infer forward call witness - Please provide them"]
                                                                               end 
  |semax _ _ ?c  _ =>  first [progress (try_forward (1000)%nat); progltac g fname freefuncName |  idtac "Error - Can't move forward here"]
  | context[if ?Op ?o1 ?o2 then _ else _ ] => match o1 with
                                              | Z.modulo ?o1' ?o2' => matchModulo o1' o2' Op o2 g; progltac g fname freefuncName
                                              | _ => checkOperatorDischarge2 Op o1 o2 g; progltac g fname freefuncName
                                              end
  | ENTAIL _, _ |-- _ => first[progress entailer! | entailer!!]; progltac g fname freefuncName 
  | EX v : _, _ |-- _ => let fv := fresh v in (Intros fv; progltac g fname freefuncName)
  | _ |-- EX a : bool, !! (_ /\ Vint Int.one = bool2val a) && _ => Exists true; first[progress entailer! | entailer!!]; progltac g fname freefuncName
  | _ |-- EX a : bool, !! (_ /\ Vint Int.zero = bool2val a) && _ => Exists false; first[progress entailer! | entailer!!]; progltac g fname freefuncName
  | _ |-- EX a : bool, !! (_ /\ force_val (sem_cast_i2bool (bool2val ?v)) = bool2val a) && _ => Exists v; first[progress entailer! | entailer!!]; progltac g fname freefuncName
  | _ |-- EX a : Z, !! (_ /\ Vint (Int.repr ?val) = Vint (Int.repr a)) && _ => Exists val; first[progress entailer! | entailer!!]; progltac g fname freefuncName
  | data_at _ _ _ _ |-- data_at _ _ _ _ => list_solve; progltac g fname freefuncName
  | ?t |-- emp =>  simpl; entailer!!; progltac g fname freefuncName
  | emp |-- ?t =>  match t with 
                   | context [EX _: _, _] => Exists nullval; simpl; entailer!!; progltac g fname freefuncName
                   | _ =>  simpl; entailer!!; progltac g fname freefuncName
                  end
  | ?Pr |-- ?Qr =>  simplifyEntailment Pr Qr; progltac g fname freefuncName 
  | Forall _ (_ :: _) => simplifyLists; apply Forall_cons_iff; split; progltac g fname freefuncName
  | Forall (map (_)) _ =>  simplifyLists; tryif solve[list_solve ] then idtac else apply Forall_map; progltac g fname freefuncName
  | Forall _ ?l => simplifyLists; tryif solve[list_solve] then idtac else first[progress (fireHypothesisOnSublist fname) | fireAppropriateHypothesis fname; fireHypothesisOnSublist fname]; progltac g fname freefuncName
  | Forall2 _ (_ :: _) (_ :: _) =>  apply Forall2_cons_iff; split; progltac g fname freefuncName
  | Forall2 _ _ _ => simplifyLists; tryif solve[list_solve] then idtac else first[progress (fireHypothesisOnSublist fname) | fireAppropriateHypothesis fname; fireHypothesisOnSublist fname]; progltac g fname freefuncName
  | In (Znth ?i _) (sublist ?j _ _) => simplifyLists; tryif (assert (j >= i) by lia) then clearMatch (j >= i); apply In_Znth_iff; exists (j - i); progltac g fname freefuncName else idtac "Cannot resolve idtac goal"
  | In ?v (_ :: _) => simplifyLists; substituteIndValue v; simpl; tryif solve[list_solve] then idtac else progltac g fname freefuncName
  | In ?v _ => simplifyLists; substituteIndValue v; tryif solve[list_solve] then idtac else first[progress (fireHypothesisOnSublist fname) | fireAppropriateHypothesis fname; fireHypothesisOnSublist fname]; progltac g fname freefuncName
  | repable_signed ?a => tryif solve[first[list_solve | rep_lia]] then idtac else idtac "Error - Cannot resolve type"
  | context[Int.signed (Int.repr _)] => rewrite !Int.signed_repr; try first[ rep_lia | list_solve]; progltac g fname freefuncName
  | context[Int.unsigned (Int.repr _)] => rewrite !Int.unsigned_repr; try first[rep_lia | list_solve]; progltac g fname freefuncName 
  | context [Znth _ (?a _)] => unfold a; tryif solve[list_solve] then idtac else progltac g fname freefuncName
  | context [Zlength (?a _)] => unfold a; tryif solve[list_solve] then idtac else progltac g fname freefuncName
  | context [Znth _ (map _ _)] => tryif solve[list_solve] then idtac else rewrite !Znth_map; progltac g fname freefuncName
  | context [Znth _ (sublist _ _ _)] => tryif solve[list_solve] then idtac else rewrite !Znth_sublist by list_solve; progltac g fname freefuncName
  | context [Zlength (map _ _)] => tryif solve[list_solve] then idtac else rewrite !Zlength_map; progltac g fname freefuncName
  | context [Zlength (upd_Znth _ _ _)] => tryif solve[list_solve] then idtac else rewrite !Zlength_upd_Znth; progltac g fname freefuncName
  | context [upd_Znth _ (map _ _) _] => rewrite !upd_Znth_map; progltac g fname freefuncName
  | context [Zlength (_ ++ _)] => tryif solve[list_solve] then idtac else rewrite !Zlength_app; progltac g fname freefuncName
  | context [Zlength (sublist _ _ _)] => tryif solve[list_solve] then idtac else rewrite !Zlength_sublist by list_solve; progltac g fname freefuncName
  | _ <-> _ => split; intros Hform; simpl in Hform; progltac g Hform freefuncName 
  | _ -> _ => intros Hform; simpl in Hform; progltac g Hform freefuncName
  | _ /\ _ => split; progltac g fname freefuncName
  | ?l \/ ?r => tryif solve[unifyLeft l g | unifyRight r g ] then idtac
                  else (tryif progress (disjunctHypothesisFname fname) then 
                  solve[left; progltac g fname freefuncName | right; progltac g fname freefuncName | idtac "Assistance needed to resolve disjunction"]
                  else solve[left; progltac g fname freefuncName | right; progltac g fname freefuncName | fireAppropriateConclusion; progltac g fname freefuncName])
  | force_val (sem_cast_i2bool (bool2val ?v)) = bool2val ?v' => match v with 
                                                                | v' => apply forceval_cast  
                                                                | _ => simpl; progltac g fname freefuncName
                                                                end
  | context [bool2val ?v] => solve[reflexivity | destruct v; simpl; reflexivity]
  | Datatypes.length _ = Datatypes.length _ => apply invariants.Zlength_eq; list_solve
  | _ = _ =>  tryif solve [simpl; reflexivity | rep_lia | list_solve ] then idtac else (tryif progress (fireAppropriateConclusion) then progltac g fname freefuncName
                  else simpl; progltac g fname freefuncName)
  | _ <= _ < _ => tryif solve [rep_lia | list_solve] then idtac else idtac "Error - Unable to resolve _ <= _ < _. User assistance needed."
  | _ <= _ <= _ => tryif solve [rep_lia | list_solve] then idtac else idtac "Error - Unable to resolve _ <= _ <= _. User assistance needed."
  | _ < _ => tryif solve [rep_lia | list_solve] then idtac else idtac "Error - Unable to resolve _ < _. User assistance needed." 
  | _ <= _ => tryif solve [rep_lia | list_solve] then idtac else idtac "Error - Unable to resolve _ <= _. User assistance needed." 
  | _ > _ => apply Z.lt_gt; tryif solve [rep_lia | list_solve ] then idtac else idtac "Error - Unable to resolve _ > _. User assistance needed."
  | _ >= _ => apply Z.le_ge; tryif solve [rep_lia | list_solve] then idtac else idtac "Error - Unable to resolve _ >= _. User assistance needed." 
  | False =>  idtac "Error - Unable to resolve goal - False. User assistance needed."
  | _ => tryif solve[rep_lia | list_solve] then idtac else idtac "Error - Can't resolve present goal. User assistance needed: "g
  end
  end
  end. 
