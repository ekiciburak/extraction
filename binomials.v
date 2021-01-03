Require Import Lia Factorial QArith.

Definition binom (n k: nat): Q :=
  if Nat.leb k n then Z.of_nat (fact n) # Pos.of_nat (fact k * fact (n - k)) else 0.

Lemma Zeq: forall n, Nat.eqb n 0 = false ->  Z.pos (Pos.of_nat n) = Z.of_nat n.
Proof. intro n.
       induction n; intros.
       - rewrite Nat.eqb_refl in H. contradict H; easy.
       - simpl. case_eq n; intros.
         + simpl. easy.
         + simpl. f_equal. apply f_equal. 
           subst. simpl in IHn.
           specialize (IHn eq_refl).
           inversion IHn. easy.
Qed.

Lemma mult_nz: forall n m: nat, (n * m <> 0 <-> n <> 0 /\ m <> 0)%nat.
Proof. split.
       - intro Hneq.
         unfold not in *; split;
         intros;
         apply Hneq; rewrite H; easy.
       - intros (Hn, Hm). lia.
Qed.

Lemma plus_z: forall n m: nat, (n + m = 0 <-> n = 0 /\ m = 0)%nat.
Proof. split.
       - intros. 
         case_eq n; intros.
         + split.
           ++ easy.
           ++ rewrite H0 in H. simpl in H. easy.
         + rewrite H0 in H. simpl in H. easy.
       - intros (Hn, Hm). rewrite Hn, Hm. easy.
Qed.



Lemma plus_nz: forall n m: nat, (n + m <> 0 <-> n <> 0 \/ m <> 0)%nat.
Proof. split.
       - case_eq n; intros.
         + simpl. now right.
         + simpl. now left.
       - intros.
         destruct H as [ H | H].
         unfold not in *. intro Hdq.
         apply H. apply plus_z in Hdq.
         easy.
         unfold not in *. intro Hdq.
         apply H. apply plus_z in Hdq.
         easy.
Qed.

Lemma fact_nk: forall n k, (S k <=? n) = true -> ((n - k) * fact (n - S k))%nat = fact (n - k).
Proof. intro n.
       induction n; intros.
       - simpl in H. easy.
       - simpl. case_eq k; intros.
         + simpl. rewrite !Nat.sub_0_r. easy.
         + simpl. 
           specialize (IHn n0).
           apply IHn.
           apply Nat.leb_le.
           apply Nat.leb_le in H. lia.
Qed.

Lemma qnum: forall n m: nat, Qnum (Z.of_nat n # Pos.of_nat m) =  Z.of_nat n.
Proof. intros n m.
       simpl.
       reflexivity.
Qed.


Lemma qden: forall n m: nat, QDen (Z.of_nat n # Pos.of_nat m) = Z.pos (Pos.of_nat m).
Proof. intros n m.
       simpl.
       reflexivity.
Qed.

Lemma binomS: forall n k: nat, binom (S n) (S k) == binom n k + binom n (S k).
Proof. intros n k.
       unfold binom.
       case_eq (k <=? n); intros.
       - case_eq (S k <=? n); intros Ha.
         + assert (Hb: (S k <=? S n) = true).
           { apply Nat.leb_le in H.
             apply Nat.leb_le. lia. }
           rewrite Hb.
           assert (Hc: (Z.of_nat (fact (S n)) = (Z.of_nat ((fact n) * (k+1) + (fact n) * (n-k))))%Z).
           { f_equal. 
             specialize (Nat.mul_add_distr_l (fact n) (k + 1) (n - k)); intros.
             rewrite <- H0.
             rewrite plus_assoc_reverse.
             rewrite plus_comm.
             rewrite plus_assoc_reverse.
             rewrite Nat.sub_add.
             assert (1 + n = S n)%nat.
             { lia. }
             rewrite H1. simpl. lia.
             apply Nat.leb_le in H. lia.
           } rewrite Hc. 
           specialize (Qinv_plus_distr (Z.of_nat (S k * fact n)) 
                                       (Z.of_nat ((n - k) * fact n)) 
                                       (Pos.of_nat (fact (S k) * fact (n - k)))); intros Hd.
           rewrite <- !Nat2Z.inj_add in Hd.
           assert (He: ((S k * fact n + (n - k) * fact n) = (fact n * (k + 1) + fact n * (n - k)))%nat ).
           { lia. }
           rewrite <- He.
           rewrite <- Hd.
           assert (H1: (Z.of_nat (S k * fact n) # Pos.of_nat ((S k) * fact k * fact (n - k))) == 
                       (Z.of_nat (fact n) # Pos.of_nat (fact k * fact (n - k)))).
           { unfold Qeq.
             rewrite !qnum, !qden.
             rewrite !Zeq.
             ++ rewrite !Nat2Z.inj_mul. lia.
             ++ apply Nat.eqb_neq.
                specialize (mult_nz (S k) (fact k * fact (n - k))); intro Hm.
                rewrite mult_assoc_reverse.
                apply Hm.
                split.
                +++ lia.
                +++ specialize (mult_nz (fact k)  (fact (n - k))); intro Hn.
                    apply Hn.
                    split.
                    * apply fact_neq_0.
                    * apply fact_neq_0.
             ++ specialize (mult_nz (fact k)  (fact (n - k))); intro Hn.
                apply Nat.eqb_neq.
                apply Hn.
                split.
                +++ apply fact_neq_0.
                +++ apply fact_neq_0. }
           rewrite H1. 
           assert (H2: (Z.of_nat ((n - k) * fact n) # Pos.of_nat (S k * fact k * fact (n - k))) ==
                       (Z.of_nat (fact n) # Pos.of_nat (S k * fact k * fact (n - S k)))).
           {   unfold Qeq.
               rewrite !qnum, !qden.
               rewrite !Zeq.
               rewrite <- !Nat2Z.inj_mul.
               f_equal.
               assert (H2: ((n - k) * fact n * (S k * fact k * fact (n - S k)))%nat = 
                           (fact n * (S k * fact k * (n - k) * fact (n - S k)))%nat). lia.
               rewrite H2.
               assert (H3: ((n - k) * fact (n - S k) = fact (n - k))%nat).
               { apply fact_nk. easy. }
               rewrite <- H3. lia.
               apply Nat.eqb_neq.
               specialize (mult_nz (S k) (fact k * fact (n - k))); intro Hm.
               rewrite mult_assoc_reverse.
               apply Hm.
               split.
               +++ easy.
               +++ specialize (mult_nz (fact k) (fact (n - k))); intro Hn.
                   apply Hn.
                   split.
                   * apply fact_neq_0.
                   * apply fact_neq_0.
               +++ specialize (mult_nz (S k) (fact k * fact (n - S k))); intro Hm.
                   rewrite mult_assoc_reverse.
                   apply Nat.eqb_neq.
                   apply Hm.
                   split.
                   * lia.
                   * specialize (mult_nz (fact k) (fact (n - S k))); intro Hn.
                     apply Hn.
                     split.
                     ** apply fact_neq_0.
                     ** apply fact_neq_0. }
           rewrite H2. reflexivity.
         + assert (H1: n = k).
           { apply Nat.leb_nle in Ha. 
             apply Nat.leb_le in H.
             lia. } 
           rewrite H1 in *.
           rewrite Nat.leb_refl. 
           assert (H2: forall m, (m-m)%nat = 0%nat) by lia.
           rewrite !H2 in *.
           unfold Qeq.
           rewrite !mult_1_r.
           simpl.
           rewrite !Zeq.
           ++ rewrite Zmult_comm.
              f_equal. 
              rewrite <- Zeq. lia.
              apply Nat.eqb_neq.
              apply fact_neq_0.
           ++ apply Nat.eqb_neq.
              apply plus_nz. left.
              apply fact_neq_0. 
       - assert (H1: S k <=? S n = false).
          { apply Nat.leb_nle in H.
            apply Nat.leb_nle. lia. }
         rewrite H1.
         assert (H2: S k <=? n = false).
         { apply Nat.leb_nle in H.
           apply Nat.leb_nle in H1.
           apply Nat.leb_nle. lia. }
         rewrite H2. 
         reflexivity. 
Defined.


Lemma binomNat : forall n k: nat, { m:nat | Z.of_nat m # Pos.of_nat 1 == (binom n k) }.
Proof. intro n.
       induction n; intros.
       - case_eq k; intros.
         + simpl. exists 1%nat. simpl. reflexivity.
         + simpl. exists 0%nat. simpl. reflexivity.
       - simpl. 
         case_eq k; intros.
         + exists 1%nat.
           unfold binom. simpl. rewrite Nat.add_0_r.
           unfold Qeq. simpl. rewrite Zeq. lia.
           apply Nat.eqb_neq.
           apply plus_nz. left.
           apply fact_neq_0.
         + pose proof IHn as IHn'.
           specialize (IHn' (k-1)%nat).
           specialize (IHn k).
           destruct IHn as (u, IHu).
           destruct IHn' as (v, IHv).
           exists (v + u)%nat.
           specialize (Qinv_plus_distr (Z.of_nat v) (Z.of_nat u) (Pos.of_nat 1 )); intro Ha.
           rewrite <- Nat2Z.inj_add in Ha.
           rewrite <- Ha.
           rewrite IHu, IHv.
           rewrite binomS.
           rewrite H. simpl.
           rewrite <- minus_n_O.
           rewrite Qplus_comm.
           reflexivity.
Defined.

Require Import Extraction.
Extraction Language Haskell.
Recursive Extraction binomNat.

