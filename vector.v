


Module Vec1.

Require Import List Nat JMeq FunctionalExtensionality ProofIrrelevance.

Fixpoint len {A: Type} (l: list A): nat :=
  match l with
    | nil   => O
    | x::xs => S (len xs)
  end.

Fixpoint plus (n m: nat): nat :=
  match n with
    | O   => m
    | S k => S (plus k m)
  end.

Lemma plus_assoc: forall a b c, plus a (plus b c) = plus (plus a b) c.
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl. rewrite IHa. easy.
Defined.

Class vector {A: Type} (n: nat) :=
  mk_vector
  {
    ul: list A;
    uc: len ul = n
  }.

Arguments mk_vector {_} _ _ _.

Fixpoint appendL {A: Type} (l1 l2: list A): list A :=
  match l1 with
    | nil   => l2
    | x::xs => x :: appendL xs l2
  end.

Lemma appL_assoc: forall {A: Type} (l1 l2 l3: list A), appendL l1 (appendL l2 l3) = appendL (appendL l1 l2) l3.
Proof. intros A l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. rewrite IHl1. easy.
Defined.

Lemma app_len: forall {A: Type} (l1 l2: list A), len (appendL l1 l2) = plus (len l1) (len l2).
Proof. intros A l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. rewrite IHl1. easy.
Defined.

Lemma vector_eq: forall {A: Type} {n m: nat} (v1: @vector A n) (v2: @vector A m) (eq: n = m),
  @ul A n v1 = @ul A m v2 -> 
  v2 = 
  match eq in _ = V return @vector A V with
    | eq_refl => v1
  end.
Proof. intros.
       destruct v1 as (l1, p1).
       destruct v2 as (l2, p2).
       subst.
       simpl.
       revert H.
       destruct l1; intros.
       simpl in eq.
       destruct l2. simpl in eq.
       assert (eq = eq_refl).
       { specialize (UIP_refl _ _ eq); intro Ha. easy. }
       rewrite H0. easy.
       simpl in *. easy.
       simpl in *.
       subst.
       simpl in eq.
       assert (eq = eq_refl).
       { specialize (UIP_refl _ _ eq); intro Ha. easy. }
       rewrite H. simpl. easy.
Qed.

Lemma vector_jmeq: forall {A: Type} {n m: nat} (v1: @vector A n) (v2: @vector A m) (eq: n = m),
  @ul A n v1 = @ul A m v2 -> 
  JMeq v1 v2.
Proof. intros.
       destruct v1 as (l1, p1).
       destruct v2 as (l2, p2).
       subst.
       apply eq_dep_id_JMeq, EqdepFacts.eq_sigT_iff_eq_dep, eq_existT_uncurried.
       simpl in *.
       unfold eq_rect.
       
       subst.
       exists eq_refl.
       easy.
Qed.

Definition appendV {A: Type} {n m} (v1: @vector A n) (v2: @vector A m): @vector A (plus n m).
Proof.
  refine(
    match (v1, v2) with
      | (mk_vector _ l1 p1, mk_vector _ l2 p2) => mk_vector (plus n m) (appendL l1 l2) _
   end).
  rewrite app_len, p1, p2. easy.
Defined.

Lemma app_assoc:
  forall n m u A (v1: @vector A n) (v2: @vector A m) (v3: @vector A u),
   (appendV (appendV v1 v2) v3) =  
   (match plus_assoc n m u in _ = V return @vector A V with
     | eq_refl => (appendV v1 (appendV v2 v3))
    end).
Proof. intros.
       apply vector_eq.
       induction v1; intros.
       induction v2; intros.
       induction v3; intros.
       subst.
       induction ul0; intros.
       - simpl. easy.
       - simpl in *. rewrite IHul0. easy.
Qed.

Lemma app_assoc_jm:
  forall n m u A (v1: @vector A n) (v2: @vector A m) (v3: @vector A u),
  JMeq (appendV (appendV v1 v2) v3) (appendV v1 (appendV v2 v3)).
Proof. intros.
       apply vector_jmeq.
       rewrite plus_assoc. easy.
       induction v1; intros.
       induction v2; intros.
       induction v3; intros. subst.
       simpl.
       rewrite appL_assoc.
       easy.
Qed.

Lemma jmeq_eq: forall n m u A (v1: @vector A n) (v2: @vector A m) (v3: @vector A u),
  (appendV (appendV v1 v2) v3) =  
   (match plus_assoc n m u in _ = V return @vector A V with
     | eq_refl => (appendV v1 (appendV v2 v3))
    end).
Proof. intros.
       induction v1; intros.
       induction v2; intros.
       induction v3; intros. subst.
       apply JMeq_eq. simpl. cbn.
       apply vector_jmeq. easy.
       cbn.
       unfold ul.
       induction ul0; intros.
       simpl. easy.
       simpl. rewrite IHul0.
       destruct (plus_assoc (len ul0) (len ul1) (len ul2)).
       simpl.
       easy.
Qed.

End Vec1.

Module Vec2.

Require Import Coq.Vectors.VectorDef.

Lemma plus_assoc: forall a b c, a + (b + c) = (a + b) + c.
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl. rewrite IHa. easy.
Defined.

Lemma app_assoc:
  forall n m u A (v1: t A n) (v2: t A m) (v3: t A u),
   (append (append v1 v2) v3) =
   (match plus_assoc n m u in _ = V return t A V with
     | eq_refl => (append v1 (append v2 v3))
   end).
Proof. intros.
       induction v1; intros.
       - simpl. easy.
       - simpl. rewrite IHv1.
         clear IHv1. unfold eq_ind_r, eq_ind, eq_sym.
         destruct (plus_assoc n m u). easy.
Qed.

End Vec2.



