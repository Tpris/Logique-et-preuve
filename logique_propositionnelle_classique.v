Require Import Setoid Classical.

(*  Logique classique
    On peut sauter les 2 commandes suivantes 
 *)

(* un peu de magie noire *)
Definition EXM :=   forall A:Prop, A \/ ~A.

Ltac add_exm  A :=
  let hname := fresh "exm" in
  assert(hname : A \/ ~A);[classical_right; assumption|].


Section LK.
  (* 
   Pour ajouter une instance du tiers-exclu de la forme  A \/ ~A 
   il suffit d'exécuter la tactique "add_exm A"
   *)

  Variables P Q R S T : Prop.

  Lemma double_neg : ~~ P -> P.
  Proof.
    intro H.
    add_exm  P. (* "je fais un tiers exclus sur P " *)
    destruct exm. (* Presque toujours, destruct suit add_exm *)
    - assumption.
    - assert (f:False).
      {
        apply H; assumption.
      }
      destruct f. (* ou: exfalso, etc. *)
   Qed.

  (* Variantes: tactiques classical_left et classical_right.
     Pour prouver A \/ B:
     - classical_left demande de prouver A, avec ~B comme hypothèse en plus.
     - classigal_right demande de prouver B, avec ~A comme hypothèse en plus.
  *)

  Lemma weak_exm: P \/ (P->Q).
  Proof.
  classical_right.
  intro p; exfalso; apply H; assumption.
  Qed.

  (* Exercice: completer toutes les preuves, en remplaçant les
     "Admitted" par des preuves terminées par "Qed."; et 
     sans utiliser ni auto, ni tauto.  *)

  Lemma de_morgan : ~ ( P /\ Q) <-> ~P \/ ~Q.
  Proof.
  split.
  - intro npeq.
    classical_right.
    intro q.
    apply npeq.
    split.
    + add_exm P.
      destruct exm as [p | np].
      * assumption.
      * exfalso.
        apply H; assumption.
    + assumption.
  - intros nponq peq.
    destruct peq as [p q].
    destruct nponq as [np | nq].
    + apply np; assumption.
    + apply nq; assumption.
  Qed.

  Lemma not_impl_and : ~(P -> Q) <-> P /\ ~ Q.
  Proof.
  split.
  - intro npq.
    add_exm P.
    destruct exm as [p | np].
    + split.
      * assumption.
      * intro q.
        apply npq. intro p2; assumption.
    + split.
      * exfalso.
        apply npq. intro p.
        exfalso.
        apply np; assumption.
      * intro q.
        apply npq. intro p;assumption.
  - intros penq pq.
    destruct penq as [p nq].
    apply nq.
    apply pq;assumption.
  Qed.

  Lemma contraposee: (P -> Q) <-> (~Q -> ~P).
  Proof.
split.
- intros pq nq p.
  apply nq.
  apply pq;assumption.
- intros nqnp p.
  add_exm Q.
  destruct exm as [q | nq].
  + assumption.
  + exfalso.
    apply nqnp;assumption. 
  Qed.

  Lemma exm_e : (P -> Q) -> (~P -> Q) -> Q.
  Proof.
intros pq npq.
add_exm P.
destruct exm as [p | np].
- apply pq;assumption.
- apply npq;assumption.
  Qed.

  Lemma exo_16 : (~ P -> P) -> P.
  Proof.
  intro npp.
  add_exm P.
  destruct exm as [p | np].
  - assumption.
  - apply npp; assumption.
  Qed.

  Lemma double_impl : (P -> Q) \/ (Q -> P).
  Proof.
classical_right.
intro q.
exfalso.
apply H.
intro p;assumption.
  Qed.

  Lemma imp_translation : (P -> Q) <-> ~P \/ Q.
  Proof.
split.
- intro pq.
  add_exm P.
  destruct exm as [p | np].
  + right. 
    apply pq;assumption.
  + left;assumption.
- intros npoq p.
  destruct npoq as [np | q].
  + exfalso.
    apply np;assumption.
  + assumption.
  Qed.

  Lemma Peirce : (( P -> Q) -> P) -> P.
  Proof.
intro pqp.
add_exm P.
destruct exm as [p | np].
- assumption.
- apply pqp;intro p.
  exfalso.
  apply np;assumption.
  Qed.

  (* Quelques exercices d'anciens tests *) 
  Lemma test_1: (P->Q)->(~P->R)->(R->Q)->Q.
  Proof.
intros pq npr rq.
add_exm P.
destruct exm as [p | np].
- apply pq; assumption.
- apply rq; apply npr; assumption.
  Qed.

  Lemma test__2: (P \/ (Q\/R))-> (~P) -> (~R) -> (P\/Q).
  Proof.
intros poqor np nr.
destruct poqor as [p | [q | r]].
- left;assumption.
- right;assumption.
- exfalso. apply nr;assumption.
  Qed.

  Lemma test_3: (~P-> Q/\R)->(Q->~R)->P.
  Proof.
intros npqer qnr.
add_exm P.
destruct exm as [p | np].
- assumption.
- exfalso.
  apply qnr.
  + apply npqer;assumption.
  + apply npqer;assumption.
  Qed.

  Lemma test_4: (~P->Q)->(~Q\/R)->(P->R)->R.
  Proof.
intros npq nqor pr.
add_exm P.
destruct exm as [p | np].
- apply pr; assumption.
- destruct nqor as [nq | r].
  * exfalso.
    apply nq; apply npq; assumption.
  * assumption.
  Qed.

  Lemma test_5: (P->Q)->(~P->~Q)->((P/\Q) \/ ~(P\/Q)).
  Proof.
intros pq npq.
classical_right; intro poq.
apply H.

destruct poq as [p | q].
- split.
  + assumption.
  + apply pq ; assumption.
- split.
  + add_exm P.
    destruct exm as [p | np].
    * assumption.
    * exfalso.
      apply npq;assumption.
   + assumption.
  Qed.

  Lemma test_6: (P->Q)->(~P->Q)->(Q->R)->R.
  Proof.
intros pq npq qr.
apply qr.
add_exm P.
destruct exm as [p | np].
- apply pq;assumption.
- apply npq;assumption.
  Qed.

End LK.

Section Club_Ecossais. (* version propositionnelle *)
  Variables E R D M K: Prop.
  (* Ecossais, chaussettes Rouges, sort le Dimanche, Marié, Kilt *)

  Hypothesis h1: ~E -> R.
  (* Tout membre non ecossais porte des chaussettes rouges *)
  Hypothesis h2: M -> ~D.
  (* Les membres maries ne sortent pas le dimanche *)
  Hypothesis h3: D <-> E.
  (* Un membre sort le dimanche si et seulement si il est ecossais *)
  Hypothesis h4: K -> E /\ M.
  (* Tout membre qui porte un kilt est ecossais et est marie *)
  Hypothesis h5: R -> K.
  (* Tout membre qui porte des chaussettes rouges porte un kilt *)
  Hypothesis h6: E -> K.
  (* Tout membre ecossais porte un kilt. *)

  Lemma personne: False. (* Le club est vide! *)
  Proof.
apply h2.
- apply h4.
  add_exm E.
  destruct exm as [e | ne].
  + apply h6; assumption.
  + apply h5; apply h1 ; assumption.
- apply h3; apply h4.
  add_exm E.
  destruct exm as [e | ne].
  + apply h6; assumption.
  + apply h5; apply h1 ; assumption.
  Qed.

End Club_Ecossais.  


  