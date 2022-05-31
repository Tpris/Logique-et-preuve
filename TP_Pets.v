(* TP 2021 *)
Require Import Setoid.

(* cette tactique permet d'appliquer une élimination du forall de H par le terme t *)
Ltac forall_e H t := generalize (H t); intro.
(* H: une hypothèse de la forme: forall _:T,... 
   t: un terme de type T                        
   "forall_e H t" applique H à t, et donne le résultat comme hypothèse *)

(* Exemple *)

Example E0 : ~(forall x:nat, x <> x).
Proof.
  intro H.                                       
  forall_e H 32.
  apply H0.
  reflexivity.
Qed.

Section Test.
  Variable pet: Type.
  Variables lapin chat chien: pet-> Prop.
  Variables carnivore herbivore: pet -> Prop.
  Variable menace: pet -> pet -> Prop.

  Variables Medor Bouboule: pet.

  Hypothesis Hpet_cases: forall p, lapin p \/ chat p \/ chien p.
  Hypothesis Hchat: forall p, chat p -> carnivore p.
  Hypothesis Hchien: forall p, chien p -> carnivore p.
  Hypothesis Hlapin: forall p, lapin p -> herbivore p.

  Hypothesis Hchat_chien: forall p, ~(chat p /\ chien p).

  Hypothesis Hb: herbivore Bouboule.
  Hypothesis Hm: chien Medor.

  Hypothesis Hregime: forall p, ~ (carnivore p /\ herbivore p).
  Hypothesis Hmenace: forall p q, carnivore p -> herbivore q -> menace p q.

  (* Exemple *)
  Lemma L0: ~ chat Medor.
  Proof.
  intro H.
  forall_e Hchat_chien Medor.
  apply H0.
  split.
  - assumption.
  - assumption.
  Qed.

(* Pour chaque lemme ci-dessous, remplacer "Admitted." par
   votre propre script de preuve, en le terminant par "Qed.".
   Pour obtenir la note maximale, vous devez par ailleurs structurer
   vos preuves au moyen de tirets ( *-+ )
*)


  Lemma L1: forall p, ~ (chat p /\ lapin p).
  Proof.
intros.
intro.
forall_e Hregime p.
destruct H as [c l].
apply H0.
split.
- forall_e Hchat p.
  apply H;assumption.
- forall_e Hlapin p.
  apply H ; assumption.
  Qed. 

  Lemma L2: forall l, lapin l -> menace Medor l.
  Proof.
intros.
forall_e Hchien Medor.
forall_e Hlapin l.
forall_e Hmenace Medor.
forall_e H2 l.
apply H3.
- apply H0;assumption.
- apply H1;assumption.
  Qed.

  Lemma L3: ~ (Medor = Bouboule).
  Proof.
intro.
forall_e Hchien Medor.
forall_e Hregime Bouboule.
apply H1;split.
- rewrite H in H0.
  rewrite H in Hm.
  apply H0;assumption.
- assumption. 
  Qed.

  Lemma L4: forall p, chat p \/ ~ chat p.
  Proof.
intros.
forall_e Hpet_cases p.
destruct H as [ l |[ ca | ce]].
- forall_e Hlapin p.
  forall_e Hchat p.
  forall_e Hregime p.
  right;intro.
  apply H1;split.
  * apply H0;assumption.
  * apply H ; assumption.
- left;assumption.
- forall_e Hchat_chien p.
  right; intro.
  apply H;split;assumption.
  Qed.

  Lemma L5: (exists p, chat p) -> exists p, carnivore p /\ ~(p=Medor).
  Proof.
intros.
destruct H.
exists x.
split.
- forall_e Hchat x.
  apply H0;assumption.
- intro.
  rewrite H0 in H.
  forall_e Hchat_chien Medor.
  apply H1;split;assumption.
  Qed.

End Test.