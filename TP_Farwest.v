Ltac forall_e H t := (generalize (H t); intro).

Require Import Setoid.

Section Farwest.
  Variable personnage: Type.
  Variables humain animal bandit cowboy: personnage -> Prop.
  Variables Averell Rantanplan Luke: personnage.
  Variable idiot: personnage -> Prop.

  Hypothesis Hh_ou_a: forall p:personnage, animal p \/ humain p.
  Hypothesis Hhna: forall p:personnage, ~(humain p /\ animal p).
  Hypothesis Hbnc: forall p:personnage, ~(cowboy p /\ bandit p).
  Hypothesis Hb: forall p:personnage, bandit p -> humain p.
  Hypothesis Hc: forall p:personnage, cowboy p -> humain p.
  Hypothesis Hhum: forall p:personnage, humain p -> cowboy p \/ bandit p.

  Hypothesis Hbni: exists p:personnage, bandit p /\ ~ idiot p.
  
  Hypothesis Hav: bandit Averell.
  Hypothesis Hlu: cowboy Luke.
  Hypothesis Hra: animal Rantanplan.
  Hypothesis Hid: idiot Rantanplan /\ idiot Averell.

  Theorem Exemple: Averell <> Luke.
  Proof.
    intro Hal.
    rewrite Hal in Hav.
    forall_e Hbnc Luke.
    apply H.
    split.
    - assumption.
    - assumption.
  Qed.

  Theorem Exercice1: ~ cowboy Rantanplan.
  Proof.
intro cr.
forall_e Hhna Rantanplan.
apply H.
split.
- forall_e Hc Rantanplan.
  apply H0; assumption.
- assumption.
  Qed.

  Theorem Exercice2: forall p:personnage, ~(bandit p /\ animal p).
  Proof.
intros.
intro.
forall_e Hb p.
forall_e Hhna p.
destruct H as [bp ap].
apply H1.
split.
- apply H0; assumption.
- assumption.
  Qed.

  Theorem Exercice3: forall p:personnage, cowboy p \/ bandit p <-> humain p.
  Proof.
intros.
split; intros.
- forall_e Hb p; forall_e Hc p.
  destruct H as [cp | bp].
  + apply H1; assumption.
  + apply H0; assumption.
- forall_e Hhum p.
  apply H0 ; assumption. 
  Qed.

  Theorem Exercice4: forall p:personnage, animal p \/ cowboy p \/ bandit p.
  Proof.
intros.
forall_e Hh_ou_a p; forall_e Hhum p.
destruct H as [a | h].
- left;assumption.
- right.
  apply H0; assumption.
  Qed.

  Theorem Exercice5: exists p:personnage, bandit p /\ p<>Averell.
  Proof.
destruct Hbni.
exists x.
destruct H as [xb xni].
split.
- assumption.
- intro.
  destruct Hid as [ri ai].
  rewrite H in xni.
  apply xni; assumption.
  Qed.

End Farwest.
