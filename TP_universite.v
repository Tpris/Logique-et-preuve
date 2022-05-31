Require Import Setoid.

(* forall_e Hypothese t: introduit une nouvelle hypothèse qui est ce 
   qu'on obtient quand on applique Hypothese de la forme
   forall x:T, ...
   au terme t:T   *)
Ltac forall_e H x:= generalize (H x); intro.

(* Alternativement:
   specialize Hypothese with t
   specialize Hypotheses with (x:=t)
   specialize Hypothese with t as Ht
   specialize Hypothese with (x:=t) as Ht
   les deux premières formes remplacent l'hypothèse;
   specifier la variable à lier avec (x:=t) permet de sélectionner
   la variable x s'il y a plusieurs quantificateurs consécutifs,
   forall z y x, ...  *)

Section Universite.

(* Prenez le temps de vous familiariser avec les hypothèses, et de les
   interpréter mentalement: cela vous aidera pour vos preuves *)

Variable cours: Type.
Variable individu: Type.

Variables etudiant professeur: individu -> Prop.

Variable connait: individu -> individu -> Prop.
Variables enseigne etudie: individu -> cours -> Prop.

Variables Alice Bob Charlie Diana: individu.
Variable Anglais: cours.

Hypothesis Huniv: forall x, professeur x \/ etudiant x.
Hypothesis Hetud_prof: forall c x y, enseigne x c -> etudie y c -> connait y x.
Hypothesis cours_pas_vide: forall c, exists y, etudie y c/\ ~professeur y.
Hypothesis cours_prof: forall c, exists x, enseigne x c.
Hypothesis enseignant: forall c x, enseigne x c -> professeur x.
Hypothesis All_english: forall x, etudiant x -> etudie x Anglais.
Hypothesis Etud_se_connaissent: forall x y c, etudie x c -> etudie y c -> connait x y.

Hypothesis Ha: etudiant Alice.
Hypothesis Hb: ~ professeur Bob.
Hypothesis Hc: forall x, connait x Charlie -> professeur x.
Hypothesis Hac: connait Alice Charlie.
Hypothesis Hd: enseigne Diana Anglais.

(* Un exemple *)

Lemma Exemple: etudiant Bob.
Proof.
  forall_e Huniv Bob.
  destruct H.
  - contradiction.
  - assumption.
Qed.

(* Les exercices commencent ici *)

(* Dans chaque Lemme, remplacer "Admitted" par votre propre script de preuve.
   N'oubliez pas de terminer chaque preuve par "Qed". *)

Lemma Exercice1: connait Alice Diana.
Proof.
forall_e All_english Alice.
forall_e Hetud_prof Anglais.
forall_e H0 Diana.
forall_e H1 Alice.
apply H2.
- assumption.
- apply H; assumption.
Qed.

Lemma Exercice2: connait Alice Bob.
Proof.
forall_e All_english Alice.
forall_e All_english Bob.
forall_e Etud_se_connaissent Alice.
forall_e H1 Bob.
forall_e H2 Anglais.
apply H3.
- apply H; assumption.
- apply H0.
  forall_e Huniv Bob.
  destruct H4.
  + contradiction.
  + assumption.
Qed.

Lemma Exercice3: exists x, professeur x /\ forall y, etudiant y -> connait y x.
Proof.
exists Diana.
split.
- forall_e enseignant Anglais.
  forall_e H Diana.
  apply H0; assumption.
- intros.
  forall_e Hetud_prof Anglais.
  forall_e H0 Diana.
  forall_e H1 y.
  apply H2.
  + assumption.
  + forall_e All_english y.
    apply H3 ; assumption.
Qed.

Lemma Exercice4: forall x y, professeur x \/ professeur y \/ connait x y.
Proof.
intros.
forall_e Huniv x.
forall_e Huniv y.
destruct H.
- left ; assumption.
- destruct H0.
  * right; left ; assumption.
  * forall_e All_english y; forall_e All_english x.
    forall_e Etud_se_connaissent x.
    forall_e H3 y.
    forall_e H4 Anglais.
    right;right; apply H5.
    + apply H2 ; assumption.
    + apply H1 ; assumption.
Qed.

Lemma Exercice5: exists x, professeur x /\ etudiant x.
Proof.
exists Alice.
split.
- forall_e Hc Alice.
  apply H; assumption.
- assumption.
Qed.

Lemma Exercice6: forall c, ~enseigne Charlie c.
Proof.
intros.
intro.
forall_e cours_pas_vide c.
destruct H0.
destruct H0.
forall_e Huniv x.
destruct H2.
- apply H1; assumption.
- forall_e Hetud_prof c.
  forall_e H3 Charlie.
  forall_e H4 x.
  apply H1.
  forall_e Hc x.
  apply H6.
  apply H5 ; assumption.
Qed.

End Universite.

(* Fin des exercices *)
