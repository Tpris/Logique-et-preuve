(* Logique du premier ordre *)

(** Tactiques :
  pour forall :  
    introduction : 
            intro, intros.
    elimination :
            apply, eapply, specialize.
            (H x ...)

  pour exists : 
     introduction: exists (fournir le terme)
     elimintation: destruct.

  pour = reflexivity (introduction),
         rewrite H   [in HØ] (elimination)
         rewrite <- H [in H0]
                  
 *)

(* tactique maison pour eliminer un forall *)
(* il faut fournir le terme temoin *)

Ltac forall_e H t := (generalize (H t); intro).

(* Exemple *)

Example E0 : ~(forall x:nat, x <> x).
Proof.
  intro H.                                       
  forall_e H 42.
  unfold not in H0.
  apply H0.
  reflexivity.
Qed.

Section Syllogismes. (* Entrainements *)
  Variable Etre: Type.
  Variables humain mortel animal : Etre -> Prop.

  Variable Socrate : Etre.
  Variable Rhino : Etre.

  Hypothesis HM : forall x,  humain x -> mortel x.
  Hypothesis HSocrate : humain Socrate.
  Hypothesis Etre_disj : forall x:Etre,  humain x \/ animal x.
  Hypothesis Hrhino : ~ humain Rhino.

  Lemma Syllogisme :  mortel Socrate.
  Proof.
    apply HM. (* elimination du forall et modus-ponens *)
    assumption.
  Qed.

  Lemma contraposee : forall x, ~ mortel x -> ~ humain x.
  Proof.  
    intros x Hx H.
    unfold not in Hx.
    apply Hx.
    apply HM; assumption.
  Qed.    

  Lemma Lmortel: exists x, mortel x.
  Proof.  
   exists Socrate.  (* introduction de l'existentiel *)
   apply Syllogisme. (* On peut appliquer un théorème déjà prouvé *)  
  Qed.


  Lemma Lanimal: exists x, animal x.
  Proof.  
    exists Rhino.
    destruct (Etre_disj Rhino).
    (* elimination sur la disjonction "Etre_disj" appliquée à Rhino *)
    (* On pourrait aussi utiliser forall_e *)
    - contradiction.
    - assumption.
  Qed.

  Lemma L : ~(exists x:Etre,  ~ humain x /\ ~ animal x).
  Proof.
    intro H.
    destruct H as [e He]. (* elimination de l'existentiel *)
    destruct He.
    forall_e Etre_disj e.
    destruct H1.
    - contradiction.
    - contradiction.
  Qed.

End Syllogismes.

Section Egalite. (* Entrainements, sur l'egalite *) 
  Variable A : Type.
  Variable f : A -> A.

  Lemma Egal1 : forall x:A, exists y: A, x=y.
  Proof.
   intros x.
   exists x.
   reflexivity. 
   Qed.

  Lemma Egal2 : forall x y z: A, x = y -> y = z -> x = z.
  Proof.
    intros x y z H H0.
    rewrite H.
    assumption.
  Qed. 

  (* x <> y est une abréviation de ~ (x = y) *)
  (* "unfold not" va faire apparaître l'implication vers False *)

  Lemma diff_eq : forall x y z:A, x <> y -> y = z -> x <> z.
  Proof.  
    intros.
    rewrite H0 in H.
    assumption. 
  Qed.
  
  (* À vous ! *)
  Lemma Egal3 : forall x y z: A , x = y -> x <> z -> z <> y.
  Proof.
intros.
unfold not in H0.
unfold not.
intro.
rewrite H1 in H0.
apply H0;assumption.
  Qed.

  Lemma L4 : forall x y:A, f x <> f y -> x <> y.
  Proof.
intros.
unfold not in H.
unfold not.
intro.
apply H.
rewrite H0.
reflexivity.
  Qed.

End Egalite.

(* Quelques preuves de logique du premier ordre *)

(* Supprimer les "Admitted" (on admet la preuve complète) et les "admit" 
   (on admet le but courant) dans toutes les preuves qui suivent, et les
   compléter *)

Section QuelquesPreuves.
  Variable A B: Type.
  Variables P Q : A -> Prop.
  Variable R : A -> B -> Prop.
  Variable X : Prop.

  Lemma Question1 : (forall x:A, P x /\ Q x) <->
                    (forall x:A, P x) /\ (forall x:A, Q x).
  Proof.
    split. intro H.
    - split.
      + intro x.
        destruct (H x).
        assumption.
      + intro x; destruct (H x). trivial.
    -  intro x. split.
      + destruct x as [Hp Hq].
        apply Hp.
      + destruct x.
        apply H0.
  Qed.

  Lemma Question2 : (forall x, P x) \/ (forall x, Q x) ->
                    forall x, P x \/ Q x.
  Proof.
intro.
destruct H.
- left. apply H.
- right; apply H.
  Qed.
  
  Lemma Question3 : (exists x:A, P x /\ Q x) ->
                    (exists x:A, P x) /\  (exists x:A, Q x).
  Proof.
intro.
destruct H.
destruct H.
split.
- exists x. assumption.
- exists x. assumption.
  Qed.

  Lemma Question4 : (exists x:A, P x \/ Q x) <->
                    (exists x:A, P x) \/   (exists x:A, Q x).
  Proof.
  split; intros.
- destruct H as [x[H1 | H2]].
  * left; exists x; assumption.
  * right; exists x; assumption.
- destruct H as [[x H1] | [x H2]].
  * exists x; left; assumption.
  * exists x; right; assumption.
  Qed.

  Section Question5.
    Hypothesis H : forall x, P x -> Q x.
    Hypothesis H0 : exists x, P x.

    Lemma L5 : exists x, Q x.
    Proof.
destruct H0.
exists x.
apply H;assumption.
    Qed.

  End Question5.
 
  (* Attention au parenthésage *)
  Lemma Question6 : forall x,  P x -> exists y,  P y.
  Proof.
intros.
exists x.
assumption.
  Qed.
 
  Lemma Question7 : ~(exists x, P x) <-> forall x, ~ P x.
  Proof.
  split;intros.
- intro.
  apply H.
  exists x; assumption.
- intro.
  destruct H0.
  forall_e H x.
  apply H1; assumption.
  Qed.

  (* Ici, X joue le rôle de n'importe quelle proposition où x n'est
     pas libre *)
  Lemma Question8 : ((exists x, P x) -> X) <->
                     forall x, P x -> X.
  Proof.
split; intros.
- apply H; exists x; assumption.
- destruct H0.
  forall_e H x.
  apply H1;assumption.
  Qed.

  Lemma Question9 :  (exists x:A, forall y:B, R x y)
                      -> (forall y:B, exists x:A, R x y).
  Proof. 
intros.
destruct H.
exists x.
forall_e H y.
assumption.
  Qed.

  (* Sur l egalite *)
  Lemma eq_sym : forall x y:A, x = y -> y = x.
  Proof.
    intros x y H.
    rewrite H.     
    reflexivity.
  Qed.

  Lemma eq_trans : forall x y z:A, x = y -> y = z -> x = z.
  Proof.
intros.
rewrite H0 in H.
assumption.
  Qed.

End QuelquesPreuves.

Section TypeVide.
(* Dans cette section, on envisage la possibilité que le type A soit vide *)
  Variable A: Type.
  Variable P: A->Prop.

  Definition A_est_vide := forall x:A, x <> x.

  
  Lemma TV1 : A_est_vide -> forall x:A, P x.
  Proof.
    unfold A_est_vide. (* A compléter *)
    intros.
    forall_e H x.
    destruct H0.
    forall_e H x.
    contradiction.
  Qed.

  Lemma TV2 : (forall x y:A, x <> y) -> A_est_vide.
  Proof.
unfold A_est_vide.
intros.
intro.
forall_e H x.
forall_e H1 x.
apply H2.
assumption.
  Qed.

End TypeVide.


(* On passe maintenant en logique classique *)
Require Import Classical.


Section classic.
  Variable A: Type.
  Variables P Q: A->Prop.

  Hypothesis exm: forall X:Prop, X \/ ~X.

  Ltac add_exm  P :=
  let hname := fresh "exm" in
  assert(hname : P \/ ~P); [classical_right; assumption|].

(* ne pas essayer de comprendre :
   applique le raisonnement par l'absurde classique 

   Transforme un but  "Gamma |- P " en 
                      "Gamma, ~P |- False" *)

  Ltac absurdK :=
    match goal with |- ?X =>
                    let hname := fresh "exm" in
                    assert(hname := exm  X);
                      destruct hname;[assumption| elimtype False]
    end.

  Lemma Classical_Question1 : ~ (forall x, P x) <-> exists x, ~ P x.
  Proof.   
    split; intro H.
    - absurdK.
      apply H.
      intro.
      absurdK.
      apply H0.
      exists x.
      assumption.
    - intro.
      destruct H.
      forall_e H0 x.
      apply H; assumption.
  Qed. (* finir la preuve; l'autre sens est intuitionniste *)

  (* Dans le même esprit *)
  Lemma Classical_Question2: ~(forall x, P x /\ Q x) <-> exists x, ~ P x \/ ~ Q x.
  Proof.
split;intros.
- absurdK.
  apply H.
  intro.
  split.
  + absurdK.
    apply H0.
    exists x.
    left; assumption.
  + absurdK.
    apply H0.
    exists x.
    right; assumption.
- intro.
  destruct H.
  forall_e H0 x.
  destruct H1 as [p q].
  destruct H as [np | nq].
  + apply np; assumption.
  + apply nq ; assumption.
  Qed.


(* On complète la section "TypeVide", mais en classique *)
(* Pour des raisons techniques, le type s'appelle B *)

Section TypeVideClassique.
  Variable B: Type.
  Variable PP: B->Prop.

  Definition B_est_vide := forall x:B, x <> x.

  Hypothesis H : ~ B_est_vide.
  Hypothesis H0 : forall x:B, PP x.
    
  Lemma forall_to_exists : exists x:B, PP x. (* difficile *)
  Proof.
    unfold B_est_vide in H.
    assert (exists x:B, x = x).
    {  absurdK.
       apply H.
       intros.
       intro.
       apply H1.
       exists x.
       assumption.
    }
    absurdK.
    apply H; intro. intro.
    apply H2.
    exists x.
    forall_e H0 x.
    assumption.
  Qed. (* Compléter la preuve, y compris le "admit" *)

End TypeVideClassique.
End classic.


 
