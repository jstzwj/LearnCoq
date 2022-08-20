Fixpoint eqb (n m : nat) : bool :=
    match n with
    | 0 => match m with
        | 0 => true
        | S m' => false
        end
    | S n' => match m with
        | 0 => false
        | S m' => eqb n' m'
        end
    end.

Fixpoint leb (n m : nat) : bool :=
    match n with
    | 0 => true
    | S n' =>
        match m with
        | 0 => false
        | S m' => leb n' m'
        end
    end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
    match (leb n m)  with
    | true => match (eqb n m) with 
        | true => false
        | false => true
        end
    | false => false 
    end.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.