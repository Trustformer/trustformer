(*! General purpose tactics !*)
Ltac destr :=
  match goal with
  |- context[match ?a with _ => _ end] => destruct a eqn:?; try congruence
  end.
Ltac destr_in H :=
  match type of H with
  | context[match ?a with _ => _ end] => destruct a eqn:?
  end.
Ltac inv H := inversion H; try subst; clear H.

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q. Proof. auto. Qed.
Ltac exploit x :=
  refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _) _)
  || refine (modusponens _ _ (x _ _) _)
  || refine (modusponens _ _ (x _) _).

Ltac trim H :=
  match type of H with
  | ?a -> ?b =>
    let x := fresh "H" in
    assert(x: a);[|specialize(H x); clear x]
  end.
