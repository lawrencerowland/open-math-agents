import OMAStatements.S_mo_434476

/-!
# A four-object counterexample to Tim Campion's pushout question

Source: https://mathoverflow.net/questions/434476

The objects are the subsets of Bool ordered by inclusion. A map belongs to
the class when it introduces at most one of the two possible elements.
Taking the union of two distinct singletons introduces both. In a functor
category pushouts are pointwise, so stability of a morphism property under
WalkingSpan-colimits says exactly that its objects in the arrow category
are closed under pushouts there.
-/

open CategoryTheory CategoryTheory.Limits

namespace Campion

def oneNew : MorphismProperty (Set Bool) :=
  fun X Y _ => (false ∈ Y → false ∈ X) ∨ (true ∈ Y → true ∈ X)

theorem identities : oneNew.ContainsIdentities :=
  ⟨fun _ => Or.inl id⟩

theorem cancel : oneNew.HasOfPrecompProperty oneNew where
  of_precomp f _ _ h := h.elim (fun k => Or.inl (fun x => f.le (k x)))
    (fun k => Or.inr (fun x => f.le (k x)))

theorem cobase : oneNew.IsStableUnderCobaseChange where
  of_isPushout {A A' B D f g f' g'} sq hf := by
    have upper : D ⊆ B ∪ A' :=
      (sq.desc (homOfLE (X := Set Bool) Set.subset_union_left)
        (homOfLE (X := Set Bool) Set.subset_union_right) (Subsingleton.elim _ _)).le
    have transport (i : Bool) (h : i ∈ A' → i ∈ A) (hi : i ∈ D) : i ∈ B :=
      (upper hi).elim id (fun hi' => g.le (h hi'))
    exact hf.elim (fun k => Or.inl (transport false k))
      (fun k => Or.inr (transport true k))

theorem failure : ¬ oneNew.IsStableUnderColimitsOfShape WalkingSpan := by
  intro h
  let _ := h
  let o : Set Bool := ∅
  let l : Set Bool := {false}
  let r : Set Bool := {true}
  let e : o ⟶ o := 𝟙 _
  let fl : o ⟶ l := homOfLE (Set.empty_subset _)
  let fr : o ⟶ r := homOfLE (Set.empty_subset _)
  let t : span e e ⟶ span fl fr :=
    spanHomMk e fl fr (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have ht : oneNew.functorCategory WalkingSpan t := by
    rintro (_ | _ | _)
    · exact Or.inl id
    · right
      change true ∈ ({false} : Set Bool) → true ∈ (∅ : Set Bool)
      simp
    · left
      change false ∈ ({true} : Set Bool) → false ∈ (∅ : Set Bool)
      simp
  have hc := MorphismProperty.colimMap (W := oneNew) t ht
  change (false ∈ pushout fl fr → false ∈ pushout e e) ∨
    (true ∈ pushout fl fr → true ∈ pushout e e) at hc
  rw [CompleteLattice.pushout_eq_sup l r o fl fr,
      CompleteLattice.pushout_eq_sup o o o e e] at hc
  simp [l, r, o] at hc

end Campion

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_434476.main) := by
  intro h
  exact Campion.failure (h (Set Bool) Campion.oneNew Campion.identities Campion.cobase Campion.cancel)
