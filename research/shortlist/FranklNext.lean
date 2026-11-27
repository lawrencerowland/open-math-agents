import Mathlib

/-!
A union-closed family may use different packages in different classes.
For a specified element, the selected package must preserve the class of its
source and yield distinct images within that class. With a single binary marker
this requires just two packages. This is a sufficient condition for the chosen
element, and does not decide the unrestricted conjecture.

Codex, with Lawrence Rowland.
-/

namespace FranklPackageClasses

variable {α : Type*} [DecidableEq α]

private theorem trace_eq_of_union_eq (X Y M : Finset α) (h : X ∪ M = Y ∪ M) :
    X \ M = Y \ M := by
  ext i
  by_cases hi : i ∈ M
  · simp [hi]
  · have membership := congrArg (fun S : Finset α => i ∈ S) h
    simpa [hi] using Iff.of_eq membership

/-- Different classes may use different packages. Preservation of the class
keeps the images of different classes disjoint. A constant class label gives
the one-package criterion. -/
theorem of_stable_package_labels {ι : Type*}
    (F : Finset (Finset α)) (a : α) (label : Finset α → ι) (pkg : ι → Finset α)
    (closed : ∀ X ∈ F, ∀ Y ∈ F, X ∪ Y ∈ F)
    (available : ∀ X ∈ F, a ∉ X → pkg (label X) ∈ F ∧ a ∈ pkg (label X))
    (stable : ∀ X ∈ F, a ∉ X → label (X ∪ pkg (label X)) = label X)
    (recover : ∀ X ∈ F, a ∉ X → ∀ Y ∈ F, a ∉ Y → label X = label Y →
      X \ pkg (label X) = Y \ pkg (label X) → X = Y) :
    F.card ≤ 2 * (F.filter fun X => a ∈ X).card := by
  classical
  let withoutA := F.filter fun X => a ∉ X
  let withA := F.filter fun X => a ∈ X
  let step := fun X : Finset α => X ∪ pkg (label X)
  have lands : Set.MapsTo step (withoutA : Set (Finset α)) (withA : Set (Finset α)) := by
    intro X hX
    obtain ⟨hXF, hXa⟩ := Finset.mem_filter.mp hX
    obtain ⟨hM, ha⟩ := available X hXF hXa
    exact Finset.mem_filter.mpr ⟨closed X hXF _ hM, Finset.mem_union_right _ ha⟩
  have inj : (withoutA : Set (Finset α)).InjOn step := by
    intro X hx Y hy h
    obtain ⟨hXF, hXa⟩ := Finset.mem_filter.mp hx
    obtain ⟨hYF, hYa⟩ := Finset.mem_filter.mp hy
    have labels : label X = label Y :=
      (stable X hXF hXa).symm.trans ((congrArg label h).trans (stable Y hYF hYa))
    apply recover X hXF hXa Y hYF hYa labels
    apply trace_eq_of_union_eq
    change X ∪ pkg (label X) = Y ∪ pkg (label Y) at h
    rwa [← labels] at h
  have bound : withoutA.card ≤ withA.card := Finset.card_le_card_of_injOn _ lands inj
  have split : withA.card + withoutA.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun X => a ∈ X)
  change F.card ≤ 2 * withA.card
  omega

/-- Use one package on sets that lack the marker, and another on sets that
have it. Only the first package must avoid the marker. -/
theorem of_one_marker (F : Finset (Finset α)) (a b : α) (M₀ M₁ : Finset α)
    (closed : ∀ X ∈ F, ∀ Y ∈ F, X ∪ Y ∈ F)
    (lo : M₀ ∈ F ∧ a ∈ M₀ ∧ b ∉ M₀) (hi : M₁ ∈ F ∧ a ∈ M₁)
    (recover₀ : ∀ X ∈ F, a ∉ X → b ∉ X → ∀ Y ∈ F, a ∉ Y → b ∉ Y →
      X \ M₀ = Y \ M₀ → X = Y)
    (recover₁ : ∀ X ∈ F, a ∉ X → b ∈ X → ∀ Y ∈ F, a ∉ Y → b ∈ Y →
      X \ M₁ = Y \ M₁ → X = Y) :
    F.card ≤ 2 * (F.filter fun X => a ∈ X).card := by
  classical
  let label := fun X : Finset α => decide (b ∈ X)
  let pkg := fun k : Bool => if k then M₁ else M₀
  apply of_stable_package_labels F a label pkg closed
  · intro X hXF hXa
    by_cases hx : b ∈ X
    · simpa [label, pkg, hx] using hi
    · simpa [label, pkg, hx] using And.intro lo.1 lo.2.1
  · intro X hXF hXa
    by_cases hx : b ∈ X <;> simp [label, pkg, hx, lo.2.2]
  · intro X hXF hXa Y hYF hYa heq ht
    by_cases hx : b ∈ X
    · have hy : b ∈ Y := by simpa [label, hx] using heq.symm
      apply recover₁ X hXF hXa hx Y hYF hYa hy
      simpa [label, pkg, hx] using ht
    · have hy : b ∉ Y := by simpa [label, hx] using heq.symm
      apply recover₀ X hXF hXa hx Y hYF hYa hy
      simpa [label, pkg, hx] using ht

end FranklPackageClasses

#print axioms FranklPackageClasses.of_one_marker
