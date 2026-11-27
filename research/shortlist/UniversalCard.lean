import Mathlib

/-!
# Extending an isomorphism over universal vertices

The vertex-deleted graph is the induced subgraph on all vertices distinct
from the deleted vertex. The statement allows arbitrary vertex types.
-/

namespace ReconstructionEssai

private noncomputable def restore {V W : Type*} (v : V) (w : W)
    (f : {x : V // x ≠ v} → {y : W // y ≠ w}) (x : V) : W := by
  classical
  exact if hx : x = v then w else (f ⟨x, hx⟩).val

private noncomputable def restoreEquiv {V W : Type*} (v : V) (w : W)
    (e : {x : V // x ≠ v} ≃ {y : W // y ≠ w}) : V ≃ W := by
  classical
  refine ⟨restore v w e, restore w v e.symm, ?_, ?_⟩
  · intro x
    by_cases hx : x = v
    · subst x
      simp [restore]
    · have hy : (e ⟨x, hx⟩).val ≠ w := (e ⟨x, hx⟩).property
      simp [restore, hx, hy]
  · intro y
    by_cases hy : y = w
    · subst y
      simp [restore]
    · have hx : (e.symm ⟨y, hy⟩).val ≠ v := (e.symm ⟨y, hy⟩).property
      simp [restore, hy, hx]

/-- If the deleted vertices are universal, an isomorphism of their
vertex-deleted cards gives an isomorphism of the original graphs. -/
theorem iso_of_universal_cards {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W)
    (hv : ∀ x, x ≠ v → G.Adj v x)
    (hw : ∀ y, y ≠ w → H.Adj w y)
    (e : G.induce {x | x ≠ v} ≃g H.induce {y | y ≠ w}) :
    Nonempty (G ≃g H) := by
  classical
  refine ⟨⟨restoreEquiv v w e.toEquiv, ?_⟩⟩
  intro a b
  change H.Adj (restore v w e.toEquiv a) (restore v w e.toEquiv b) ↔ G.Adj a b
  by_cases ha : a = v
  · subst a
    by_cases hb : b = v
    · subst b
      simp [restore]
    · simpa [restore, hb] using
        (iff_of_true (hw _ (e ⟨b, hb⟩).property) (hv b hb))
  · by_cases hb : b = v
    · subst b
      simpa [restore, ha] using
        (iff_of_true (hw _ (e ⟨a, ha⟩).property).symm (hv a ha).symm)
    · have h : H.Adj (e ⟨a, ha⟩).val (e ⟨b, hb⟩).val ↔ G.Adj a b :=
        e.map_rel_iff
      simpa [restore, ha, hb] using h

end ReconstructionEssai
