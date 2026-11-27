import Mathlib

/-!
# Inserting one or two elements in a finite family

For the singleton case, it suffices that inserting the designated element
into every member omitting it lands back in the family. With two designated
elements, it suffices to insert both into members omitting both. This proves
a conclusion about at least one of the two elements.

The singleton injection is also formalised in the Formal Conjectures entry
`UnionClosed.union_closed.variants.singleton_mem`. For the classical pair
case, see D. G. Sarvate and J.-C. Renaud (1989), Theorem 2, and R. van der
Hout and K. Roos (2026), Theorem 3.1. We use their neither-to-both argument
under its local insertion hypothesis. The general conjecture stays open.

Codex, with Lawrence Rowland.
-/

open Finset

namespace FranklScope

variable {α : Type*} [DecidableEq α]

def occurrences (F : Finset (Finset α)) (a : α) : ℕ :=
  (F.filter fun X => a ∈ X).card

/-- Only the part of insertion closure on sets missing both elements is needed. -/
theorem of_local_pair (F : Finset (Finset α)) (a b : α)
    (step : ∀ X ∈ F, a ∉ X → b ∉ X → insert a (insert b X) ∈ F) :
    F.card ≤ 2 * occurrences F a ∨ F.card ≤ 2 * occurrences F b := by
  classical
  let A := F.filter fun X => a ∈ X
  let B := F.filter fun X => b ∈ X
  let Z := F.filter fun X => ¬ (a ∈ X ∨ b ∈ X)
  have lands : Set.MapsTo (fun X => insert a (insert b X)) (Z : Set (Finset α))
      ((A ∩ B : Finset (Finset α)) : Set (Finset α)) := by
    intro X hX
    obtain ⟨hF, hmiss⟩ := Finset.mem_filter.mp hX
    have h := step X hF (fun hi => hmiss (Or.inl hi)) (fun hi => hmiss (Or.inr hi))
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨h, by simp⟩, Finset.mem_filter.mpr ⟨h, by simp⟩⟩
  have injects : (Z : Set (Finset α)).InjOn (fun X => insert a (insert b X)) := by
    intro X hX Y hY heq
    have hx : ¬ (a ∈ X ∨ b ∈ X) := (Finset.mem_filter.mp hX).2
    have hy : ¬ (a ∈ Y ∨ b ∈ Y) := (Finset.mem_filter.mp hY).2
    ext i
    by_cases hia : i = a
    · subst i
      exact ⟨fun h => (hx (Or.inl h)).elim, fun h => (hy (Or.inl h)).elim⟩
    by_cases hib : i = b
    · subst i
      exact ⟨fun h => (hx (Or.inr h)).elim, fun h => (hy (Or.inr h)).elim⟩
    have hi := congrArg (fun S : Finset α => i ∈ S) heq
    simpa [hia, hib] using (Iff.of_eq hi)
  have comparison : Z.card ≤ (A ∩ B).card := Finset.card_le_card_of_injOn _ lands injects
  have union_eq : A ∪ B = F.filter (fun X => a ∈ X ∨ b ∈ X) := by
    ext X
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    tauto
  have split : (A ∪ B).card + Z.card = F.card := by
    rw [union_eq]
    exact Finset.card_filter_add_card_filter_not (s := F) (fun X => a ∈ X ∨ b ∈ X)
  have inclusion_exclusion := Finset.card_union_add_card_inter A B
  change F.card ≤ 2 * A.card ∨ F.card ≤ 2 * B.card
  omega

/-- For a fixed element, insertion remains injective on all members omitting it. -/
theorem of_local_insert (F : Finset (Finset α)) (a : α)
    (step : ∀ X ∈ F, a ∉ X → insert a X ∈ F) :
    F.card ≤ 2 * occurrences F a := by
  have h := of_local_pair F a a (fun X hX ha _ => by simpa using step X hX ha)
  exact h.elim id id

def Closed (F : Finset (Finset α)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ∪ Y ∈ F

/-- A fixed member may play the role of the singleton whenever the traces
outside that member distinguish all the sets omitting the chosen element. -/
theorem of_distinct_outside_traces (F : Finset (Finset α)) (a : α) (M : Finset α)
    (closed : Closed F) (hM : M ∈ F) (ha : a ∈ M)
    (recover : ∀ X ∈ F, a ∉ X → ∀ Y ∈ F, a ∉ Y →
      X \ M = Y \ M → X = Y) : F.card ≤ 2 * occurrences F a := by
  classical
  let withoutA := F.filter fun X => a ∉ X
  let keep := F.filter fun X => a ∈ X
  have lands : Set.MapsTo (fun X => X ∪ M) (withoutA : Set (Finset α))
      (keep : Set (Finset α)) := by
    intro X hX
    exact Finset.mem_filter.mpr
      ⟨closed X (Finset.mem_filter.mp hX).1 M hM, Finset.mem_union_right _ ha⟩
  have injects : (withoutA : Set (Finset α)).InjOn (fun X => X ∪ M) := by
    intro X hX Y hY heq
    obtain ⟨hXF, hXa⟩ := Finset.mem_filter.mp hX
    obtain ⟨hYF, hYa⟩ := Finset.mem_filter.mp hY
    apply recover X hXF hXa Y hYF hYa
    ext i
    by_cases hi : i ∈ M
    · simp [hi]
    · have membership := congrArg (fun S : Finset α => i ∈ S) heq
      simpa [hi] using (Iff.of_eq membership)
  have bound : withoutA.card ≤ keep.card := Finset.card_le_card_of_injOn _ lands injects
  have partition : keep.card + withoutA.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun X => a ∈ X)
  change F.card ≤ 2 * keep.card
  omega

/-- The known singleton case of the union-closed sets conjecture. -/
theorem of_singleton_mem (F : Finset (Finset α)) (a : α)
    (closed : Closed F) (ha : {a} ∈ F) : F.card ≤ 2 * occurrences F a := by
  apply of_local_insert
  intro X hX _
  simpa using closed {a} ha X hX

/-- The known two-element case, also allowing the two elements to coincide. -/
theorem of_pair_mem (F : Finset (Finset α)) (a b : α)
    (closed : Closed F) (hab : {a, b} ∈ F) :
    F.card ≤ 2 * occurrences F a ∨ F.card ≤ 2 * occurrences F b := by
  apply of_local_pair
  intro X hX _ _
  simpa using closed {a, b} hab X hX

end FranklScope
