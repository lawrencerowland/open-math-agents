import Mathlib

/-!
# An equivalent witness for Brendan Fong’s span comparison

Question and source: Brendan Fong, MathOverflow 251914 (2016).
https://mathoverflow.net/questions/251914

The test works for any pullback-stable class of arrows. In particular one may
take the left class of Fong’s stable factorisation system and restrict the
legs of the span to his chosen subcategory. The witnessing cospan may be
chosen independently of the pushout.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace OMA.S_mo_251914

theorem main {C : Type u} [Category.{v} C] [HasPullbacks C] [HasPushouts C]
    (E : MorphismProperty C) [E.IsStableUnderBaseChange]
    {N X Y : C} (f : N ⟶ X) (g : N ⟶ Y) :
    E (pullback.lift f g (pushout.condition (f := f) (g := g))) ↔
      ∃ (T : C) (i : X ⟶ T) (j : Y ⟶ T) (h : f ≫ i = g ≫ j),
        E (pullback.lift f g h) := by
  constructor
  · intro hk
    exact ⟨pushout f g, pushout.inl f g, pushout.inr f g, pushout.condition, hk⟩
  · rintro ⟨T, i, j, h, he⟩
    let m := pullback.map (pushout.inl f g) (pushout.inr f g) i j
      (𝟙 X) (𝟙 Y) (pushout.desc i j h) (by simp) (by simp)
    have m_fst : m ≫ pullback.fst i j = pullback.fst (pushout.inl f g) (pushout.inr f g) := by
      simp [m, pullback.map]
    have m_snd : m ≫ pullback.snd i j = pullback.snd (pushout.inl f g) (pushout.inr f g) := by
      simp [m, pullback.map]
    have m_mono : Mono m := by
      constructor
      intro W a b hab
      apply pullback.hom_ext
      · simpa only [Category.assoc, m_fst] using
          congrArg (fun z => z ≫ pullback.fst i j) hab
      · simpa only [Category.assoc, m_snd] using
          congrArg (fun z => z ≫ pullback.snd i j) hab
    apply E.of_postcomp (W' := MorphismProperty.monomorphisms C) _ m m_mono
    have eq : pullback.lift f g (pushout.condition (f := f) (g := g)) ≫ m =
        pullback.lift f g h := by
      apply pullback.hom_ext
      · simp only [Category.assoc, m_fst, pullback.lift_fst]
      · simp only [Category.assoc, m_snd, pullback.lift_snd]
    rw [eq]
    exact he

end OMA.S_mo_251914
