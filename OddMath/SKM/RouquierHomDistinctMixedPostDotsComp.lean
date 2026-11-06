import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso

/-!
# The post-side dotted mixed mate with an arbitrary crossing

This extends (13)–(15) of `docs/Nondegeneracy/SwappedDistinctMixedMates.md` on the post side
from polynomial crossings to an arbitrary endomorphism `Φ` of the target of `J⁻¹`. A pre dot
`X = x ▷ _` in front of `Φ` moves to the source pre dot `A = x ▷ _` of the dotted mate for every
`Φ` (`homDistinctMixedMateDot_preDot_comp`). A post dot `Y = E ◁ Π^κ(_ ◁ y)` in front of `Φ`
moves to the transposed source dot `B = E ◁ (Π^κ H ◁ yᵀ)` when `Φ` commutes with `Y` and with
the transposed target dot `Γ = E ◁ Π^κ((Π^κ H ◁ yᵀ) ▷ E')`
(`homDistinctMixedMateDot_postDot_comp`). Hence an admissible polynomial `N` in front of `Φ`
moves to an admissible source polynomial (`exists_homDistinctMixedMateDot_comp_eq`).

`homDistinctMixedMateDot_isIso_of_comp`: if `x` is invertible, `y` is nilpotent, `Φ` commutes
with `Y` and `Γ`, and `(c • Xᵈ + N) ≫ Φ = c' • Xᵉ + N'` with `c`, `c'` units and `N`, `N'`
combinations of monomials with a positive power of `Y`, then the dotted mate of `Φ` is
invertible. This is the case of a crossing that is the inverse of a polynomial up to a
polynomial factor, for instance `a = (y - x)⁻¹`.

For a crossing of the form `Φ = J (-α²) J⁻¹`, with `α` an endomorphism of the source of `J⁻¹`
(the shape of the two-sided Rouquier crossing of a probe and a reservoir strand), conjugation by
`J` (`isoConjRingHom`) carries the pre dot, the post dot and the transposed dot to the
corresponding dots on the source of `J⁻¹` (`homDistinctMixedMateDot_isIso_of_conj`). This gives
two consequences of the defining inverse identities of the crossing:
`homDistinctMixedMateDot_isIso_of_inverse` (even colour: `α` inverts `Y - X`) and
`homDistinctMixedMateDot_isIso_of_inverse_odd` (odd colour: `(X² - Y²) α = X - Y`, `X` a unit,
`Y` nilpotent). Neither needs any assumption on bubbles.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The transposed post dot on the target of `J⁻¹`. -/
abbrev mixedPostTargetTransposeDot (A : SuperAdjunction (k := k) E' F') (y : E' ⟶ E') :
    End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')) :=
  E ◁ (homParityShift (k := k) κ).map
    (((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y) ▷ E')

/-- A pre dot in front of the crossing moves to the source of the dotted mate. -/
theorem homDistinctMixedMateDot_preDot_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) :
    homDistinctMixedMateDot E A κ τ H
        (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ≫ Φ) =
      mixedPostSourcePreDot (k := k) E κ H (F' := F') x ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  have hx' : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ x ▷ _ = (homParityShift (k := k) τ).map ((x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ▷ E') ≫ (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv := by
    have h := homMixedInterchange_pre (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F') x hx
    rw [koszulSign_zero_right, one_smul] at h
    rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]
  unfold homDistinctMixedMateDot
  rw [Category.assoc, reassoc_of% hx', Functor.map_comp, TwoSupercategory.comp_whiskerRight (R := k)]
  have hn : (x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) =
      (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫
        (homParityShift (k := k) τ).map
          ((homParityShift (k := k) τ).map ((x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ▷ E')) ▷ F' :=
    (homShiftPostAdjunction A a τ).unit.naturality _
  unfold mixedPostSourcePreDot
  rw [← reassoc_of% hn]

/-- The post dot and the transposed post dot on the target of `J⁻¹` commute. -/
theorem commute_mixedPostTargetPostDot_transposeDot {y : E' ⟶ E'}
    (hy : y ∈ parity (R := k) E' E' 0) :
    Commute (mixedPostTargetPostDot (k := k) E κ H (F' := F') y)
      (mixedPostTargetTransposeDot (k := k) E κ H A y) := by
  have hyT := SuperAdjunction.rightTranspose_mem A A hy
  have hg := TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H) hyT
  change _ ≫ _ = _ ≫ _
  rw [← TwoSupercategory.whiskerLeft_comp (R := k), ← TwoSupercategory.whiskerLeft_comp (R := k),
    ← Functor.map_comp, ← Functor.map_comp,
    TwoSupercategory.whisker_exchange_of_even_left (R := k) hg]

/-- A post dot in front of a crossing that commutes with it and with its transpose moves to the
transposed source dot of the dotted mate. -/
theorem homDistinctMixedMateDot_postDot_comp {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H
        (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ≫ Φ) =
      mixedPostSourcePostDot (k := k) E κ H A y ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  have hg : (homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y ∈
      parity (R := k) ((homParityShift (k := k) κ).obj H ≫ F') ((homParityShift (k := k) κ).obj H ≫ F') 0 :=
    TwoSupercategory.whiskerLeft_mem _ (SuperAdjunction.rightTranspose_mem A A hy)
  have hg' : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ E ◁ (homParityShift (k := k) κ).map (((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y) ▷ E') =
      (homParityShift (k := k) τ).map ((E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ▷ E') ≫ (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv := by
    have h := homMixedInterchange_naturality_even (k := k) E E' κ τ hg
    rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]
  have e₁ : mixedPostTargetPostDot (k := k) E κ H (F' := F') y ≫ Φ =
      Φ ≫ mixedPostTargetPostDot (k := k) E κ H (F' := F') y := h₁.eq
  have e₂ : mixedPostTargetTransposeDot (k := k) E κ H A y ≫ Φ =
      Φ ≫ mixedPostTargetTransposeDot (k := k) E κ H A y := h₂.eq
  have hcore : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ≫ Φ) ≫
      E ◁ (homShiftPostAdjunction A b κ).counit.app H =
      (homParityShift (k := k) τ).map ((E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ▷ E') ≫ (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ Φ ≫
        E ◁ (homShiftPostAdjunction A b κ).counit.app H := by
    rw [e₁, Category.assoc]
    dsimp only [mixedPostTargetPostDot]
    rw [← TwoSupercategory.whiskerLeft_comp (R := k),
      homShiftPostAdjunction_counit_transpose A κ H hy,
      TwoSupercategory.whiskerLeft_comp (R := k)]
    change (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ Φ ≫ mixedPostTargetTransposeDot (k := k) E κ H A y ≫ _ = _
    rw [← reassoc_of% e₂, ← reassoc_of% hg']
  unfold homDistinctMixedMateDot
  rw [hcore, Functor.map_comp, TwoSupercategory.comp_whiskerRight (R := k)]
  have hn : (E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ≫ (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) =
      (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫
        (homParityShift (k := k) τ).map
          ((homParityShift (k := k) τ).map ((E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ▷ E')) ▷ F' :=
    (homShiftPostAdjunction A a τ).unit.naturality _
  unfold mixedPostSourcePostDot
  rw [← reassoc_of% hn]

theorem homDistinctMixedMateDot_preDot_pow_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    (p : ℕ) (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) :
    homDistinctMixedMateDot E A κ τ H
        ((mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p) ≫ Φ) =
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ p :
        End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMateDot E A κ τ H Φ := by
  induction p with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.id_comp, Category.id_comp]
  | succ p ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Category.assoc, Category.assoc,
      homDistinctMixedMateDot_preDot_comp E A κ τ H hx, ih]

theorem homDistinctMixedMateDot_postDot_pow_comp {y : E' ⟶ E'}
    (hy : y ∈ parity (R := k) E' E' 0) (q : ℕ)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H
        ((mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q) ≫ Φ) =
      (mixedPostSourcePostDot (k := k) E κ H A y ^ q :
        End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMateDot E A κ τ H Φ := by
  induction q with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.id_comp, Category.id_comp]
  | succ q ih =>
    have hc := commute_mixedPostTargetPostDot_transposeDot E A κ H hy
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Category.assoc, Category.assoc,
      homDistinctMixedMateDot_postDot_comp E A κ τ H hy, ih]
    · change Commute (Φ * _) _
      exact h₁.mul_left (Commute.pow_left (Commute.refl _) q)
    · change Commute (Φ * _) _
      exact h₂.mul_left (hc.pow_left q)

/-- An admissible monomial in front of the crossing moves to the source. -/
theorem homDistinctMixedMateDot_pow_mul_pow_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) (p q : ℕ)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H
        ((mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
          mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q :
          End (E ≫ (homParityShift (k := k) κ).obj
            (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) ≫ Φ) =
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ p *
          mixedPostSourcePostDot (k := k) E κ H A y ^ q :
          End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMateDot E A κ τ H Φ := by
  have ht := ((commute_mixedPostTarget (k := k) E κ H (F' := F') hx (y := y)).pow_pow p q).eq
  have hs := ((commute_mixedPostSource (k := k) E A κ H hx (y := y)).pow_pow p q).eq
  rw [ht, hs, End.mul_def, End.mul_def, Category.assoc,
    homDistinctMixedMateDot_preDot_pow_comp E A κ τ H hx,
    homDistinctMixedMateDot_postDot_pow_comp E A κ τ H hy q Φ h₁ h₂, Category.assoc]

end Mate

/-- Conjugation by an isomorphism, as a ring homomorphism of endomorphism rings. -/
def isoConjRingHom {C : Type*} [Category C] [Preadditive C] {X Y : C} (α : X ≅ Y) :
    End X →+* End Y where
  toFun f := α.inv ≫ f ≫ α.hom
  map_one' := by
    change α.inv ≫ 𝟙 X ≫ α.hom = 𝟙 Y
    simp
  map_mul' f g := by
    change α.inv ≫ (g ≫ f) ≫ α.hom = (α.inv ≫ g ≫ α.hom) ≫ (α.inv ≫ f ≫ α.hom)
    simp
  map_zero' := by
    change α.inv ≫ (0 : X ⟶ X) ≫ α.hom = 0
    simp
  map_add' f g := by
    change α.inv ≫ (f + g : X ⟶ X) ≫ α.hom = (α.inv ≫ f ≫ α.hom) + (α.inv ≫ g ≫ α.hom)
    rw [Preadditive.add_comp, Preadditive.comp_add]

theorem isoConjRingHom_smul {k : Type*} [CommRing k] {C : Type*} [Category C] [Preadditive C]
    [Linear k C] {X Y : C} (α : X ≅ Y) (c : k) (f : End X) :
    isoConjRingHom α (c • f) = c • isoConjRingHom α f := by
  change α.inv ≫ (c • (f : X ⟶ X)) ≫ α.hom = c • (α.inv ≫ f ≫ α.hom)
  rw [Linear.smul_comp, Linear.comp_smul]

/-- An element that commutes with a unit `u` and with `v` commutes with every solution `a` of
`a u = v`. -/
theorem commute_of_mul_eq_of_isUnit {R : Type*} [Ring R] {a u v w : R} (hu : IsUnit u)
    (hau : a * u = v) (hwu : Commute w u) (hwv : Commute w v) : Commute w a := by
  obtain ⟨u, rfl⟩ := hu
  have : a = v * ↑u⁻¹ := by rw [← hau, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact hwv.mul_right hwu.units_inv_right

section Conj
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The pre dot on the source of `J⁻¹`. -/
abbrev mixedPostJPreDot (x : E ⟶ E) :
    End ((homParityShift (k := k) τ).obj ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')) :=
  (homParityShift (k := k) τ).map ((x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ▷ E')

/-- The post dot on the source of `J⁻¹`. -/
abbrev mixedPostJPostDot (y : E' ⟶ E') :
    End ((homParityShift (k := k) τ).obj ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')) :=
  (homParityShift (k := k) τ).map ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ◁ y)

/-- An even endomorphism of the middle letter on the source of `J⁻¹`. -/
abbrev mixedPostJMidDot (g : (homParityShift (k := k) κ).obj H ≫ F' ⟶
      (homParityShift (k := k) κ).obj H ≫ F') :
    End ((homParityShift (k := k) τ).obj ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')) :=
  (homParityShift (k := k) τ).map ((E ◁ g) ▷ E')

theorem commute_mixedPostJPreDot_midDot (x : E ⟶ E) {g : (homParityShift (k := k) κ).obj H ≫ F' ⟶
      (homParityShift (k := k) κ).obj H ≫ F'} (hg : g ∈ parity (R := k) _ _ 0) :
    Commute (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x)
      (mixedPostJMidDot (k := k) E κ τ H (E' := E') g) := by
  change _ ≫ _ = _ ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp, ← TwoSupercategory.comp_whiskerRight (R := k),
    ← TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whisker_exchange_of_even_right (R := k) x hg]

theorem commute_mixedPostJPostDot_midDot (y : E' ⟶ E') {g : (homParityShift (k := k) κ).obj H ≫ F' ⟶
      (homParityShift (k := k) κ).obj H ≫ F'} (hg : g ∈ parity (R := k) _ _ 0) :
    Commute (mixedPostJPostDot (k := k) E κ τ H (F' := F') y)
      (mixedPostJMidDot (k := k) E κ τ H (E' := E') g) := by
  change _ ≫ _ = _ ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp,
    TwoSupercategory.whisker_exchange_of_even_left (R := k)
      (TwoSupercategory.whiskerLeft_mem E hg) y]

theorem commute_mixedPostJPreDot_postDot {x : E ⟶ E} {y : E' ⟶ E'}
    (hx : x ∈ parity (R := k) E E 0) (hy : y ∈ parity (R := k) E' E' 0) :
    Commute (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x)
      (mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
  have h := homMixedInterchange_dot_exchange (k := k) E E' τ
    ((homParityShift (k := k) κ).obj H ≫ F') x y hx hy
  rw [koszulSign_zero_left, one_smul] at h
  change _ ≫ _ = _ ≫ _
  exact h.symm

end Conj
end OddMath.SKM
