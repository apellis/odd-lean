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

/-- An admissible polynomial in front of the crossing moves to an admissible source
polynomial. -/
theorem exists_homDistinctMixedMateDot_comp_eq {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) (m : ℕ)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) m) :
    ∃ Ψ ∈ admissibleMonomials (k := k)
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x)
      (mixedPostSourcePostDot (k := k) E κ H A y) (fun _ => True) (fun _ => True) m,
      homDistinctMixedMateDot E A κ τ H (N ≫ Φ) = Ψ ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  induction hN using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, -, -, hm, rfl⟩ := hz
    exact ⟨_, Submodule.subset_span ⟨p, q, trivial, trivial, hm, rfl⟩,
      homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy p q Φ h₁ h₂⟩
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [Limits.zero_comp, ← homDistinctMixedMateDotLinear_apply, map_zero, Limits.zero_comp]
  | add z z' _ _ h h' =>
    obtain ⟨Ψ, hΨ, e⟩ := h
    obtain ⟨Ψ', hΨ', e'⟩ := h'
    refine ⟨Ψ + Ψ', Submodule.add_mem _ hΨ hΨ', ?_⟩
    rw [Preadditive.add_comp, ← homDistinctMixedMateDotLinear_apply, map_add,
      homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply, e, e',
      Preadditive.add_comp]
  | smul s z _ h =>
    obtain ⟨Ψ, hΨ, e⟩ := h
    refine ⟨s • Ψ, Submodule.smul_mem _ s hΨ, ?_⟩
    rw [Linear.smul_comp, ← homDistinctMixedMateDotLinear_apply, map_smul,
      homDistinctMixedMateDotLinear_apply, e, Linear.smul_comp]

/-- The dotted mate of a crossing `Φ` is invertible when an admissible unit polynomial in front
of `Φ` gives another one: `(c • Xᵈ + N) ≫ Φ = c' • Xᵉ + N'`, with `x` invertible, `y`
nilpotent, and `Φ` commuting with the post dot and its transpose. -/
theorem homDistinctMixedMateDot_isIso_of_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) [IsIso x]
    (hn : IsNilpotent (show End E' from y))
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y))
    (c c' : kˣ) (d e : ℕ) {N N'}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) 1)
    (hN' : N' ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) 1)
    (h : ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ d + N) ≫ Φ =
      (c' : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ e + N') :
    IsIso (homDistinctMixedMateDot E A κ τ H Φ) := by
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_homDistinctMixedMateDot_comp_eq E A κ τ H hx hy 1 Φ h₁ h₂ hN
  have h0 := homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy d 0 Φ h₁ h₂
  simp only [pow_zero, mul_one] at h0
  have hR : IsIso (homDistinctMixedMateDot E A κ τ H
      ((c' : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ e + N')) :=
    homDistinctMixedMateDot_isIso E A κ τ H hx hy hn c' e hN'
  rw [← h, Preadditive.add_comp, Linear.smul_comp, ← homDistinctMixedMateDotLinear_apply,
    map_add, map_smul, homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply,
    h0, hΨe, ← Linear.smul_comp, ← Preadditive.add_comp] at hR
  have ha : IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x) := by
    refine ⟨⟨_, inv x ▷ ((homParityShift (k := k) κ).obj H ≫ F'), ?_, ?_⟩, rfl⟩ <;>
      rw [End.mul_def, ← TwoSupercategory.comp_whiskerRight (R := k)] <;>
      simp only [IsIso.hom_inv_id, IsIso.inv_hom_id] <;>
      exact TwoSupercategory.id_whiskerRight (R := k) _ _
  have hb : IsNilpotent (mixedPostSourcePostDot (k := k) E κ H A y) := by
    obtain ⟨n, hn'⟩ := isNilpotent_rightTranspose A hy hn
    refine ⟨n, ?_⟩
    rw [← rouquierPower_eq_pow] at hn'
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow,
      whiskerLeft_rouquierPower (k := k), hn']
    rw [whiskerLeft_zero' (k := k), whiskerLeft_zero' (k := k)]
  have hu := isUnit_smul_pow_add_of_mem_admissibleMonomials (k := k)
    (Pa := fun _ => True) (Pb := fun _ => True) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun p q _ _ => (commute_mixedPostSource (k := k) E A κ H hx (y := y)).pow_pow p q)
    hb ha c (d := d) trivial hΨ
  have : IsIso ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ d + Ψ :
      End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) := (isUnit_iff_isIso _).mp hu
  exact IsIso.of_isIso_comp_left
    ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ d + Ψ :
      End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) _

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

theorem isoConjRingHom_apply {C : Type*} [Category C] [Preadditive C] {X Y : C} (α : X ≅ Y)
    (f : End X) : isoConjRingHom α f = α.inv ≫ f ≫ α.hom := rfl

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

/-- **The dotted mate of a conjugated crossing.** Let `α` be an endomorphism of the source of
`J⁻¹` that commutes with the post dot `y` and with the middle dot `Π^κ H ◁ yᵀ`, and suppose
`α² (x - y)² = xᵉ + β y`. Then the dotted mate of `J (-α²) J⁻¹` is invertible when `x` is an
even invertible dot and `y` an even nilpotent dot. -/
theorem homDistinctMixedMateDot_isIso_of_conj {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) [IsIso x]
    (hn : IsNilpotent (show End E' from y))
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')))
    (h₁ : Commute α (mixedPostJPostDot (k := k) E κ τ H (F' := F') y))
    (h₂ : Commute α (mixedPostJMidDot (k := k) E κ τ H (E' := E')
      ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)))
    (e : ℕ) (β : k)
    (h : α * α * ((mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) *
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y)) =
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ e +
        β • mixedPostJPostDot (k := k) E κ τ H (F' := F') y) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)))) := by
  have hχ : ∀ f, isoConjRingHom
      (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm f =
      (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫ f ≫
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv :=
    fun f => rfl
  have hX : mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) := by
    rw [hχ]
    have h' := homMixedInterchange_pre (k := k) E E' κ τ
      ((homParityShift (k := k) κ).obj H ≫ F') x hx
    rw [koszulSign_zero_right, one_smul] at h'
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have hY : mixedPostTargetPostDot (k := k) E κ H (F' := F') y =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
    rw [hχ]
    have h' := homMixedInterchange_post (k := k) E E' κ τ
      ((homParityShift (k := k) κ).obj H ≫ F') y hy
    rw [koszulSign_zero_right, one_smul] at h'
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have hΓ : mixedPostTargetTransposeDot (k := k) E κ H A y =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (mixedPostJMidDot (k := k) E κ τ H (E' := E')
          ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) := by
    rw [hχ]
    have h' := homMixedInterchange_naturality_even (k := k) E E' κ τ
      (TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H)
        (SuperAdjunction.rightTranspose_mem A A hy))
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have hΦ : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)) =
      isoConjRingHom
        (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm
        (-(α * α)) := by
    rw [hχ, End.mul_def]
    erw [Preadditive.neg_comp]
    rw [Preadditive.comp_neg, Category.assoc]
    exact (Preadditive.comp_neg _ _).symm
  have hc := commute_mixedPostJPreDot_postDot (k := k) E κ τ H (F' := F') hx hy
  refine homDistinctMixedMateDot_isIso_of_comp (E := E) (A := A) (κ := κ) (τ := τ) (H := H)
    hx hy hn _ ?_ ?_ 1 (-1) 2 e
    (N := (-2 : k) • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ 1 *
        mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ 1) +
      (1 : k) • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ 0 *
        mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ 2))
    (N' := (-β) • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ 0 *
        mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ 1)) ?_ ?_ ?_
  · rw [hΦ, hY]
    exact ((h₁.mul_left h₁).neg_left).map _
  · rw [hΦ, hΓ]
    exact ((h₂.mul_left h₂).neg_left).map _
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, 1, trivial, trivial, le_rfl, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 2, trivial, trivial, by norm_num, rfl⟩))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 1, trivial, trivial, le_rfl, rfl⟩)
  · have hsq : (1 : k) • mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 2 +
        ((-2 : k) • (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 1 *
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y ^ 1) +
        (1 : k) • (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 0 *
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y ^ 2)) =
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y) *
        (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
      rw [pow_one, pow_one, pow_zero, one_mul, one_smul, one_smul, pow_two, pow_two, sub_mul,
        mul_sub, mul_sub, ← hc.eq, neg_smul, two_smul]
      abel
    have key : -(α * α) * ((1 : k) • mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 2 +
        ((-2 : k) • (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 1 *
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y ^ 1) +
        (1 : k) • (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 0 *
          mixedPostJPostDot (k := k) E κ τ H (F' := F') y ^ 2))) =
        (-1 : k) • mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ e +
          (-β) • (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 0 *
            mixedPostJPostDot (k := k) E κ τ H (F' := F') y ^ 1) := by
      rw [hsq, neg_mul, h, pow_zero, one_mul, pow_one, neg_smul, one_smul, neg_smul, neg_add]
    have := congrArg (isoConjRingHom
      (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).symm) key
    simp only [map_mul, map_neg, map_add, map_pow, isoConjRingHom_smul] at this
    rw [hΦ, hX, hY, ← End.mul_def, Units.val_one, Units.val_neg, Units.val_one]
    simpa only [map_mul, map_neg, map_add, map_pow, isoConjRingHom_smul] using this

/-- **Even case.** If `x` is an even invertible dot, `y` an even nilpotent dot and `α` is a
two-sided inverse of `y - x` on the source of `J⁻¹`, then the dotted mate of `J (-α²) J⁻¹` is
invertible. -/
theorem homDistinctMixedMateDot_isIso_of_inverse {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) (hxi : IsIso x)
    (hn : IsNilpotent (show End E' from y))
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')))
    (h₁ : α ≫ (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) = 𝟙 _)
    (h₂ : (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) ≫ α = 𝟙 _) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)))) := by
  have := hxi
  have hau : α * (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) = 1 := h₂
  have hua : (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) * α = 1 := h₁
  have hu : IsUnit (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) := ⟨⟨_, α, hua, hau⟩, rfl⟩
  have hc := commute_mixedPostJPreDot_postDot (k := k) E κ τ H (F' := F') hx hy
  have hg := TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H)
    (SuperAdjunction.rightTranspose_mem A A hy)
  have hxg := commute_mixedPostJPreDot_midDot (k := k) E κ τ H (E' := E') x hg
  have hyg := commute_mixedPostJPostDot_midDot (k := k) E κ τ H y hg
  refine homDistinctMixedMateDot_isIso_of_conj E A κ τ H hx hy hn α ?_ ?_ 0 0 ?_
  · exact (commute_of_mul_eq_of_isUnit hu hau ((Commute.refl _).sub_right hc.symm)
      (Commute.one_right _)).symm
  · exact (commute_of_mul_eq_of_isUnit hu hau (hyg.symm.sub_right hxg.symm)
      (Commute.one_right _)).symm
  · generalize mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x = X at hau ⊢
    generalize mixedPostJPostDot (k := k) E κ τ H (F' := F') y = Y at hau ⊢
    rw [← neg_sub Y X, neg_mul_neg, pow_zero, zero_smul, add_zero]
    calc α * α * ((Y - X) * (Y - X)) = α * (α * (Y - X)) * (Y - X) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hau, mul_one, hau]

/-- **Odd case.** If `x` is an odd dot, `y` an odd nilpotent dot, the dot `X` of `x` on the
source of `J⁻¹` is a unit, the dot `Y` of `y` is nilpotent, and `(X² - Y²) ≫ α = X - Y`, then
the dotted mate of `J (-α²) J⁻¹` is invertible. -/
theorem homDistinctMixedMateDot_isIso_of_inverse_odd {x : E ⟶ E}
    (hx : x ∈ parity (R := k) E E 1) {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 1)
    (hxi : IsIso x) (hn : IsNilpotent (show End E' from y))
    (hxu : IsUnit (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x))
    (hyn : IsNilpotent (mixedPostJPostDot (k := k) E κ τ H (F' := F') y))
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')))
    (h₂ : (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ≫
        mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y ≫
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) ≫ α =
      (show _ ⟶ _ from mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) -
        (show _ ⟶ _ from mixedPostJPostDot (k := k) E κ τ H (F' := F') y)) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)))) := by
  have := hxi
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hx2 : x ≫ x ∈ parity (R := k) E E 0 := h11 ▸ Supercategory.comp_mem hx hx
  have hy2 : y ≫ y ∈ parity (R := k) E' E' 0 := h11 ▸ Supercategory.comp_mem hy hy
  have hn2 : IsNilpotent (show End E' from y ≫ y) := by
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    change ((show End E' from y) * (show End E' from y)) ^ n = 0
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hn, zero_pow two_ne_zero]
  have hX2 : mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') (x ≫ x) =
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x := by
    change (homParityShift (k := k) τ).map _ = _ ≫ _
    rw [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k),
      Functor.map_comp]
  have hY2 : mixedPostJPostDot (k := k) E κ τ H (F' := F') (y ≫ y) =
      mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y := by
    change (homParityShift (k := k) τ).map _ = _ ≫ _
    rw [TwoSupercategory.whiskerLeft_comp (R := k), Functor.map_comp]
  -- the odd dots anticommute
  have hac : mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x =
      -(mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
    have h := homMixedInterchange_dot_exchange (k := k) E E' τ
      ((homParityShift (k := k) κ).obj H ≫ F') x y hx hy
    have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
    rw [hs, neg_one_zsmul] at h
    exact h
  have hg := TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H)
    (SuperAdjunction.rightTranspose_mem A A hy2)
  have hXg := commute_mixedPostJPreDot_midDot (k := k) E κ τ H (E' := E') x hg
  have hYg := commute_mixedPostJPostDot_midDot (k := k) E κ τ H y hg
  have hau : α * (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) =
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y := h₂
  obtain ⟨G, hG⟩ : ∃ G, G = mixedPostJMidDot (k := k) E κ τ H (E' := E')
      ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A (y ≫ y)) :=
    ⟨_, rfl⟩
  rw [← hG] at hXg hYg
  set X := mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x
  set Y := mixedPostJPostDot (k := k) E κ τ H (F' := F') y
  have hYYX : Commute (Y * Y) X := by
    change Y * Y * X = X * (Y * Y)
    rw [mul_assoc, hac, mul_neg, ← mul_assoc, hac, neg_mul, neg_neg, mul_assoc]
  have hXXY : Commute (X * X) Y := by
    change X * X * Y = Y * (X * X)
    rw [← mul_assoc Y X X, hac, neg_mul, mul_assoc X Y X, hac, mul_neg, neg_neg, mul_assoc]
  have hYY : Commute (Y * Y) Y := (Commute.refl Y).mul_left (Commute.refl Y)
  have hXX : Commute (X * X) X := (Commute.refl X).mul_left (Commute.refl X)
  have hs : IsUnit (X * X - Y * Y) := by
    rw [sub_eq_add_neg]
    obtain ⟨m, hm⟩ := hyn
    exact (show IsNilpotent (-(Y * Y)) from ⟨m, by
        rw [neg_pow, ← pow_two, ← pow_mul, mul_comm 2 m, pow_mul, hm, zero_pow two_ne_zero,
          mul_zero]⟩).isUnit_add_left_of_commute (hxu.mul hxu)
      ((hXXY.mul_right hXXY).neg_right).symm
  have hds : Commute (X - Y) (X * X - Y * Y) :=
    ((hXX.symm.sub_right hYYX.symm)).sub_left (hXXY.symm.sub_right hYY.symm)
  refine homDistinctMixedMateDot_isIso_of_conj E A κ τ H hx2 hy2 hn2 α ?_ ?_ 1 1 ?_
  · rw [hY2]
    exact (commute_of_mul_eq_of_isUnit hs hau ((hYYX.mul_right hYYX).sub_right (Commute.refl _))
      (hYYX.sub_right hYY)).symm
  · rw [← hG]
    exact (commute_of_mul_eq_of_isUnit hs hau
      ((hXg.symm.mul_right hXg.symm).sub_right (hYg.symm.mul_right hYg.symm))
      (hXg.symm.sub_right hYg.symm)).symm
  · rw [hX2, hY2, pow_one, one_smul]
    calc α * α * ((X * X - Y * Y) * (X * X - Y * Y)) =
          α * (α * (X * X - Y * Y)) * (X * X - Y * Y) := by simp only [mul_assoc]
      _ = α * ((X * X - Y * Y) * (X - Y)) := by rw [hau, mul_assoc, hds.eq]
      _ = (X - Y) * (X - Y) := by rw [← mul_assoc, hau]
      _ = X * X + Y * Y := by
          rw [sub_mul, mul_sub, mul_sub, hac]
          abel

end Conj
end OddMath.SKM
