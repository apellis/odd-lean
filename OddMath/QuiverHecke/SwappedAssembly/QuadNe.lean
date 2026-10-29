/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SlideAssembly

/-! # The distinct-colour quadratic relations for the swapped generators

The relations (1.7) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
for distinct colours `i ≠ j`, for the images of the upward crossings and the dots in the
swapped action (`docs/Nondegeneracy/SwappedActionAssembly.md`, §3).

On the word `Eᵢ Eⱼ` with `i ≠ j` every summand path `p` has exactly one partner path `m` of
`Eⱼ Eᵢ` with the same end sectors, and no other path of `Eᵢ Eⱼ` has those end sectors. So the
entry of the two-crossing diagram is diagonal, with diagonal entry the product of the two
crossing entries through `m`. On the four kinds of paths:

* probe/probe and reservoir/reservoir: the multicolour quadratic relation (1.7) of the probe,
  resp. the reservoir, whiskered and conjugated; in the probe case the two dots trade places,
  and the polynomial is symmetric under this exchange since the dots supercommute;
* probe/reservoir: the entry `J` followed by `J⁻¹ Q` gives `Q`;
* reservoir/probe: `J⁻¹ Q` followed by `J` gives `J⁻¹ Q J`, which is `Q` in the transported
  dots.

## Main results

* `ProbeReservoir.cross_comp_cross_eq_qExpr`: (1.7) of a multicolour family in the shape
  `qExpr`.
* `ProbeReservoir.swappedGens_crossCrossNe`: the diagonal entry of the two crossings is the
  parameter polynomial in the two dots.
* `ProbeReservoir.swappedGens_crossQuad`: `CrossQuad (P.swappedGens c L)`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

/-! ## The parameter polynomial under algebra maps and exchange of the dots -/

section QAlgebra

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {C' : Type*} [Category C'] [Preadditive C'] [Linear k C']

variable (Sc) in
theorem qExpr_map {A : C} {A' : C'} (φ : End A →ₐ[k] End A') (a b : End A) (i j : I) :
    φ (qExpr Sc a b i j) = qExpr Sc (φ a) (φ b) i j := by
  unfold qExpr
  split_ifs <;> simp only [map_add, map_smul, map_sum, map_mul, map_pow, map_one]

theorem pow_mul_signed {R : Type*} [Ring R] [Algebra k R] {a b : R} {ε : k}
    (h : a * b = ε • (b * a)) : ∀ n : ℕ, a ^ n * b = ε ^ n • (b * a ^ n)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc, pow_mul_signed h n, smul_mul_assoc,
      smul_smul, mul_assoc, ← pow_succ']

variable (Sc) in
/-- `Q_ij(a, b) = Q_ji(b, a)` for supercommuting `a`, `b` whose sign is trivial on the powers
of `a` that occur. -/
theorem qExpr_swap {A : C} (a b : End A) (i j : I) (ε : k)
    (h : a * b = ε • (b * a)) (hε : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 → ε ^ n = 1) :
    qExpr Sc a b i j = qExpr Sc b a j i := by
  unfold qExpr
  by_cases hd : D.d i j = 0
  · have hd' : D.d j i = 0 := (D.d_eq_zero_iff i j).1 hd
    simp only [hd, hd', ↓reduceIte, Sc.t_symm_of_d_eq_zero i j hd]
  · have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff j i).1 h)
    simp only [hd, hd', ↓reduceIte]
    rw [add_comm ((Sc.t i j : k) • a ^ D.dn i j), Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    rw [Sc.s_symm i j p q]
    by_cases hs : Sc.s j i q p = 0
    · rw [hs, zero_smul, zero_smul]
    · have hp : (p : ZMod 2) * D.parity i = 0 := by
        by_contra hp'
        apply hs
        rw [← Sc.s_symm]
        refine Sc.s_eq_zero i j p q ?_
        rcases Supercategory.parity_eq_zero_or_one ((p : ZMod 2) * D.parity i) with h0 | h1
        · exact absurd h0 hp'
        · exact h1
      have hc : Commute (a ^ p) b := by
        show a ^ p * b = b * a ^ p
        rw [pow_mul_signed h p, hε p hp, one_smul]
      rw [(hc.pow_right q).eq]

/-- A `k`-linear functor as an algebra map of endomorphism rings. -/
@[simps]
def functorAlg (F : C ⥤ C') [F.Additive] [F.Linear k] (A : C) :
    End A →ₐ[k] End (F.obj A) where
  toFun x := F.map x
  map_one' := F.map_id A
  map_mul' x y := F.map_comp y x
  map_zero' := F.map_zero A A
  map_add' _ _ := F.map_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, End.one_def]
    rw [Functor.map_smul, F.map_id]

/-- Conjugation by an isomorphism as an algebra map of endomorphism rings. -/
@[simps]
def conjAlg {A A' : C} (e : A ≅ A') : End A →ₐ[k] End A' where
  toFun x := e.inv ≫ x ≫ e.hom
  map_one' := by simp [End.one_def]
  map_mul' x y := by simp [End.mul_def]
  map_zero' := by
    show e.inv ≫ (0 : A ⟶ A) ≫ e.hom = 0
    simp
  map_add' x y := by
    show e.inv ≫ (x + y) ≫ e.hom = e.inv ≫ x ≫ e.hom + e.inv ≫ y ≫ e.hom
    rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, End.one_def]
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.inv_hom_id]

end QAlgebra

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- **(1.7) of a multicolour family for distinct colours** in the shape of `qExpr`. -/
theorem cross_comp_cross_eq_qExpr (T : RouquierFamily (k := k) (B := B) D)
    (hT : RouquierMulticolour T Sc) {i j : I} (hij : i ≠ j) {a b c d : X}
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) :
    T.cross i j h₁ h₂ h₃ h₄ ≫ T.cross j i h₃ h₄ h₁ h₂ =
      qExpr Sc (End.of (T.E j h₁ ◁ T.dot i h₂))
        (T.dot j h₁ ▷ T.E i h₂) i j := by
  have hl : ∀ n : ℕ, T.E j h₁ ◁ rouquierPower (T.dot i h₂) n =
      (End.of (T.E j h₁ ◁ T.dot i h₂)) ^ n := fun n => by
    rw [rouquierPower_eq_pow]
    exact map_pow (functorAlg (k := k) (homPre (k := k) (T.E j h₁)) (T.E i h₂)) _ n
  have hr : ∀ n : ℕ, rouquierPower (T.dot j h₁) n ▷ T.E i h₂ =
      (End.of (T.dot j h₁ ▷ T.E i h₂)) ^ n := fun n => by
    rw [rouquierPower_eq_pow]
    exact map_pow (functorAlg (k := k) (homPost (k := k) (T.E i h₂)) (T.E j h₁)) _ n
  unfold qExpr
  split_ifs with hd
  · rw [hT.quadZero i j hij hd]
    rfl
  · rw [hT.quadNe i j hij hd]
    simp only [hl, hr]
    rfl

/-! ## The probe/probe entry -/

section ProbeCore

variable (T : RouquierFamily (k := k) (B := B) D)

/-- The reassociated whiskered probe crossing: the probe/probe entry of the crossing image
before the transport of its target. -/
def probeCore (i j : I) {a b c d : X} (h₁ : a + D.α i = b) (h₂ : b + D.α j = d)
    (h₃ : a + D.α j = c) (h₄ : c + D.α i = d) {w : B} (Z : T.obj d ⟶ w) :
    T.E i h₁ ≫ (T.E j h₂ ≫ Z) ⟶ T.E j h₃ ≫ (T.E i h₄ ≫ Z) :=
  (associator (T.E i h₁) (T.E j h₂) Z).inv ≫ T.cross j i h₁ h₂ h₃ h₄ ▷ Z ≫
    (associator (T.E j h₃) (T.E i h₄) Z).hom

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- **(1.7) on the probe/probe entry**: the two reassociated probe crossings compose to the
parameter polynomial in the dots on the two strands. -/
theorem probeCore_quad (hT : RouquierMulticolour T Sc) {i j : I} (hij : i ≠ j) {a b c d : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α j = d) (h₃ : a + D.α j = c) (h₄ : c + D.α i = d)
    {w : B} (Z : T.obj d ⟶ w) :
    probeCore T i j h₁ h₂ h₃ h₄ Z ≫ probeCore T j i h₃ h₄ h₁ h₂ Z =
      qExpr Sc (End.of (T.dot i h₁ ▷ (T.E j h₂ ≫ Z))) (End.of (T.E i h₁ ◁ (T.dot j h₂ ▷ Z)))
        i j := by
  set L : End (T.E i h₁ ≫ (T.E j h₂ ≫ Z)) := End.of (T.dot i h₁ ▷ (T.E j h₂ ≫ Z))
  set R : End (T.E i h₁ ≫ (T.E j h₂ ≫ Z)) := End.of (T.E i h₁ ◁ (T.dot j h₂ ▷ Z))
  let φ := (conjAlg (k := k) (associator (T.E i h₁) (T.E j h₂) Z)).comp
    (functorAlg (k := k) (homPost (k := k) Z) (T.E i h₁ ≫ T.E j h₂))
  have hφR : φ (End.of (T.E i h₁ ◁ T.dot j h₂)) = R := by
    show (associator (T.E i h₁) (T.E j h₂) Z).inv ≫ (T.E i h₁ ◁ T.dot j h₂) ▷ Z ≫
      (associator (T.E i h₁) (T.E j h₂) Z).hom = _
    rw [TwoSupercategory.whisker_assoc (R := k)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  have hφL : φ (End.of (T.dot i h₁ ▷ T.E j h₂)) = L := by
    show (associator (T.E i h₁) (T.E j h₂) Z).inv ≫ (T.dot i h₁ ▷ T.E j h₂) ▷ Z ≫
      (associator (T.E i h₁) (T.E j h₂) Z).hom = _
    rw [← TwoSupercategory.whiskerRight_comp (R := k)]
  have hLR : L * R = zsign k (D.parity i * D.parity j) • (R * L) := by
    have h := TwoSupercategory.super_interchange (R := k) (T.dot_mem i h₁)
      (TwoSupercategory.whiskerRight_mem (R := k) Z (T.dot_mem j h₂))
    rw [koszulSign_smul_eq_zsign (k := k)] at h
    have h' := congrArg (zsign k (D.parity i * D.parity j) • ·) h
    simp only [smul_smul, zsign_mul_self', one_smul] at h'
    exact h'.symm
  have hε : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 →
      zsign k (D.parity i * D.parity j) ^ n = 1 :=
    fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn
  rw [qExpr_swap Sc L R i j _ hLR hε, ← hφR, ← hφL, ← qExpr_map,
    ← cross_comp_cross_eq_qExpr T hT hij.symm h₁ h₂ h₃ h₄]
  show _ = (associator (T.E i h₁) (T.E j h₂) Z).inv ≫
    (T.cross j i h₁ h₂ h₃ h₄ ≫ T.cross i j h₃ h₄ h₁ h₂) ▷ Z ≫
      (associator (T.E i h₁) (T.E j h₂) Z).hom
  rw [TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [probeCore, Category.assoc, Iso.hom_inv_id_assoc]

end ProbeCore

/-! ## The reservoir/reservoir entry -/

omit [TwoSupercategory k B] in
/-- Two parity-shifted morphisms separated by transports along `p = q` compose. -/
@[reassoc]
theorem homParityShift_map_eqToHom_comp {y z : B} {Y Y' : y ⟶ z} {p q : ZMod 2} (hpq : p = q)
    (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y)
    (e₁ : (homParityShift (k := k) p).obj Y' = (homParityShift (k := k) q).obj Y')
    (e₂ : (homParityShift (k := k) q).obj Y = (homParityShift (k := k) p).obj Y) :
    (homParityShift (k := k) p).map g₁ ≫ eqToHom e₁ ≫ (homParityShift (k := k) q).map g₂ ≫
      eqToHom e₂ = (homParityShift (k := k) p).map (g₁ ≫ g₂) := by
  subst hpq
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.map_comp]

section ResCore

variable (W : RouquierFamily (k := k) (B := B) D)

/-- The reservoir crossing whiskered by `Z` and conjugated by the comparisons of the parity
shifts: the reservoir/reservoir entry of the crossing image before the transport of its
target. -/
def resCore (i j : I) (κi κj : ZMod 2) {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) {x : B} (Z : x ⟶ W.obj a) :
    (homParityShift (k := k) κi).obj ((homParityShift (k := k) κj).obj (Z ≫ W.E j h₁) ≫
        W.E i h₂) ⟶
      (homParityShift (k := k) κj).obj ((homParityShift (k := k) κi).obj (Z ≫ W.E i h₃) ≫
        W.E j h₄) :=
  (postPairIso (k := k) (W.E i h₂) Z (W.E j h₁) κi κj).hom ≫
    (homParityShift (k := k) (κj + κi)).map
      ((associator Z (W.E j h₁) (W.E i h₂)).hom ≫ Z ◁ W.cross i j h₁ h₂ h₃ h₄ ≫
        (associator Z (W.E i h₃) (W.E j h₄)).inv) ≫
    eqToHom (by rw [add_comm]) ≫ (postPairIso (k := k) (W.E j h₄) Z (W.E i h₃) κj κi).inv

/-- **(1.7) on the reservoir/reservoir entry**: the two conjugated reservoir crossings compose
to the parameter polynomial in the dots on the two strands. -/
theorem resCore_quad (hW : RouquierMulticolour W Sc) {i j : I} (hij : i ≠ j) (κi κj : ZMod 2)
    {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c)
    (h₄ : c + D.α j = d) {x : B} (Z : x ⟶ W.obj a) :
    resCore W i j κi κj h₁ h₂ h₃ h₄ Z ≫ resCore W j i κj κi h₃ h₄ h₁ h₂ Z =
      qExpr Sc (End.of ((homParityShift (k := k) κi).map
          ((homParityShift (k := k) κj).obj (Z ≫ W.E j h₁) ◁ W.dot i h₂)))
        (End.of ((homParityShift (k := k) κi).map
          ((homParityShift (k := k) κj).map (Z ◁ W.dot j h₁) ▷ W.E i h₂))) i j := by
  set P1 := postPairIso (k := k) (W.E i h₂) Z (W.E j h₁) κi κj
  set α := associator Z (W.E j h₁) (W.E i h₂)
  let φ := (conjAlg (k := k) P1.symm).comp
    ((functorAlg (k := k) (homParityShift (k := k) (κj + κi)) _).comp
      ((conjAlg (k := k) α.symm).comp
        (functorAlg (k := k) (homPre (k := k) Z) (W.E j h₁ ≫ W.E i h₂))))
  have hφL : φ (End.of (W.E j h₁ ◁ W.dot i h₂)) = End.of ((homParityShift (k := k) κi).map
      ((homParityShift (k := k) κj).obj (Z ≫ W.E j h₁) ◁ W.dot i h₂)) := by
    show P1.hom ≫ (homParityShift (k := k) (κj + κi)).map
      (α.hom ≫ Z ◁ (W.E j h₁ ◁ W.dot i h₂) ≫ α.inv) ≫ P1.inv = _
    rw [← TwoSupercategory.associator_naturality_right_assoc (R := k), Iso.hom_inv_id,
      Category.comp_id, postPairIso_outer_inv Z _ _ κi κj _ (W.dot_mem i h₂),
      Iso.hom_inv_id_assoc]
  have hφR : φ (End.of (W.dot j h₁ ▷ W.E i h₂)) = End.of ((homParityShift (k := k) κi).map
      ((homParityShift (k := k) κj).map (Z ◁ W.dot j h₁) ▷ W.E i h₂)) := by
    show P1.hom ≫ (homParityShift (k := k) (κj + κi)).map
      (α.hom ≫ Z ◁ (W.dot j h₁ ▷ W.E i h₂) ≫ α.inv) ≫ P1.inv = _
    rw [← TwoSupercategory.associator_naturality_middle_assoc (R := k), Iso.hom_inv_id,
      Category.comp_id, postPairIso_inner_inv Z _ _ κi κj, Iso.hom_inv_id_assoc]
  rw [← hφL, ← hφR, ← qExpr_map, ← cross_comp_cross_eq_qExpr W hW hij h₁ h₂ h₃ h₄]
  show _ = P1.hom ≫ (homParityShift (k := k) (κj + κi)).map
    (α.hom ≫ Z ◁ (W.cross i j h₁ h₂ h₃ h₄ ≫ W.cross j i h₃ h₄ h₁ h₂) ≫ α.inv) ≫ P1.inv
  simp only [resCore, Category.assoc, Iso.inv_hom_id_assoc]
  rw [homParityShift_map_eqToHom_comp_assoc (add_comm κj κi)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, TwoSupercategory.whiskerLeft_comp (R := k)]
  rfl

end ResCore

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
