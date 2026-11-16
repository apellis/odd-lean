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

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
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

/-! ## The mixed entries -/

section Mixed

variable (P : ProbeReservoir k B D Sc)

/-- The parameter polynomial of the path `(P,R)` of `Eᵢ Eⱼ`, conjugated by the mixed
interchange, is the parameter polynomial `Q_ji` in the transported dots of the path `(R,P)`
of `Eⱼ Eᵢ`. -/
theorem mixedJ_inv_mixedQ_hom (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t))
    (Z : P.H (nextSector (true, j) false (nextSector (true, i) true t))) :
    (P.mixedJ i j t hR Z).inv ≫ P.mixedQ i j t hR Z ≫ (P.mixedJ i j t hR Z).hom =
      qExpr Sc (homContentPostDot P.T.obj P.W j t.1 (P.muP t) (P.muM_postE j hR)
          ((P.step (true, i) true (nextSector (true, j) false t) trivial).obj Z))
        ((P.step (true, j) false t hR).map (P.T.dot i (P.muP_preE i t) ▷ Z)) j i := by
  set J := P.mixedJ i j t hR Z
  set ε := zsign k (D.parity i * D.parity j)
  have hε : ε * ε = 1 := zsign_mul_self' _
  have hxy : P.prPreDot i j t hR Z * P.prPostDot i j t hR Z =
      ε • (P.prPostDot i j t hR Z * P.prPreDot i j t hR Z) := by
    simp only [End.mul_def]
    exact P.prPostDot_comp_prPreDot i j t hR Z
  have hQ : P.mixedQ i j t hR Z =
      qExpr Sc (P.prPostDot i j t hR Z) (P.prPreDot i j t hR Z) j i :=
    qExpr_swap Sc _ _ i j ε hxy (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
  have hflip : ∀ {a : End (P.prObj i j t hR Z)} {a' : End (P.rpObj j i t hR Z)},
      a ≫ J.hom = ε • (J.hom ≫ a') → J.inv ≫ a = ε • (a' ≫ J.inv) := by
    intro a a' h
    rw [inv_comp_signed J a a' ε hε h, smul_smul, hε, one_smul]
  have hc := comp_qExpr (Sc := Sc) J.inv _ _ (P.prPostDot i j t hR Z)
    (P.prPreDot i j t hR Z) j i ε ε (hflip (P.prPostDot_comp_mixedJ_ne i j t hR Z))
    (hflip (P.prPreDot_comp_mixedJ_ne i j t hR Z))
    (fun n hn => by
      rw [show ε = zsign k (D.parity j * D.parity i) by rw [mul_comm]]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)
    (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
  rw [hQ, reassoc_of% hc, Iso.inv_hom_id, Category.comp_id]

end Mixed

/-! ## Transport of the entries -/

section Transport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

variable (Sc) in
/-- A composite of two morphisms equal to the parameter polynomial transports along
heterogeneous equalities of its factors and its dots. -/
theorem quad_of_heq {A M A' M' : C} (hA : A = A') (hM : M = M') {f : A ⟶ M} {g : M ⟶ A}
    {f' : A' ⟶ M'} {g' : M' ⟶ A'} {l r : A ⟶ A} {l' r' : A' ⟶ A'} (hf : HEq f f')
    (hg : HEq g g') (hl : HEq l l') (hr : HEq r r') (i j : I)
    (h : f' ≫ g' = qExpr Sc l' r' i j) : f ≫ g = qExpr Sc l r i j := by
  subst hA hM
  cases hf; cases hg; cases hl; cases hr
  exact h

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] [Preadditive C] [Linear k C] in
/-- Postcomposition with the image of a transport is heterogeneously trivial. -/
theorem comp_map_eqToHom_heq {E : Type*} [Category E] (F : C ⥤ E) {A : E} {Y Y' : C}
    (e : Y = Y') (f : A ⟶ F.obj Y) : HEq (f ≫ F.map (eqToHom e)) f := by
  subst e
  simp

end Transport

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
theorem probeCore_heq (T : RouquierFamily (k := k) (B := B) D) (i j : I) {a b c d d' : X}
    (h₁ : a + D.α i = b) (h₂ : b + D.α j = d) (h₃ : a + D.α j = c) (h₄ : c + D.α i = d)
    (h₂' : b + D.α j = d') (h₄' : c + D.α i = d') (hd : d = d') {w w' : B}
    (hw : w = w') (Z : T.obj d ⟶ w) (Z' : T.obj d' ⟶ w') (hZ : HEq Z Z') :
    HEq (probeCore T i j h₁ h₂ h₃ h₄ Z) (probeCore T i j h₁ h₂' h₃ h₄' Z') := by
  subst hd hw
  cases hZ
  rfl

theorem resCore_heq (W : RouquierFamily (k := k) (B := B) D) (i j : I) (κi κj : ZMod 2)
    {a a' b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d) (h₃ : a + D.α i = c)
    (h₄ : c + D.α j = d) (h₁' : a' + D.α j = b) (h₃' : a' + D.α i = c) (ha : a = a')
    {x x' : B} (hx : x = x') (Z : x ⟶ W.obj a) (Z' : x' ⟶ W.obj a') (hZ : HEq Z Z') :
    HEq (resCore W i j κi κj h₁ h₂ h₃ h₄ Z) (resCore W i j κi κj h₁' h₂ h₃' h₄ Z') := by
  subst ha hx
  cases hZ
  rfl

section Assembly

variable (P : ProbeReservoir k B D Sc)

theorem preCrossNe_heq (i j : I) (t : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) true t))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true t)))
    (h₄ : -P.muP (nextSector (true, j) true t) + D.α i =
      -P.muP (nextSector (true, j) true (nextSector (true, i) true t))) :
    HEq (P.preCrossNe i j t hs Z) (probeCore P.T i j (P.muP_preE i t) (P.muP_preE j _)
      (P.muP_preE j t) h₄ (hs ▸ Z)) := by
  refine HEq.trans (heq_of_eq ?_) (comp_map_eqToHom_heq (P.step (true, j) true t trivial)
    (eq_of_heq (P.preE_obj_heq i hs h₄ (P.muP_preE i _) Z)) (probeCore P.T i j (P.muP_preE i t)
      (P.muP_preE j _) (P.muP_preE j t) h₄ (hs ▸ Z)))
  simp only [preCrossNe, probeCore, Category.assoc]

theorem postCrossNe_heq (i j : I) (t : Sector I) (hv₁ : StepValid (true, i) false t)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) false t))
    (hw₁ : StepValid (true, j) false t)
    (hw₂ : StepValid (true, i) false (nextSector (true, j) false t))
    (hs : nextSector (true, j) false (nextSector (true, i) false t) =
      nextSector (true, i) false (nextSector (true, j) false t))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false t)))
    (h₃ : P.muM (nextSector (true, j) false (nextSector (true, i) false t)) + D.α i =
      P.muM (nextSector (true, j) false t)) :
    HEq (P.postCrossNe i j t hv₁ hv₂ hw₁ hw₂ hs Z)
      (resCore P.W i j (homContentShift D i t.1) (homContentShift D j t.1)
        (P.muM_postE j hv₂) (P.muM_postE i hv₁) h₃ (P.muM_postE j hw₁) (hs ▸ Z)) := by
  refine HEq.trans (heq_of_eq ?_) (comp_map_eqToHom_heq (P.step (true, j) false t hw₁)
    (eq_of_heq (P.postE_obj_heq i t.1 hs h₃ (P.muM_postE i hw₂) Z))
    (resCore P.W i j (homContentShift D i t.1) (homContentShift D j t.1)
      (P.muM_postE j hv₂) (P.muM_postE i hv₁) h₃ (P.muM_postE j hw₁) (hs ▸ Z)))
  simp only [postCrossNe, resCore, Category.assoc]

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- For distinct colours, a summand path of `Eᵢ Eⱼ` is determined by its end sectors. -/
theorem path_eq_of_ne {i j : I} (hij : i ≠ j) {ν : X} {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j]) s t) : p = q := by
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e', rfl⟩ := SPath.exists_eq_two q
  have hE := e.trans e'.symm
  have hi := congrArg (fun x : Sector I => x.1 i) hE
  have hj := congrArg (fun x : Sector I => x.1 j) hE
  cases σ₁ <;> cases σ₂ <;> cases τ₁ <;> cases τ₂ <;>
    simp [nextSector, hij, Ne.symm hij] at hi hj <;> rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem compPow_eq_pow {C : Type*} [Category C] {Y : C} (f : Y ⟶ Y) :
    ∀ n : ℕ, compPow f n = (End.of f) ^ n
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ, End.mul_def, ← compPow_eq_pow f n]
    rfl

/-- **The diagonal entry of the two distinct-colour crossings** for the swapped generators is
the parameter polynomial `Q_ij` in the dots on the two strands. -/
theorem swappedGens_crossCrossNe (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    (hij : i ≠ j) {s t : Sector I} (p : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    crossCross (P.swappedGens c L) i j ν p p Z =
      qExpr Sc (leftDot (P.swappedGens c L) i j ν p Z) (rightDot (P.swappedGens c L) i j ν p Z)
        i j := by
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_two p
  have key : ∀ m : SPath (wd D ν [up j, up i]) s t,
      crossCross (P.swappedGens c L) i j ν (SPath.two σ₁ σ₂ hv₁ hv₂ e) (SPath.two σ₁ σ₂ hv₁ hv₂ e)
        Z = P.twoTwo _ _ _ _ (P.crossNeEntry i j _ _ _ _) (SPath.two σ₁ σ₂ hv₁ hv₂ e) m rfl Z ≫
          P.twoTwo _ _ _ _ (P.crossNeEntry j i _ _ _ _) m (SPath.two σ₁ σ₂ hv₁ hv₂ e) rfl Z := by
    intro m
    have : Subsingleton (SPath (wd D ν [up j, up i]) s t) := ⟨path_eq_of_ne hij.symm⟩
    let : Fintype (SPath (wd D ν [up j, up i]) s t) := Fintype.ofFinite _
    unfold crossCross
    refine (Fintype.sum_subsingleton _ m).trans ?_
    exact congrArg₂ (· ≫ ·) (P.crossImage_ne c hij ν _ m Z) (P.crossImage_ne c hij.symm ν m _ Z)
  cases σ₁ <;> cases σ₂
  case true.true =>
    have e' : nextSector (true, i) true (nextSector (true, j) true s) = t := by
      rw [← e]; simp only [nextSector, add_right_comm]
    rw [key (SPath.two true true trivial trivial e')]
    have hZ' := P.castH_obj_heq e' Z
    have hZ'' := P.castH_obj_heq e Z
    have hs := e.trans (rfl.trans e'.symm)
    have hs2 := e'.trans (rfl.trans e.symm)
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      true true true true hv₁ hv₂ trivial trivial e e' rfl Z _ hZ'
    have hg := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry j i (SKM.wt D ν [up i]) (SKM.wt D ν []) (SKM.wt D ν [up j]) (SKM.wt D ν []))
      true true true true trivial trivial hv₁ hv₂ e' e rfl Z _ hZ''
    have hf' : HEq _ (P.preCrossNe i j s hs ((P.castH e').obj Z)) := hf
    have hg' : HEq _ (P.preCrossNe j i s hs2 ((P.castH e).obj Z)) := hg
    have hZ₀ : HEq (hs ▸ (P.castH e').obj Z : P.H _) Z := (P.sector_heq hs _).trans hZ'
    have h₄ : -P.muP (nextSector (true, j) true s) + D.α i =
        -P.muP (nextSector (true, j) true (nextSector (true, i) true s)) := by
      rw [hs]; exact P.muP_preE i _
    have h₄' : -P.muP (nextSector (true, i) true s) + D.α j =
        -P.muP (nextSector (true, i) true (nextSector (true, j) true s)) := by
      rw [← hs]; exact P.muP_preE j _
    have hF := hf'.trans (P.preCrossNe_heq i j s hs _ h₄)
    have hG := (hg'.trans (P.preCrossNe_heq j i s hs2 _ h₄')).trans
      (probeCore_heq P.T j i _ _ _ _ h₄ (P.muP_preE j _) (congrArg (fun x => -P.muP x) hs2)
        (congrArg (fun x => P.W.obj (P.muM x)) hs2) _ _
        ((P.sector_heq hs2 _).trans (hZ''.trans hZ₀.symm)))
    have hA := P.pathFunctor_two_obj true true hv₁ hv₂ e Z _ hZ₀
    have hM := (P.pathFunctor_two_obj (c₁ := { l := (true, j), r := SKM.wt D ν [up i] }) (c₂ := { l := (true, i), r := SKM.wt D ν [] }) true true trivial trivial e' Z _ hZ').trans
      (congrArg (P.step (true, j) true s trivial).obj
        (eq_of_heq (P.preE_obj_heq i hs h₄ (P.muP_preE i _) ((P.castH e').obj Z))).symm)
    exact quad_of_heq Sc hA hM hF hG (P.leftDot_two_probe_heq c L i j ν true hv₂ e Z _ hZ₀)
      (P.rightDot_two_probe_heq c L i j ν true hv₁ e Z _ hZ₀) i j
      (probeCore_quad P.T P.probeRel hij _ _ _ _ _)
  case false.false =>
    have hw₁ : StepValid (true, j) false s := by
      simpa [StepValid, nextSector, Finsupp.single_apply, hij, Ne.symm hij] using hv₂
    have hw₂ : StepValid (true, i) false (nextSector (true, j) false s) := by
      simpa [StepValid, nextSector, Finsupp.single_apply, hij, Ne.symm hij] using hv₁
    have e' : nextSector (true, i) false (nextSector (true, j) false s) = t := by
      rw [← e]; simp only [nextSector, tsub_right_comm]
    rw [key (SPath.two false false hw₁ hw₂ e')]
    have hZ' := P.castH_obj_heq e' Z
    have hZ'' := P.castH_obj_heq e Z
    have hs := e.trans (rfl.trans e'.symm)
    have hs2 := e'.trans (rfl.trans e.symm)
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      false false false false hv₁ hv₂ hw₁ hw₂ e e' rfl Z _ hZ'
    have hg := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry j i (SKM.wt D ν [up i]) (SKM.wt D ν []) (SKM.wt D ν [up j]) (SKM.wt D ν []))
      false false false false hw₁ hw₂ hv₁ hv₂ e' e rfl Z _ hZ''
    have hf' : HEq _ (P.postCrossNe i j s hv₁ hv₂ hw₁ hw₂ hs ((P.castH e').obj Z)) := hf
    have hg' : HEq _ (P.postCrossNe j i s hw₁ hw₂ hv₁ hv₂ hs2 ((P.castH e).obj Z)) := hg
    have hZ₀ : HEq (hs ▸ (P.castH e').obj Z : P.H _) Z := (P.sector_heq hs _).trans hZ'
    have h₃ : P.muM (nextSector (true, j) false (nextSector (true, i) false s)) + D.α i =
        P.muM (nextSector (true, j) false s) := by
      rw [hs]; exact P.muM_postE i hw₂
    have h₃' : P.muM (nextSector (true, i) false (nextSector (true, j) false s)) + D.α j =
        P.muM (nextSector (true, i) false s) := by
      rw [← hs]; exact P.muM_postE j hv₂
    have hF := hf'.trans (P.postCrossNe_heq i j s hv₁ hv₂ hw₁ hw₂ hs _ h₃)
    have hG := (hg'.trans (P.postCrossNe_heq j i s hw₁ hw₂ hv₁ hv₂ hs2 _ h₃')).trans
      (resCore_heq P.W j i _ _ _ _ _ _ h₃ (P.muM_postE j hv₂) (congrArg P.muM hs2)
        (congrArg (fun x => P.T.obj (-P.muP x)) hs2) _ _
        ((P.sector_heq hs2 _).trans (hZ''.trans hZ₀.symm)))
    have hA := P.pathFunctor_two_obj false false hv₁ hv₂ e Z _ hZ₀
    have hM := (P.pathFunctor_two_obj (c₁ := { l := (true, j), r := SKM.wt D ν [up i] }) (c₂ := { l := (true, i), r := SKM.wt D ν [] }) false false hw₁ hw₂ e' Z _ hZ').trans
      (congrArg (P.step (true, j) false s hw₁).obj
        (eq_of_heq (P.postE_obj_heq i s.1 hs h₃ (P.muM_postE i hw₂) ((P.castH e').obj Z))).symm)
    exact quad_of_heq Sc hA hM hF hG
      (P.leftDot_two_reservoir_heq c L i j ν hv₁ false hv₂ e Z _ hZ₀)
      (P.rightDot_two_reservoir_heq c L i j ν false hv₁ hv₂ e Z _ hZ₀) i j
      (resCore_quad P.W P.reservoirRel hij _ _ _ _ _ _ _)
  case true.false =>
    have hw : StepValid (true, j) false s := hv₂
    have e₂ : nextSector (true, i) true (nextSector (true, j) false s) = t := e
    rw [key (SPath.two false true hw trivial e₂)]
    have hZ' := P.castH_obj_heq e Z
    have hZ₂ := P.castH_obj_heq e₂ Z
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      true false false true hv₁ hv₂ hw trivial e e₂ rfl Z _ hZ₂
    have hg := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry j i (SKM.wt D ν [up i]) (SKM.wt D ν []) (SKM.wt D ν [up j]) (SKM.wt D ν []))
      false true true false hw trivial hv₁ hv₂ e₂ e rfl Z _ hZ'
    have hf' : HEq _ (P.mixedJ i j s hw ((P.castH e₂).obj Z)).hom := hf
    have hg' : HEq _ ((P.mixedJ i j s hw ((P.castH e₂).obj Z)).inv ≫
        P.mixedQ i j s hw ((P.castH e₂).obj Z)) := hg
    exact quad_of_heq Sc (P.pathFunctor_two_obj true false hv₁ hv₂ e Z _ hZ')
      (P.pathFunctor_two_obj (c₁ := { l := (true, j), r := SKM.wt D ν [up i] })
        (c₂ := { l := (true, i), r := SKM.wt D ν [] })
        false true hw trivial e₂ Z _ hZ₂) hf' hg'
      (P.leftDot_two_probe_heq c L i j ν false hv₂ e Z _ hZ')
      (P.rightDot_two_reservoir_heq c L i j ν true hv₁ hv₂ e Z _ hZ') i j
      (by rw [Iso.hom_inv_id_assoc]; rfl)
  case false.true =>
    have hw : StepValid (true, i) false (nextSector (true, j) true s) := hv₁
    have e₂ : nextSector (true, i) false (nextSector (true, j) true s) = t := e
    rw [key (SPath.two true false trivial hw e₂)]
    have hZ' := P.castH_obj_heq e Z
    have hZ₂ := P.castH_obj_heq e₂ Z
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      false true true false hv₁ hv₂ trivial hw e e₂ rfl Z _ hZ₂
    have hg := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry j i (SKM.wt D ν [up i]) (SKM.wt D ν []) (SKM.wt D ν [up j]) (SKM.wt D ν []))
      true false false true trivial hw hv₁ hv₂ e₂ e rfl Z _ hZ'
    have hf' : HEq _ ((P.mixedJ j i s hv₁ ((P.castH e₂).obj Z)).inv ≫
        P.mixedQ j i s hv₁ ((P.castH e₂).obj Z)) := hf
    have hg' : HEq _ (P.mixedJ j i s hv₁ ((P.castH e₂).obj Z)).hom := hg
    exact quad_of_heq Sc (P.pathFunctor_two_obj false true hv₁ hv₂ e Z _ hZ')
      (P.pathFunctor_two_obj (c₁ := { l := (true, j), r := SKM.wt D ν [up i] })
        (c₂ := { l := (true, i), r := SKM.wt D ν [] })
        true false trivial hw e₂ Z _ hZ₂) hf' hg'
      (P.leftDot_two_reservoir_heq c L i j ν hv₁ true hv₂ e Z _ hZ')
      (P.rightDot_two_probe_heq c L i j ν false hv₁ e Z _ hZ') i j
      (by rw [Category.assoc]; exact P.mixedJ_inv_mixedQ_hom j i s hv₁ _)

/-- **The quadratic relations (1.7)** for the swapped generators. -/
theorem swappedGens_crossQuad (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    CrossQuad (P.swappedGens c L) where
  quadEq i ν _ _ p q Z := P.swappedGens_quadEq c L i ν p q Z
  offDiag _ _ _ hij _ _ p q _ hpq := absurd (path_eq_of_ne hij p q) hpq
  quadZero i j ν hij hd _ _ p Z := by
    rw [P.swappedGens_crossCrossNe c L i j ν hij p Z]
    unfold qExpr
    simp only [hd, ↓reduceIte]
    rfl
  quadNe i j ν hij hd _ _ p Z := by
    rw [P.swappedGens_crossCrossNe c L i j ν hij p Z]
    unfold qExpr
    simp only [hd, ↓reduceIte, compPow_eq_pow, End.mul_def]

end Assembly

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
