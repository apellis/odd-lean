/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientCategory

/-!
# The old-cyclotomic ELV target

`DeformedGlobalQP.md` §1 and `DeformedProjectiveResolution.md` §3:
the matrix-Hom components of H e(i,β) / H F₂ R₁(β)e(i,β), over the
signed ELV coefficient category. `insert` fixes the full coefficient algebra
and inserts the moving strand on the left. `ideal` is two-sided only in the
old category; `relations` closes its image under ambient left multiplication
(postcomposition in diagram order), not arbitrary right H multiplication.

`Target`, `projection` and `act` construct the quotient module componentwise,
without finite-colour matrix units. `pair` descends h ⊗ πᵖb ↦ [h ξ(φᵖ(b))]
and satisfies signed balance using total parity, including exterior coefficients.
`insert_elvPolynomial` identifies the old polynomial with F₂, and
`projection_elvPolynomial` proves its vanishing. No moving F₁ relation is imposed.

`ELVOldBalancedTensor` supplies the bundled signed tensor equivalence.
Right PBW coordinates for this coefficient extension, nonvanishing of the
moving polynomial, and all-prefix QP/cancellation remain unproved.
No flatness or cyclotomic freeness is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev obj (v : List I) := elvQuotientObj D Sc cutoff (coefficientObj D Sc v)
abbrev hom (v w : List I) := obj D Sc cutoff v ⟶ obj D Sc cutoff w

def affineInsert (i : I) (v w : List I) :
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k]
    ((pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (i :: w))) where
  toFun f := (pres D Sc).obj (ob D [i]) ◁ f
  map_add' := MonoidalSupercategory.whiskerLeft_add (R := k) _
  map_smul' := MonoidalSupercategory.whiskerLeft_smul (R := k) _

/-- The old algebra inclusion on positions two onwards; coefficients are unchanged. -/
def insert (i : I) (v w : List I) : hom D Sc cutoff v w →ₗ[k]
    hom D Sc cutoff (i :: v) (i :: w) :=
  TensorProduct.map LinearMap.id (affineInsert D Sc i v w)

@[simp] theorem insert_tmul (i : I) {v w : List I}
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    insert D Sc cutoff i v w (a ⊗ₜ[k] f) = a ⊗ₜ[k] affineInsert D Sc i v w f := rfl

private theorem induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

theorem insert_comp (i : I) {v w z : List I}
    (f : hom D Sc cutoff v w) (g : hom D Sc cutoff w z) :
    insert D Sc cutoff i v z (f ≫ g) =
      insert D Sc cutoff i v w f ≫ insert D Sc cutoff i w z g := by
  induction f using induction_hom D Sc cutoff with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add f f' hf hf' => simp only [Preadditive.add_comp, map_add, hf, hf']
  | tmul p q a f ha hf =>
    induction g using induction_hom D Sc cutoff with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add g g' hg hg' => simp only [Preadditive.comp_add, map_add, hg, hg']
    | tmul r s b g hb hg =>
      have hi : affineInsert D Sc i w z g ∈ parity (R := k) _ _ s :=
        MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) hg
      rw [BoxProd.tmulHom_comp_tmulHom ha f b hg, map_zsmul]
      change koszulSign p s • BoxProd.tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: z))
        (a ≫ b) (affineInsert D Sc i v z (f ≫ g)) =
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: w))
          a (affineInsert D Sc i v w f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: w)) (Y := obj D Sc cutoff (i :: z))
          b (affineInsert D Sc i w z g)
      rw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: w))
        (Z := obj D Sc cutoff (i :: z)) ha _ b hi]
      congr 2
      exact MonoidalSupercategory.whiskerLeft_comp (R := k) _ f g

@[simp] theorem insert_id (i : I) (v : List I) :
    insert D Sc cutoff i v v (𝟙 _) = 𝟙 _ := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((pres D Sc).obj (ob D [i]) ◁ 𝟙 ((pres D Sc).obj (ob D v))) = _
  exact congrArg (fun f => (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (MonoidalSupercategory.whiskerLeft_id (R := k) ((pres D Sc).obj (ob D [i]))
      ((pres D Sc).obj (ob D v)))

/-- The actual first-position cyclotomic relation in the finite coefficient category. -/
def relation (j : I) (v : List I) : hom D Sc cutoff (j :: v) (j :: v) :=
  if h : D.parity j = 1 then
    (elvQuotientFunctor D Sc cutoff).map (elvCyclotomic D Sc ⟨j, h⟩ v (cutoff j))
  else (elvQuotientFunctor D Sc cutoff).map (evenCyclotomic D Sc j v (cutoff j))

/-- The two-sided cyclotomic ideal belongs to the OLD category only. -/
def ideal (v w : List I) : Submodule k (hom D Sc cutoff v w) :=
  Submodule.span k {f | ∃ j t,
    ∃ a : hom D Sc cutoff v (j :: t), ∃ b : hom D Sc cutoff (j :: t) w,
      a ≫ relation D Sc cutoff j t ≫ b = f}

/-- Matrix component of H e(i,β) / H F₂ R₁(β)e(i,β).
Only the right factor is old; the final factor is an arbitrary enlarged affine Hom. -/
def relations (i : I) (v w : List I) : Submodule k (hom D Sc cutoff (i :: v) w) :=
  Submodule.span k {f | ∃ t, ∃ r : hom D Sc cutoff v t,
    r ∈ ideal D Sc cutoff v t ∧ ∃ h : hom D Sc cutoff (i :: t) w,
      insert D Sc cutoff i v t r ≫ h = f}

abbrev Target (i : I) (v w : List I) :=
  hom D Sc cutoff (i :: v) w ⧸ relations D Sc cutoff i v w

def projection (i : I) (v w : List I) : hom D Sc cutoff (i :: v) w →ₗ[k]
    Target D Sc cutoff i v w := (relations D Sc cutoff i v w).mkQ

theorem projection_old_ideal (i : I) {v t w : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t)
    (h : hom D Sc cutoff (i :: t) w) :
    projection D Sc cutoff i v w (insert D Sc cutoff i v t r ≫ h) = 0 := by
  change (relations D Sc cutoff i v w).mkQ _ = 0
  exact (Submodule.Quotient.mk_eq_zero (relations D Sc cutoff i v w)).mpr
    (Submodule.subset_span ⟨t, r, hr, h, rfl⟩)


theorem relation_mem (j : I) (t : List I) :
    relation D Sc cutoff j t ∈ ideal D Sc cutoff (j :: t) (j :: t) := by
  apply Submodule.subset_span
  exact ⟨j, t, 𝟙 _, 𝟙 _, by simp⟩

theorem projection_relation (i j : I) (t w : List I)
    (h : hom D Sc cutoff (i :: j :: t) w) :
    projection D Sc cutoff i (j :: t) w
      (insert D Sc cutoff i _ _ (relation D Sc cutoff j t) ≫ h) = 0 :=
  projection_old_ideal D Sc cutoff i (relation_mem D Sc cutoff j t) h

theorem ideal_comp {v t w : List I} {r : hom D Sc cutoff v t}
    (hr : r ∈ ideal D Sc cutoff v t) (b : hom D Sc cutoff t w) :
    r ≫ b ∈ ideal D Sc cutoff v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨j, s, a, c, rfl⟩ := hr
    exact Submodule.subset_span ⟨j, s, a, c ≫ b, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs => exact (by
      rw [Preadditive.add_comp]; exact Submodule.add_mem _ hr hs)
  | smul c r _ hr => exact (by
      rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hr)

theorem comp_ideal {v t w : List I} (a : hom D Sc cutoff v t)
    {r : hom D Sc cutoff t w} (hr : r ∈ ideal D Sc cutoff t w) :
    a ≫ r ∈ ideal D Sc cutoff v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨j, s, b, c, rfl⟩ := hr
    exact Submodule.subset_span ⟨j, s, a ≫ b, c, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs => exact (by
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hr hs)
  | smul c r _ hr => exact (by
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hr)

/-- The ambient action is only on the left (postcomposition in diagram order). -/
theorem relations_comp (i : I) {v t w : List I}
    {r : hom D Sc cutoff (i :: v) t} (hr : r ∈ relations D Sc cutoff i v t)
    (h : hom D Sc cutoff t w) : r ≫ h ∈ relations D Sc cutoff i v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨s, b, hb, a, rfl⟩ := hr
    exact Submodule.subset_span ⟨s, b, hb, a ≫ h, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs => exact (by
      rw [Preadditive.add_comp]; exact Submodule.add_mem _ hr hs)
  | smul c r _ hr => exact (by
      rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hr)

/-- Left H action on the quotient, with no closure under arbitrary right H factors. -/
def act (i : I) {v t w : List I} (h : hom D Sc cutoff t w) :
    Target D Sc cutoff i v t →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v t).mapQ (relations D Sc cutoff i v w)
    (Linear.rightComp k _ h) (fun _ hr => relations_comp D Sc cutoff i hr h)

private theorem dot_pow_mem (w : List I) (r : ℕ) {p : ZMod 2}
    (hp : dotE D Sc w r ∈ parity (R := k) _ _ p) (n : ℕ) :
    (dotE D Sc w r ^ n : End _) ∈ parity (R := k) _ _ (n • p) := by
  induction n with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) _
  | succ n ih => simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using comp_mem hp ih

private theorem polynomial_mem (w : List I) (r N : ℕ) (c : Fin (N + 1) → SKM.SYM D k)
    (p P : ZMod 2) (hp : dotE D Sc w r ∈ parity (R := k) _ _ p)
    (hc : ∀ j, SKM.SYM.polynomialExteriorEquiv D k (c j) ∈
      SKM.SYM.polynomialExteriorParity D k (P - j.val • p)) :
    coefficientDotPolynomial D Sc w r N c ∈ parity (R := k) _ _ P := by
  apply Submodule.sum_mem
  intro j _
  have h := BoxProd.tmul_mem_parity
    (X := coefficientObj D Sc w) (Y := coefficientObj D Sc w)
    (hc j) (dot_pow_mem D Sc w r hp j.val)
  change sourceCoefficientHom D Sc (c j) (dotE D Sc w r ^ j.val) ∈
    parity (R := k) _ _ (P - j.val • p + j.val • p) at h
  rw [sub_add_cancel] at h
  exact h

/-- The entire polynomial has its total parity, including all exterior coefficients. -/
theorem relation_mem_parity (j : I) (v : List I) :
    relation D Sc cutoff j v ∈ parity (R := k) _ _ ((cutoff j : ZMod 2) * D.parity j) := by
  unfold relation
  split_ifs with hj
  · apply elvQuotientMap_mem
    rw [← elvDotPolynomial_first]
    unfold elvDotPolynomial
    rw [hj, mul_one]
    exact polynomial_mem D Sc _ _ _ _ _ _
      (positionedDot_parity D Sc [] v j)
      (SKM.SYM.elvMonicCoefficient_mem_parity D ⟨j, hj⟩ _)
  · have he : D.parity j = 0 := (parity_eq_zero_or_one (D.parity j)).resolve_right hj
    apply elvQuotientMap_mem
    have hpoly : evenCyclotomic D Sc j v (cutoff j) =
        coefficientDotPolynomial D Sc (j :: v) 0 (cutoff j)
          (SKM.SYM.evenMonicCoefficient D k j (cutoff j)) := by
      unfold evenCyclotomic deformedCyclotomic coefficientDotPolynomial
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp only [dotE_pow, firstDotPower, List.map_replicate]
    rw [hpoly, he, mul_zero]
    apply polynomial_mem D Sc _ _ _ _ 0 0
    · have h := positionedDot_parity D Sc [] v j
      rw [he] at h
      exact h
    · intro a
      simp only [nsmul_zero, sub_self, SKM.SYM.evenMonicCoefficient, map_smul]
      apply Submodule.smul_mem
      cases cutoff j - a.val with
      | zero => simpa only [SKM.SYM.evenCyclotomicCoefficient, map_one] using
          (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior D k) ∈
            SKM.SYM.polynomialExteriorParity D k 0)
      | succ n => exact SKM.SYM.polynomialExterior_e_mem_even D k j n

/-- Total parity preserves the old ideal, rather than twisting only its dots. -/
theorem twist_ideal (p : ZMod 2) {v w : List I} {r : hom D Sc cutoff v w}
    (hr : r ∈ ideal D Sc cutoff v w) : twist k p r ∈ ideal D Sc cutoff v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨j, s, a, b, rfl⟩ := hr
    rw [twist_comp, twist_comp, twist_of_mem p (relation_mem_parity D Sc cutoff j s),
      Linear.smul_comp, Linear.comp_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, s, twist k p a, twist k p b, rfl⟩
  | zero => simpa only [map_zero] using (ideal D Sc cutoff v w).zero_mem
  | add r s _ _ hr hs => simpa only [map_add] using Submodule.add_mem _ hr hs
  | smul c r _ hr => simpa only [map_smul] using Submodule.smul_mem _ c hr

abbrev Old (v w : List I) := hom D Sc cutoff v w ⧸ ideal D Sc cutoff v w

/-- The total-parity automorphism on the old cyclotomic quotient. -/
def oldTwist (p : ZMod 2) (v w : List I) : Old D Sc cutoff v w →ₗ[k] Old D Sc cutoff v w :=
  (ideal D Sc cutoff v w).mapQ (ideal D Sc cutoff v w) (twist k p)
    (fun _ hr => twist_ideal D Sc cutoff p hr)

/-- h ⊗ πᵖ[b] maps to [h ξ(φᵖ(b))]. This is the signed balanced quotient map. -/
def pair (p : ZMod 2) (i : I) {v t w : List I} (h : hom D Sc cutoff (i :: t) w) :
    Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v w :=
  (ideal D Sc cutoff v t).liftQ
    ((projection D Sc cutoff i v w).comp
      ((Linear.rightComp k _ h).comp ((insert D Sc cutoff i v t).comp (twist k p))))
    (fun _ hr => projection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff p hr) h)

@[simp] theorem pair_mk (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : hom D Sc cutoff v t) :
    pair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b) =
      projection D Sc cutoff i v w (insert D Sc cutoff i v t (twist k p b) ≫ h) := rfl

/-- Full signed balance, before choosing homogeneous representatives. In algebra order:
h ξ(r) ⊗ πᵖb = h ⊗ πᵖ(φᵖ(r)b). -/
theorem pair_balance (p : ZMod 2) (i : I) {v s t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (r : hom D Sc cutoff s t)
    (b : hom D Sc cutoff v s) :
    pair D Sc cutoff p i (insert D Sc cutoff i s t r ≫ h) ((ideal D Sc cutoff v s).mkQ b) =
      pair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ (b ≫ twist k p r)) := by
  simp only [pair_mk, twist_comp, twist_twist, insert_comp, Category.assoc]

/-- Homogeneous balance uses total degree, not just affine degree. -/
theorem pair_balance_homogeneous (p : ZMod 2) (i : I) {v s t w : List I}
    (h : hom D Sc cutoff (i :: t) w) {r : hom D Sc cutoff s t} {q : ZMod 2}
    (hr : r ∈ parity (R := k) _ _ q) (b : hom D Sc cutoff v s) :
    pair D Sc cutoff p i (insert D Sc cutoff i s t r ≫ h) ((ideal D Sc cutoff v s).mkQ b) =
      sign k (p * q) • pair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ (b ≫ r)) := by
  rw [pair_balance, twist_of_mem p hr, Linear.comp_smul, map_smul, map_smul]

/-- The even-cutoff coefficient relation is already zero before imposing any old polynomial. -/
theorem projection_top (i : I) (v w : List I)
    (j : {j : I // D.parity j = 1}) (he : cutoff j.1 % 2 = 0)
    (f : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D w)) :
    projection D Sc cutoff i v w ((elvQuotientFunctor D Sc cutoff).map
      (sourceCoefficientHom D Sc (SKM.SYM.delta D k j *
        SKM.SYM.elvChi D k j (cutoff j.1 / 2)) f)) = 0 := by
  have hz : (elvQuotientFunctor D Sc cutoff).map
      (sourceCoefficientHom D Sc (SKM.SYM.delta D k j *
        SKM.SYM.elvChi D k j (cutoff j.1 / 2)) f) = 0 :=
    elvQuotientMap_kills D Sc (TwoSidedIdeal.subset_span (Or.inr ⟨j, he, rfl⟩)) f
  exact (congrArg (projection D Sc cutoff i v w) hz).trans (map_zero _)

private theorem affineInsert_dot (i j : I) (v : List I) :
    affineInsert D Sc i (j :: v) (j :: v) (dotE D Sc (j :: v) 0) =
      dotE D Sc (i :: j :: v) 1 := by
  simp [affineInsert, dotE_eq, cl, Presentation.diag_whiskerLeft, pl, PG.ld]
  apply Presentation.diag_eq_of_layers_eq
  simp [mkD, layList, ob, lay, Layer.wl]

private def affineInsertEnd (i : I) (v : List I) :
    End ((pres D Sc).obj (ob D v)) →ₐ[k] End ((pres D Sc).obj (ob D (i :: v))) where
  toFun := affineInsert D Sc i v v
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := MonoidalSupercategory.whiskerLeft_id (R := k)
    ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v))
  map_mul' f g := MonoidalSupercategory.whiskerLeft_comp (R := k) _ g f
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul]
    exact congrArg (c • ·) (MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v)))

private theorem affineInsert_dot_pow (i j : I) (v : List I) (n : ℕ) :
    affineInsert D Sc i (j :: v) (j :: v) (dotE D Sc (j :: v) 0 ^ n) =
      dotE D Sc (i :: j :: v) 1 ^ n := by
  change affineInsertEnd D Sc i (j :: v) (dotE D Sc (j :: v) 0 ^ n) = _
  rw [map_pow]
  have h : affineInsertEnd D Sc i (j :: v) (dotE D Sc (j :: v) 0) =
      dotE D Sc (i :: j :: v) 1 := affineInsert_dot D Sc i j v
  rw [h]

/-- Inclusion of the ELV polynomial is precisely F₂, not F₁. -/
theorem insert_elvPolynomial (i : I) (j : {j : I // D.parity j = 1}) (v : List I) :
    insert D Sc cutoff i _ _ ((elvQuotientFunctor D Sc cutoff).map
      (elvCyclotomic D Sc j v (cutoff j.1))) =
    (elvQuotientFunctor D Sc cutoff).map
      (elvDotPolynomial D Sc j (i :: j.1 :: v) 1 (cutoff j.1)) := by
  rw [← elvDotPolynomial_first]
  change insert D Sc cutoff i _ _ (elvQuotientMap D Sc cutoff _ _
    (elvDotPolynomial D Sc j (j.1 :: v) 0 (cutoff j.1))) =
    elvQuotientMap D Sc cutoff _ _ (elvDotPolynomial D Sc j (i :: j.1 :: v) 1 (cutoff j.1))
  unfold elvDotPolynomial coefficientDotPolynomial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [elvQuotientMap_source, elvQuotientMap_source, insert_tmul,
    affineInsert_dot_pow]

/-- The concrete full old ELV polynomial kills every ambient continuation. -/
theorem projection_elvPolynomial (i : I) (j : {j : I // D.parity j = 1})
    (v w : List I) (h : hom D Sc cutoff (i :: j.1 :: v) w) :
    projection D Sc cutoff i (j.1 :: v) w
      ((elvQuotientFunctor D Sc cutoff).map
        (elvDotPolynomial D Sc j (i :: j.1 :: v) 1 (cutoff j.1)) ≫ h) = 0 := by
  rw [← insert_elvPolynomial]
  have hr : relation D Sc cutoff j.1 v = (elvQuotientFunctor D Sc cutoff).map
      (elvCyclotomic D Sc j v (cutoff j.1)) := by simp only [relation, dite_eq_left j.property]
  rw [← hr]
  exact projection_relation D Sc cutoff i j.1 v w h

/-- Every quotient class is the signed pairing with the old identity class. -/
theorem pair_id (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    pair D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) =
      projection D Sc cutoff i v w h := by
  rw [pair_mk, twist_id, insert_id, Category.id_comp]

/-- The quotient projection is surjective, with no flatness hypothesis. -/
theorem projection_surjective (i : I) (v w : List I) :
    Function.Surjective (projection D Sc cutoff i v w) := Submodule.mkQ_surjective _

@[simp] theorem act_projection (i : I) {v t w : List I}
    (h : hom D Sc cutoff t w) (x : hom D Sc cutoff (i :: v) t) :
    act D Sc cutoff i h (projection D Sc cutoff i v t x) =
      projection D Sc cutoff i v w (x ≫ h) := rfl

theorem act_id (i : I) {v w : List I} (x : Target D Sc cutoff i v w) :
    act D Sc cutoff i (𝟙 _) x = x := by
  obtain ⟨x, rfl⟩ := projection_surjective D Sc cutoff i v w x
  rw [act_projection, Category.comp_id]

theorem act_comp (i : I) {v s t w : List I} (f : hom D Sc cutoff s t)
    (g : hom D Sc cutoff t w) (x : Target D Sc cutoff i v s) :
    act D Sc cutoff i g (act D Sc cutoff i f x) = act D Sc cutoff i (f ≫ g) x := by
  obtain ⟨x, rfl⟩ := projection_surjective D Sc cutoff i v s x
  simp only [act_projection, Category.assoc]

theorem oldTwist_twice (p : ZMod 2) (v w : List I) (b : Old D Sc cutoff v w) :
    oldTwist D Sc cutoff p v w (oldTwist D Sc cutoff p v w b) = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective b
  change (ideal D Sc cutoff v w).mkQ (twist k p (twist k p b)) = _
  rw [twist_twist]

/-- No additional quotient is hidden in the projection. -/
theorem projection_eq_zero_iff (i : I) (v w : List I) (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w h = 0 ↔ h ∈ relations D Sc cutoff i v w :=
  Submodule.Quotient.mk_eq_zero _

end OddMath.QuiverHecke.ELVOld
