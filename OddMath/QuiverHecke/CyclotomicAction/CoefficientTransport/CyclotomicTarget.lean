import Mathlib.Algebra.DirectSum.Module
import OddMath.QuiverHecke.CyclotomicAction.CoefficientTransport.CoefficientPolynomialTransport

/-!
# Coefficient transport

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

`ELVBalancedTensor` supplies the bundled signed tensor equivalence.
Right PBW coordinates for this coefficient extension, nonvanishing of the
moving polynomial, and all-prefix QP/cancellation remain unproved.
No flatness or cyclotomic freeness is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# The signed balanced tensor for the old ELV quotient

The quotient comparison of `DeformedGlobalQP.md` §1, with the full exterior
coefficient algebra. The tensor is the coend of the coefficient-category
Homs with the old cyclotomic quotient. Its balance twists the old action by
total parity. `balancedEquiv` identifies it with `ELV.Target`, by pairing
and insertion of the old identity class, without flatness assumptions.
This is the quotient comparison needed for right PBW coordinates; those
coordinates and moving-polynomial cancellation are not asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The old quotient action, twisted on the acting morphism by total parity. -/
def oldCompose (p : ZMod 2) {v s t : List I} (r : hom D Sc cutoff s t) :
    Old D Sc cutoff v s →ₗ[k] Old D Sc cutoff v t :=
  (ideal D Sc cutoff v s).mapQ (ideal D Sc cutoff v t)
    (Linear.rightComp k _ (twist k p r))
    (fun _ hb => ideal_comp D Sc cutoff hb _)

@[simp] theorem oldCompose_mk (p : ZMod 2) {v s t : List I}
    (r : hom D Sc cutoff s t) (b : hom D Sc cutoff v s) :
    oldCompose D Sc cutoff p r ((ideal D Sc cutoff v s).mkQ b) =
      (ideal D Sc cutoff v t).mkQ (b ≫ twist k p r) := rfl

/-- Ordinary module tensors, indexed by the intermediate old word. -/
abbrev TensorSum (i : I) (v w : List I) :=
  ⨁ t : List I, hom D Sc cutoff (i :: t) w ⊗[k] Old D Sc cutoff v t

/-- A pure tensor in the summand specified by its old intermediate word. -/
def tensorIn (i : I) {v t w : List I} (h : hom D Sc cutoff (i :: t) w)
    (b : Old D Sc cutoff v t) : TensorSum D Sc cutoff i v w :=
  DirectSum.lof k (List I) (fun t => hom D Sc cutoff (i :: t) w ⊗[k]
    Old D Sc cutoff v t) t (h ⊗ₜ[k] b)

/-- Only old-category balance is imposed, with the prescribed total-parity twist. -/
def balanceRelations (p : ZMod 2) (i : I) (v w : List I) :
    Submodule k (TensorSum D Sc cutoff i v w) :=
  Submodule.span k {z | ∃ s t, ∃ h : hom D Sc cutoff (i :: t) w,
    ∃ r : hom D Sc cutoff s t, ∃ b : Old D Sc cutoff v s,
      tensorIn D Sc cutoff i (insert D Sc cutoff i s t r ≫ h) b -
        tensorIn D Sc cutoff i h (oldCompose D Sc cutoff p r b) = z}

/-- The balanced tensor with the full old ELV coefficient module. -/
abbrev BalancedTensor (p : ZMod 2) (i : I) (v w : List I) :=
  TensorSum D Sc cutoff i v w ⧸ balanceRelations D Sc cutoff p i v w

def balancedTmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ (tensorIn D Sc cutoff i h b)

theorem balancedTmul_balance (p : ZMod 2) (i : I) {v s t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (r : hom D Sc cutoff s t)
    (b : Old D Sc cutoff v s) :
    balancedTmul D Sc cutoff p i (insert D Sc cutoff i s t r ≫ h) b =
      balancedTmul D Sc cutoff p i h (oldCompose D Sc cutoff p r b) := by
  apply sub_eq_zero.mp
  rw [balancedTmul, balancedTmul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨s, t, h, r, b, rfl⟩)

private def pairBilinear (p : ZMod 2) (i : I) (v t w : List I) :
    hom D Sc cutoff (i :: t) w →ₗ[k]
      Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v w where
  toFun := pair D Sc cutoff p i
  map_add' h h' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [LinearMap.add_apply, pair_mk, Preadditive.comp_add, map_add]
  map_smul' c h := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [LinearMap.smul_apply, pair_mk, Linear.comp_smul, map_smul,
      RingHom.id_apply]

private def tensorSumPair (p : ZMod 2) (i : I) (v w : List I) :
    TensorSum D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  DirectSum.toModule k (List I) _
    (fun t => TensorProduct.lift (pairBilinear D Sc cutoff p i v t w))

private theorem tensorSumPair_in (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    tensorSumPair D Sc cutoff p i v w (tensorIn D Sc cutoff i h b) =
      pair D Sc cutoff p i h b := by
  simp [tensorSumPair, tensorIn, pairBilinear]

/-- The pairing descends through the signed old-category balance relations. -/
def balancedForward (p : ZMod 2) (i : I) (v w : List I) :
    BalancedTensor D Sc cutoff p i v w →ₗ[k] Target D Sc cutoff i v w :=
  (balanceRelations D Sc cutoff p i v w).liftQ (tensorSumPair D Sc cutoff p i v w) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, t, h, r, b, rfl⟩
    change tensorSumPair D Sc cutoff p i v w _ = 0
    rw [map_sub, tensorSumPair_in, tensorSumPair_in, sub_eq_zero]
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v s).mkQ_surjective b
    exact pair_balance D Sc cutoff p i h r b)

@[simp] theorem balancedForward_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    balancedForward D Sc cutoff p i v w (balancedTmul D Sc cutoff p i h b) =
      pair D Sc cutoff p i h b := tensorSumPair_in D Sc cutoff p i h b

private def identityTensor (p : ZMod 2) (i : I) (v w : List I) :
    hom D Sc cutoff (i :: v) w →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ.comp
    ((DirectSum.lof k (List I) _ v).comp
      ((TensorProduct.mk k _ _).flip ((ideal D Sc cutoff v v).mkQ (𝟙 _))))

private theorem identityTensor_in (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    identityTensor D Sc cutoff p i v w h =
      balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) := rfl

private theorem identityTensor_kills (p : ZMod 2) (i : I) (v w : List I) :
    relations D Sc cutoff i v w ≤ LinearMap.ker (identityTensor D Sc cutoff p i v w) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, r, hr, h, rfl⟩
  change identityTensor D Sc cutoff p i v w _ = 0
  rw [identityTensor_in, balancedTmul_balance, oldCompose_mk, Category.id_comp]
  have hz : (ideal D Sc cutoff v t).mkQ (twist k p r) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (twist_ideal D Sc cutoff p hr)
  rw [hz]
  simp [balancedTmul, tensorIn]

/-- The inverse inserts the old identity class; only the old ideal is killed. -/
def balancedBackward (p : ZMod 2) (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (relations D Sc cutoff i v w).liftQ (identityTensor D Sc cutoff p i v w)
    (identityTensor_kills D Sc cutoff p i v w)

@[simp] theorem balancedBackward_projection (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    balancedBackward D Sc cutoff p i v w (projection D Sc cutoff i v w h) =
      balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) := rfl

theorem balancedForward_backward (p : ZMod 2) (i : I) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    balancedForward D Sc cutoff p i v w (balancedBackward D Sc cutoff p i v w z) = z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  rw [balancedBackward_projection, balancedForward_tmul, pair_id]

private theorem backward_forward_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    balancedBackward D Sc cutoff p i v w
      (balancedForward D Sc cutoff p i v w (balancedTmul D Sc cutoff p i h b)) =
        balancedTmul D Sc cutoff p i h b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [balancedForward_tmul, pair_mk, balancedBackward_projection,
    balancedTmul_balance, oldCompose_mk, Category.id_comp, twist_twist]

theorem balancedBackward_forward (p : ZMod 2) (i : I) (v w : List I)
    (z : BalancedTensor D Sc cutoff p i v w) :
    balancedBackward D Sc cutoff p i v w (balancedForward D Sc cutoff p i v w z) = z := by
  obtain ⟨z, rfl⟩ := (balanceRelations D Sc cutoff p i v w).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of t z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul h b => exact backward_forward_tmul D Sc cutoff p i h b

/-- The full-coefficient signed balanced tensor is the old-only cyclotomic target.
No independence or tensor comparison is assumed. -/
def balancedEquiv (p : ZMod 2) (i : I) (v w : List I) :
    BalancedTensor D Sc cutoff p i v w ≃ₗ[k] Target D Sc cutoff i v w :=
  LinearEquiv.ofLinearMap (balancedForward D Sc cutoff p i v w)
    (balancedBackward D Sc cutoff p i v w)
    (LinearMap.ext (balancedForward_backward D Sc cutoff p i v w))
    (LinearMap.ext (balancedBackward_forward D Sc cutoff p i v w))

@[simp] theorem balancedEquiv_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : hom D Sc cutoff v t) :
    balancedEquiv D Sc cutoff p i v w
      (balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b)) =
        projection D Sc cutoff i v w (insert D Sc cutoff i v t (twist k p b) ≫ h) :=
  balancedForward_tmul D Sc cutoff p i h _

end OddMath.QuiverHecke.ELV
end

end
