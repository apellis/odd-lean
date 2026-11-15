import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails
import OddMath.QuiverHecke.CyclotomicAction.OutputTransport
import OddMath.QuiverHecke.CyclotomicAction.LeadingSourceTransport
import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CentreFinite
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwiner
import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.ParabolicTransport
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerAnnihilation
import OddMath.QuiverHecke.HalfTurn.CoefficientGenerators
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction

/-!
# Append source rows

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Prescribed source and polynomial long coordinates

The source step of `DeformedMackeyBoundary.md` identifies the range of the
prescribed epsilon-balanced column with the chronological short span. On the
diagonal output this is the kernel of every normalized long extraction.
`sourceCoordinateEquiv` uses the existing decoder and a corrected PBW section,
not an independently chosen complement or an injectivity hypothesis.
The result is ground-ring linear; bimodule and categorical naturality are separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem range_alpha_eq_chronologicalShortSpan (i : I) (v t : List I) :
    LinearMap.range (alpha D Sc cutoff i v t) = chronologicalShortSpan D Sc cutoff i v t := by
  apply le_antisymm
  · have hz : (chronologicalShortSpan D Sc cutoff i v t).mkQ ∘ₗ
        alpha D Sc cutoff i v t = 0 := by
      apply BalancedInduction.hom_ext
      intro s h b
      change (chronologicalShortSpan D Sc cutoff i v t).mkQ
        (alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b)) = 0
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
      rw [alpha_tensor, alphaPair_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.subset_span ⟨s.word, twist k (epsilon D cutoff i v) r, h, rfl⟩
    rintro z ⟨a, rfl⟩
    have h := LinearMap.congr_fun hz a
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · apply Submodule.span_le.mpr
    rintro z ⟨s, r, h, rfl⟩
    refine ⟨pprimeTensor D Sc cutoff i v s t h
      ((ideal D Sc cutoff v (s ++ [i])).mkQ (twist k (epsilon D cutoff i v) r)), ?_⟩
    rw [alpha_tensor, alphaPair_mk, twist_twist]

theorem ker_outputLongExtraction_eq_range_alpha (p : ZMod 2) (i : I) (v : List I) :
    LinearMap.ker (outputLongExtraction D Sc cutoff p i v) =
      LinearMap.range (alpha D Sc cutoff i v v) := by
  rw [ker_outputLongExtraction_eq_chronologicalShortSpan, range_alpha_eq_chronologicalShortSpan]

@[simp] theorem outputLongExtraction_alpha (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) :
    outputLongExtraction D Sc cutoff p i v (alpha D Sc cutoff i v v a) = 0 := by
  have h : alpha D Sc cutoff i v v a ∈ LinearMap.range (alpha D Sc cutoff i v v) := ⟨a, rfl⟩
  rw [← ker_outputLongExtraction_eq_range_alpha D Sc cutoff p i v] at h
  exact h

/-- The existing long lift corrected by its prescribed short-source coordinate. -/
def sourceLongSection (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  outputLongSection D Sc cutoff p i v -
    alpha D Sc cutoff i v v ∘ₗ extract D Sc cutoff i v v ∘ₗ outputLongSection D Sc cutoff p i v

@[simp] theorem extract_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    extract D Sc cutoff i v v (sourceLongSection D Sc cutoff p i v f) = 0 := by
  simp only [sourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    extract_alpha, sub_self]

@[simp] theorem outputLongExtraction_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v (sourceLongSection D Sc cutoff p i v f) = f := by
  simp only [sourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    outputLongExtraction_alpha, outputLongExtraction_section, sub_zero]

theorem source_reconstruction (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    alpha D Sc cutoff i v v (extract D Sc cutoff i v v z) +
      sourceLongSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z) = z := by
  have hz : z - sourceLongSection D Sc cutoff p i v
      (outputLongExtraction D Sc cutoff p i v z) ∈
      LinearMap.ker (outputLongExtraction D Sc cutoff p i v) := by
    simp only [LinearMap.mem_ker, map_sub, outputLongExtraction_sourceLongSection, sub_self]
  rw [ker_outputLongExtraction_eq_range_alpha] at hz
  obtain ⟨a, ha⟩ := hz
  have he := congrArg (extract D Sc cutoff i v v) ha
  simp only [extract_alpha, map_sub, extract_sourceLongSection, sub_zero] at he
  rw [← he, ha]
  exact sub_add_cancel _ _

/-- Coordinates in the prescribed balanced source and the existing polynomial old module. -/
def sourceCoordinateEquiv (p : ZMod 2) (i : I) (v : List I) :
    Target D Sc cutoff i v (v ++ [i]) ≃ₗ[k]
      (PprimeDomain D Sc cutoff i v v × (ℕ →₀ Old D Sc cutoff v v)) where
  toLinearMap := (extract D Sc cutoff i v v).prod (outputLongExtraction D Sc cutoff p i v)
  invFun a := alpha D Sc cutoff i v v a.1 + sourceLongSection D Sc cutoff p i v a.2
  left_inv := source_reconstruction D Sc cutoff p i v
  right_inv a := by
    apply Prod.ext
    · change extract D Sc cutoff i v v (_ + _) = a.1
      simp only [map_add, extract_alpha, extract_sourceLongSection, add_zero]
    · change outputLongExtraction D Sc cutoff p i v (_ + _) = a.2
      simp only [map_add, outputLongExtraction_alpha,
        outputLongExtraction_sourceLongSection, zero_add]

@[simp] theorem sourceCoordinateEquiv_apply (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    sourceCoordinateEquiv D Sc cutoff p i v z =
      (extract D Sc cutoff i v v z, outputLongExtraction D Sc cutoff p i v z) := rfl

@[simp] theorem sourceCoordinateEquiv_symm_apply (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    (sourceCoordinateEquiv D Sc cutoff p i v).symm (a, f) =
      alpha D Sc cutoff i v v a + sourceLongSection D Sc cutoff p i v f := rfl

@[simp] theorem sourceCoordinateEquiv_alpha (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) :
    sourceCoordinateEquiv D Sc cutoff p i v (alpha D Sc cutoff i v v a) = (a, 0) := by
  simp only [sourceCoordinateEquiv_apply, extract_alpha, outputLongExtraction_alpha]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-!
# The independent ordered-product boundary coefficients

The polynomial below is defined by the independent ordered-product choices,
not by an extractor. The genuine source expansion and termwise transport identify
its coefficients with output extraction, with the library's fixed global sign.
This is the fixed-word polynomial comparison for `DeformedBoundaryDivision.md`
§§1, 4 in the library crossing convention of `MackeyCrossingConventions.md`.
It is not the corrected-rho iterate comparison, boundary division or prescribed inverse.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The signed independent ordered-product coefficient row. -/
def orderedOutputCoefficients (i : I) (v : List I) : ℕ →₀ Old D Sc cutoff v v :=
  ∑ c : MoveChoices v, leadingMoveCoeff D (k := k) i v c •
    Finsupp.single (sourceMovingDegree (leadingSourceDots D i 0 0 v c))
      ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c))

/-- The unsigned ordered S polynomial, specified by explicit independent
monomials and coefficients. The global sign removes the signed local factors. -/
def independentOutputS (i : I) (v : List I) : ℕ →₀ Old D Sc cutoff v v :=
  SKM.zsign k (D.parity i) ^ v.count i • orderedOutputCoefficients D Sc cutoff i v

/-- Fully explicit independent coefficient formula. The finite choices and old
dot monomials come from the ordered square product, not from extraction. -/
theorem independentOutputS_apply (i : I) (v : List I) (n : ℕ) :
    independentOutputS D Sc cutoff i v n =
      SKM.zsign k (D.parity i) ^ v.count i •
        ∑ c : MoveChoices v,
          if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
            leadingMoveCoeff D (k := k) i v c •
              (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
          else 0 := by
  simp only [independentOutputS, orderedOutputCoefficients, Finsupp.smul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

private theorem global_sign_square (i : I) (v : List I) :
    (SKM.zsign k (D.parity i) ^ v.count i) *
      (SKM.zsign k (D.parity i) ^ v.count i) = 1 := by
  rw [← mul_pow]
  by_cases hi : D.parity i = 1 <;> simp [SKM.zsign, hi]

/-- Extraction of the independent source expansion, evaluated term by term. -/
theorem outputLongExtraction_source_expansion (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          ((∑ c : MoveChoices v, leadingMoveCoeff D (k := k) i v c •
            endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c)) ≫
            OutputOldComposite.bareU D Sc i v))) =
      orderedOutputCoefficients D Sc cutoff i v := by
  simp only [Preadditive.sum_comp, Linear.smul_comp, map_sum, map_smul,
    leading_source_output_extraction, orderedOutputCoefficients]

/-- The independent unsigned ordered square product extracts to the explicit S
coefficient row; S is not defined by this equation. -/
theorem outputLongExtraction_squareProduct (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (leadingMoveSquareProduct D Sc i [] v ≫ OutputOldComposite.bareU D Sc i v))) =
      independentOutputS D Sc cutoff i v := by
  have h := outputLongExtraction_source_expansion D Sc cutoff p i v
  rw [leadingSource_expansion_eq_sign_smul] at h
  change outputLongExtraction D Sc cutoff p i v
    (projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        ((SKM.zsign k (D.parity i) ^ v.count i • leadingMoveSquareProduct D Sc i [] v) ≫
          OutputOldComposite.bareU D Sc i v))) = _ at h
  rw [Linear.smul_comp, map_smul, map_smul, map_smul] at h
  rw [independentOutputS, ← h, smul_smul, global_sign_square, one_smul]

/-- The actual moving intertwiner extracts to the independent S polynomial with
the fixed global library sign, for arbitrary words and both moving parities. -/
theorem outputLongExtraction_move_independentS (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v))) =
      SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v := by
  have h := outputLongExtraction_move_endpointPolynomial D Sc cutoff p i v 1
  change outputLongExtraction D Sc cutoff p i v
    (projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v))) =
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (leadingMoveEndpointPolynomial D Sc i [] v ≫ OutputOldComposite.bareU D Sc i v))) at h
  rw [h, leadingMoveEndpointPolynomial_eq_sign_smul_squareProduct,
    Linear.smul_comp, map_smul, map_smul, map_smul, outputLongExtraction_squareProduct]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Signed QP polynomial transport to the append endpoint

`qpProduct_comp_moveHom` transports the independently evaluated ordered product
through the moving chain. This supplies the polynomial comparison needed for
`DeformedBoundaryDivision.md` §3; it is not the full chain norm or boundary S.
The library crossing normalization retains the repeated-even factor −1.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The signed QP polynomial at the append endpoint, distinct from the chain norm. -/
def appendQPFactor (i : I) (v : List I) (j : I) (b : ℕ) :
    End ((pres D Sc).obj (ob D (v ++ [i]))) :=
  if j = i then
    if D.parity i = 1 then
      (dotE D Sc (v ++ [i]) b - dotE D Sc (v ++ [i]) v.length) ^ 2
    else -1
  else qPoly D Sc (dotE D Sc (v ++ [i]) v.length) (dotE D Sc (v ++ [i]) b) i j

def appendQPProduct (i : I) (v : List I) : End ((pres D Sc).obj (ob D (v ++ [i]))) :=
  ((List.range v.length).map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod

private theorem split_getD (v : List I) (i : I) (b : ℕ) (hb : b < v.length) :
    v = v.take b ++ [v.getD b i] ++ v.drop (b + 1) := by
  induction v generalizing b with
  | nil => simp at hb
  | cons x v ih =>
    cases b with
    | zero => simp
    | succ b => simpa using congrArg (List.cons x) (ih b (by simpa using hb))

theorem dot_getD_comp_moveHom (i : I) (v : List I) (b : ℕ) (hb : b < v.length) :
    dotE D Sc (i :: v) (b + 1) ≫ moveHom D Sc i [] v =
      SKM.zsign k (D.parity (v.getD b i) * (D.parity i * wordSumParity D v)) •
        (moveHom D Sc i [] v ≫ dotE D Sc (v ++ [i]) b) := by
  have h := dot_mem_comp_moveHom D Sc i (v.getD b i) (v.drop (b + 1)) (v.take b)
    [] v (split_getD v i b hb)
  simpa only [List.nil_append, List.length_nil, zero_add, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hb), Nat.add_comm 1 b] using h

theorem qpFactor_comp_moveHom (i : I) (v : List I) (b : ℕ) (hb : b < v.length) :
    qpFactor D Sc i v (v.getD b i) b ≫ moveHom D Sc i [] v =
      moveHom D Sc i [] v ≫ appendQPFactor D Sc i v (v.getD b i) b := by
  have hm := dot_comp_moveHom D Sc i [] v
  simp only [List.nil_append, List.length_nil, zero_add] at hm
  have ho := dot_getD_comp_moveHom D Sc i v b hb
  have hm' := congrArg (SKM.zsign k (D.parity i * wordSumParity D v) • ·) hm
  have ho' := congrArg (SKM.zsign k (D.parity (v.getD b i) *
    (D.parity i * wordSumParity D v)) • ·) ho
  simp only [smul_smul, zsign_mul_self, one_smul] at hm' ho'
  unfold qpFactor appendQPFactor
  split_ifs with hj hp
  · rw [hj, hp, one_mul] at ho'
    have hs : moveHom D Sc i [] v ≫
        (dotE D Sc (v ++ [i]) b - dotE D Sc (v ++ [i]) v.length : End _) =
        SKM.zsign k (D.parity i * wordSumParity D v) •
          ((dotE D Sc (i :: v) (b + 1) - dotE D Sc (i :: v) 0 : End _) ≫
            moveHom D Sc i [] v) := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, smul_sub, ← ho', ← hm', hp]
    have he := comp_pow_of_signed _ _ _ _ hs 2
    simpa only [pow_two (SKM.zsign k _), zsign_mul_self, one_smul] using he.symm
  · change (- (𝟙 _) : _ ⟶ _) ≫ _ = _ ≫ (- (𝟙 _) : _ ⟶ _)
    rw [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
  · symm
    apply comp_qPoly D Sc _ _ _ _ _ i (v.getD b i)
      (SKM.zsign k (D.parity i * wordSumParity D v))
      (SKM.zsign k (D.parity (v.getD b i) * (D.parity i * wordSumParity D v)))
      hm'.symm ho'.symm
    · intro n hn
      apply zsign_pow_eq_one
      rw [← mul_assoc, hn, zero_mul]
    · intro n hn
      apply zsign_pow_eq_one
      rw [← mul_assoc, hn, zero_mul]

theorem qpProduct_comp_moveHom (i : I) (v : List I) :
    qpProduct D Sc i v ≫ moveHom D Sc i [] v =
      moveHom D Sc i [] v ≫ appendQPProduct D Sc i v := by
  unfold qpProduct appendQPProduct
  have h (l : List ℕ) (hl : ∀ b ∈ l, b < v.length) :
      (l.map fun b => qpFactor D Sc i v (v.getD b i) b).prod ≫ moveHom D Sc i [] v =
        moveHom D Sc i [] v ≫ (l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod := by
    induction l with
    | nil =>
      change (𝟙 _ : _ ⟶ _) ≫ _ = _ ≫ (𝟙 _ : _ ⟶ _)
      rw [Category.id_comp, Category.comp_id]
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons, End.mul_def, Category.assoc]
      rw [qpFactor_comp_moveHom D Sc i v b (hl b (by simp)),
        ← Category.assoc, ih (fun c hc => hl c (by simp [hc])), Category.assoc]
  exact h _ (fun b hb => List.mem_range.mp hb)
/-- The repeated-odd QP factor has positive unit highest moving coefficient.
The mixed terms cancel by the actual disjoint-dot super interchange. -/
theorem appendQPFactor_odd (i : I) (hi : D.parity i = 1) (v : List I)
    (b : ℕ) (hb : b < v.length) (hx : v.getD b i = i) :
    appendQPFactor D Sc i v i b =
      dotE D Sc (v ++ [i]) b ^ 2 + dotE D Sc (v ++ [i]) v.length ^ 2 := by
  have hs : v = v.take b ++ [i] ++ v.drop (b + 1) := by
    simpa only [hx] using split_getD v i b hb
  have ht := genE_interchange D Sc (w := v ++ [i])
    (v.take b) (v.drop (b + 1)) [] (.dot i) (.dot i) rfl rfl
    (by simpa only [Shape.dom, List.append_nil] using congrArg (· ++ [i]) hs)
    (p := b) (q := v.length)
    (by simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hb)])
    (by exact congrArg List.length hs.symm)
  change dotE D Sc (v ++ [i]) v.length * dotE D Sc (v ++ [i]) b =
    SKM.zsign k (D.parity i * D.parity i) •
      (dotE D Sc (v ++ [i]) b * dotE D Sc (v ++ [i]) v.length) at ht
  simp only [hi, one_mul, SKM.zsign, ite_eq_left, neg_one_smul] at ht
  rw [appendQPFactor, ite_eq_left rfl, ite_eq_left hi, pow_two, sub_mul, mul_sub, mul_sub, ht]
  noncomm_ring

end OddMath.QuiverHecke
end

end

section

/-! # Common-source rows for the prepend endpoint

The reconstruction maps below use representable old rows, rather than separate
scalar coordinates at each old source. Their naturality includes arbitrary
word-to-word old arrows and retains the total parity twist in `pair`.
The intended application is the source endpoint of the deformed square resolution.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Absorbing the prescribed twist into `pair` leaves ordinary old composition
on coefficients, even for off-diagonal arrows and inhomogeneous coefficients. -/
theorem sourcePull_pair (p : ZMod 2) (i : I) {u v t w : List I}
    (c : Old D Sc cutoff u v) (h : hom D Sc cutoff (i :: t) w)
    (b : Old D Sc cutoff v t) :
    sourcePull D Sc cutoff p i u v w c (pair D Sc cutoff p i h b) =
      pair D Sc cutoff p i h (oldComp D Sc cutoff u v t c b) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  simp only [pair_mk, sourcePull_mk, oldComp_mk, twist_comp, insert_comp,
    Category.assoc]

/-- The representable old presheaf at an arbitrary target word. -/
def oldRowPresheaf (t : List I) : (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Old D Sc cutoff v.unop.word t)
  map f := ModuleCat.ofHom (oldComp D Sc cutoff _ _ t f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact Category.id_comp (X := (⟨v.unop.word⟩ : OldCategory D Sc cutoff))
      (Y := ⟨t⟩) b
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact Category.assoc (Z := (⟨t⟩ : OldCategory D Sc cutoff)) g.unop f.unop b

instance oldRowPresheaf_additive (t : List I) :
    (oldRowPresheaf D Sc cutoff t).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (oldComp D Sc cutoff _ _ t).map_add f.unop g.unop

/-- All old columns of a single representable old row. No corner is assumed nonzero. -/
abbrev OldContentRow (ν t : List I) :=
  OddMath.FiniteHomMatrix.RightModule (contentObject D Sc cutoff ν)
    (oldRowPresheaf D Sc cutoff t)

/-- A fixed positioned tail is a natural transformation from its representable row. -/
def sourcePairNat (p : ZMod 2) (i : I) {t w : List I}
    (h : hom D Sc cutoff (i :: t) w) :
    oldRowPresheaf D Sc cutoff t ⟶ sourcePresheaf D Sc cutoff p i w where
  app v := ModuleCat.ofHom (pair D Sc cutoff p i h)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (sourcePull_pair D Sc cutoff p i f.unop h z).symm

/-- Right-old-ring-linear reconstruction along a common positioned tail. -/
def sourcePairRow (p : ZMod 2) (i : I) (ν : List I) {t w : List I}
    (h : hom D Sc cutoff (i :: t) w) :
    OldContentRow D Sc cutoff ν t →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceRow D Sc cutoff p i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (sourcePairNat D Sc cutoff p i h)

@[simp] theorem sourcePairRow_apply (p : ZMod 2) (i : I) (ν : List I)
    {t w : List I} (h : hom D Sc cutoff (i :: t) w)
    (b : OldContentRow D Sc cutoff ν t) (v : ContentWords ν) :
    sourcePairRow D Sc cutoff p i ν h b v = pair D Sc cutoff p i h (b v) := rfl

/-- The finite part of the common tail index: an old target and an input shuffle. -/
abbrev SourceTailIndex (ν : List I) := Σ t : ContentWords ν, PrependShuffle t.val.length

instance sourceTailIndexFintype (ν : List I) : Fintype (SourceTailIndex ν) := inferInstance

/-- The ambient word is determined by the old target and shuffle, not the old source. -/
def sourceTailWord (i : I) {ν : List I} (q : SourceTailIndex ν) : ContentWords (i :: ν) :=
  ⟨tgt (i :: q.1.val)
      (cw (Categorification.TypeA.canWord (q.1.val.length + 1) q.2.val⁻¹)),
    (tgt_perm _ _).trans (q.1.property.cons i)⟩

private theorem source_canWord_one (n : ℕ) : Categorification.TypeA.canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]

/-- A common tail represented with the identity old normal form. -/
def sourceTailPBW (i : I) {ν : List I} (q : SourceTailIndex ν) (m : ℕ) :
    PrependIdx i q.1.val (sourceTailWord i q).val :=
  ⟨(m, [], 1, q.2), by simp, by simp, by
    simp [prependCrossingWord, source_canWord_one, cw, sourceTailWord,
      Categorification.TypeA.shiftWord]⟩

@[simp] theorem sourceTailPBW_oldTarget (i : I) {ν : List I}
    (q : SourceTailIndex ν) (m : ℕ) : (sourceTailPBW i q m).oldTarget = q.1.val := by
  simp [sourceTailPBW, PrependIdx.oldTarget, source_canWord_one, cw]

/-- The common tail, with its old target independent of the coefficient's source. -/
def sourceTail (i : I) {ν : List I} (q : SourceTailIndex ν) (m : ℕ) :
    hom D Sc cutoff (i :: q.1.val) (sourceTailWord i q).val :=
  sourceTailPBW_oldTarget i q m ▸
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      prependTail D Sc (sourceTailPBW i q m))

/-- Embed one representable old row along a common tail into all ambient rows. -/
def sourceTailRow (p : ZMod 2) (i : I) (ν : List I) (q : SourceTailIndex ν) (m : ℕ) :
    OldContentRow D Sc cutoff ν q.1.val →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceContent D Sc cutoff p i ν :=
  (LinearMap.single (R := (ContentRing D Sc cutoff ν)ᵐᵒᵖ)
    (φ := fun w : ContentWords (i :: ν) => SourceRow D Sc cutoff p i ν w.val)
    (sourceTailWord i q)).comp
      (sourcePairRow D Sc cutoff p i ν (sourceTail D Sc cutoff i q m))

/-- Finitely supported common tails, each carrying an entire old idempotent row. -/
abbrev SourceRows (ν : List I) :=
  ⨁ q : SourceTailIndex ν × ℕ, OldContentRow D Sc cutoff ν q.1.1.val

/-- Actual common-source reconstruction; the scalar ring is the full old content ring. -/
def sourceRowsReconstruct (p : ZMod 2) (i : I) (ν : List I) :
    SourceRows D Sc cutoff ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceContent D Sc cutoff p i ν :=
  DirectSum.toModule _ _ _ fun q => sourceTailRow D Sc cutoff p i ν q.1 q.2

@[simp] theorem sourceRowsReconstruct_lof (p : ZMod 2) (i : I) (ν : List I)
    (q : SourceTailIndex ν × ℕ) (b : OldContentRow D Sc cutoff ν q.1.1.val) :
    sourceRowsReconstruct D Sc cutoff p i ν (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b) =
      sourceTailRow D Sc cutoff p i ν q.1 q.2 b :=
  DirectSum.toModule_lof _ _ _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Common old rows for the append endpoint

The old-only append quotient is reconstructed from representable old rows.
Naturality includes all word-to-word old arrows. The append action is untwisted,
so its reconstruction uses `appendPair` at parity zero; the signed ELV tensor
composition and the old cyclotomic quotient are unchanged. These rows supply
coordinates for the underlying old-ring module of K₀ in the deformed square.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Untwisted old precomposition acts on the whole old coefficient row. -/
theorem appendPull_pair (i : I) {u v t w : List I}
    (c : Old D Sc cutoff u v) (h : hom D Sc cutoff (t ++ [i]) w)
    (b : Old D Sc cutoff v t) :
    appendPull D Sc cutoff i u v w c (appendPair D Sc cutoff 0 i h b) =
      appendPair D Sc cutoff 0 i h (oldComp D Sc cutoff u v t c b) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  simp only [appendPair_mk, appendPull_mk, oldComp_mk, twist_zero,
    rightContext_comp, Category.assoc]

/-- A positioned append tail gives a map of representable old presheaves. -/
def appendPairNat (i : I) {t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) :
    oldRowPresheaf D Sc cutoff t ⟶ appendPresheaf D Sc cutoff i w where
  app v := ModuleCat.ofHom (appendPair D Sc cutoff 0 i h)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (appendPull_pair D Sc cutoff i f.unop h z).symm

/-- Reconstruction is linear over the full opposite old content ring. -/
def appendPairRow (i : I) (ν : List I) {t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) :
    OldContentRow D Sc cutoff ν t →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRow D Sc cutoff i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (appendPairNat D Sc cutoff i h)

@[simp] theorem appendPairRow_apply (i : I) (ν : List I)
    {t w : List I} (h : hom D Sc cutoff (t ++ [i]) w)
    (b : OldContentRow D Sc cutoff ν t) (v : ContentWords ν) :
    appendPairRow D Sc cutoff i ν h b v = appendPair D Sc cutoff 0 i h (b v) := rfl

/-- An old target and the input shuffle of its appended strand. -/
abbrev AppendTailIndex (i : I) (ν : List I) :=
  Σ t : ContentWords ν, AppendShuffle (appendLen t.val i)

instance appendTailIndexFintype (i : I) (ν : List I) :
    Fintype (AppendTailIndex i ν) := inferInstance

/-- The ambient target depends on the common old target and shuffle only. -/
def appendTailWord (i : I) {ν : List I} (q : AppendTailIndex i ν) :
    ContentWords (i :: ν) :=
  ⟨tgt (q.1.val ++ [i])
      (cw (Categorification.TypeA.canWord (q.1.val ++ [i]).length q.2.val⁻¹)),
    (tgt_perm _ _).trans
      ((List.perm_append_comm).trans (q.1.property.cons i))⟩

private theorem append_rows_canWord_one (n : ℕ) :
    Categorification.TypeA.canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]

/-- The common tail with identity old normal form. -/
def appendTailPBW (i : I) {ν : List I} (q : AppendTailIndex i ν) (m : ℕ) :
    AppendIdx i q.1.val (appendTailWord i q).val :=
  ⟨(m, [], 1, q.2), by simp, by simp, by
    simp [appendCrossingWord, append_rows_canWord_one, cw, appendTailWord]⟩

@[simp] theorem appendTailPBW_oldTarget (i : I) {ν : List I}
    (q : AppendTailIndex i ν) (m : ℕ) : (appendTailPBW i q m).oldTarget = q.1.val := by
  simp [appendTailPBW, AppendIdx.oldTarget, append_rows_canWord_one, cw]

/-- The tail with its coefficient source replaced by the common old target. -/
def appendCommonTail (i : I) {ν : List I} (q : AppendTailIndex i ν) (m : ℕ) :
    hom D Sc cutoff (q.1.val ++ [i]) (appendTailWord i q).val :=
  appendTailPBW_oldTarget i q m ▸
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      appendTail D Sc (appendTailPBW i q m))

/-- Embed a whole representable old row along its common append tail. -/
def appendTailRow (i : I) (ν : List I) (q : AppendTailIndex i ν) (m : ℕ) :
    OldContentRow D Sc cutoff ν q.1.val →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  (LinearMap.single (R := (ContentRing D Sc cutoff ν)ᵐᵒᵖ)
    (φ := fun w : ContentWords (i :: ν) => AppendRow D Sc cutoff i ν w.val)
    (appendTailWord i q)).comp
      (appendPairRow D Sc cutoff i ν (appendCommonTail D Sc cutoff i q m))

/-- Finitely supported common tails carrying full old idempotent rows. -/
abbrev AppendRows (i : I) (ν : List I) :=
  ⨁ q : AppendTailIndex i ν × ℕ, OldContentRow D Sc cutoff ν q.1.1.val

/-- Common-row reconstruction of the old-ring module underlying K₀. -/
def appendRowsReconstruct (i : I) (ν : List I) :
    AppendRows D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  DirectSum.toModule _ _ _ fun q => appendTailRow D Sc cutoff i ν q.1 q.2

@[simp] theorem appendRowsReconstruct_lof (i : I) (ν : List I)
    (q : AppendTailIndex i ν × ℕ) (b : OldContentRow D Sc cutoff ν q.1.1.val) :
    appendRowsReconstruct D Sc cutoff i ν
      (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b) =
      appendTailRow D Sc cutoff i ν q.1 q.2 b :=
  DirectSum.toModule_lof _ _ _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Moving powers on append common rows

The moving central dot or square translates the last-strand exponent and
leaves every old quotient coefficient unchanged, including exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace AppendIdx
variable {i : I} {v w : List I}
def shift (x : AppendIdx i v w) (d : ℕ) : AppendIdx i v w :=
  ⟨(d + x.1.1, x.1.2), x.2⟩
end AppendIdx
namespace ELVOld
theorem appendTail_shift {i : I} {v w : List I} (x : AppendIdx i v w) (d : ℕ) :
    (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ d : End _) ≫ appendTail D Sc x =
      appendTail D Sc (x.shift d) := by
  have hl : x.oldTarget.length = v.length := by simp [AppendIdx.oldTarget]
  rw [dotE_pow, appendTail, cl_comp]
  apply cl_eq_cl
  simp only [AppendIdx.shift, List.replicate_add, List.map_append, List.append_assoc,
    List.map_replicate, hl]

end ELVOld
end OddMath.QuiverHecke
end

end

section

/-! # Moving support in append quotient coordinates

Positive even moving powers shift the actual append PBW exponent. Arbitrary old
operators change only the full old quotient coefficient. Finite maximal support
therefore proves moving-minus-old cancellation, without exterior flatness.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem appendPower_tail {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) :
    appendMovingPower D Sc cutoff i x.oldTarget d ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc x) =
      affineUnit D Sc cutoff _ _ (appendTail D Sc (x.shift d)) := by
  rw [appendMovingPower, ← affineUnit_comp, appendTail_shift]
  rfl

/-- The moving dot power shifts the exponent, with every old quotient coefficient retained. -/
theorem appendMovingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (hd : d • D.parity i = 0)
    (b : Old D Sc cutoff v x.oldTarget) :
    appendMovingPowerTarget D Sc cutoff i v w d
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) =
      appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc (x.shift d)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change appendMovingPowerTarget D Sc cutoff i v w d
    (appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)) =
    appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc (x.shift d))
  rw [appendMovingPowerTarget_projection, ← Category.assoc,
    appendMovingPower_rightContext_cross D Sc cutoff i d hd, Category.assoc]
  exact congrArg (fun f => appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫ f))
      (appendPower_tail D Sc cutoff x d)

/-- Read back the old coefficient of a normalized single tail. -/
theorem appendOldCoordinate_pair (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (b : Old D Sc cutoff v x.oldTarget) :
    appendOldCoordinate D Sc cutoff p x
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) = b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  rw [appendPair_mk, appendOldCoordinate_projection, appendExtractOldQuotient_insert_tail, twist_twist]

/-- Different moving tails have disjoint old quotient coordinates. -/
theorem appendOldCoordinate_pair_off (p : ZMod 2) {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (b : Old D Sc cutoff v z.oldTarget) :
    appendOldCoordinate D Sc cutoff p x
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z) b) = 0 := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v z.oldTarget).mkQ_surjective b
  rw [appendPair_mk, appendOldCoordinate_projection]
  exact appendExtractOldQuotient_insert_off_tail D Sc cutoff p x z h _

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem appendMovingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : AppendIdx.Tail i v w) (d : ℕ) (hd : d • D.parity i = 0)
    (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w f)) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t b =>
    change appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [appendOldReconstruct, DirectSum.toModule_lof, appendMovingPower_pair_shift D Sc cutoff p _ d hd]
    by_cases ht : t = q
    · subst t
      rw [appendOldCoordinate_pair, DirectSum.of_eq_same]
    · rw [appendOldCoordinate_pair_off]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro he
        apply ht
        apply Subtype.ext
        have hk : q.representative.tailKey = t.representative.tailKey := by
          apply Prod.ext
          · have hn := congrArg Prod.fst he
            change d + q.representative.1.1 = d + t.representative.1.1 at hn
            exact Nat.add_left_cancel hn
          · have hs := congrArg Prod.snd he
            exact hs
        exact t.representative_tailKey.symm.trans (hk.symm.trans q.representative_tailKey)

/-- The other operator changes only the old coefficient; the total parity twist is retained. -/
theorem appendOldSourceTarget_pair (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (c : hom D Sc cutoff v v)
    (b : Old D Sc cutoff v x.oldTarget) :
    appendOldSourceTarget D Sc cutoff i v w c
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) =
      appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)
        (oldPrecomp D Sc cutoff v x.oldTarget (twist k p c) b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v v c ≫ (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)) =
    appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v x.oldTarget (twist k p (twist k p c ≫ r)) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)
  rw [twist_comp, twist_twist, rightContext_comp, Category.assoc]

/-- A coordinate above the input moving-exponent bound stays zero under the actual old action. -/
theorem appendOldSourceTarget_above (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (c : hom D Sc cutoff v v)
    (f : AppendOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, q.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff p x
      (appendOldSourceTarget D Sc cutoff i v w c (appendOldReconstruct D Sc cutoff p i v w f)) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) := by
    exact (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [appendOldReconstruct, DirectSum.toModule_lof, appendOldSourceTarget_pair]
  apply appendOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst (he.trans q.representative_tailKey)
  have hh := h q hq
  change x.1.1 = q.1.1 at hn
  omega

/-- Finite support cancels the actual positive moving power against any old source action. -/
theorem appendMovingPower_eq_oldSource (p : ZMod 2) (i : I) (v w : List I)
    (d : ℕ) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (c : hom D Sc cutoff v v) (z : AppendTarget D Sc cutoff i v w)
    (hz : appendMovingPowerTarget D Sc cutoff i v w d z = appendOldSourceTarget D Sc cutoff i v w c z) :
    z = 0 := by
  let f := appendOldCoordinateEquiv D Sc cutoff p i v w z
  suffices hf : f = 0 by
    exact (appendOldCoordinateEquiv D Sc cutoff p i v w).injective (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have he := appendMovingPower_coordinate_shift D Sc cutoff p q d hd f
  rw [appendOldReconstruct_coordinateEquiv, hz] at he
  have hb : ∀ t ∈ f.support, t.1.1 < (q.representative.shift d).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change t.1.1 < d + q.representative.1.1
    omega
  have ho := appendOldSourceTarget_above D Sc cutoff p (q.representative.shift d) c f hb
  rw [appendOldReconstruct_coordinateEquiv] at ho
  exact (DFinsupp.mem_support_iff.mp hq) (he.symm.trans ho)

theorem appendOldSource_movingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (hd : d • D.parity i = 0) (c : hom D Sc cutoff v v)
    (f : AppendOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff p x
      (appendOldSourceTarget D Sc cutoff i v w c
        (appendMovingPowerTarget D Sc cutoff i v w d
          (appendOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [appendOldReconstruct, DirectSum.toModule_lof, appendMovingPower_pair_shift D Sc cutoff p _ d hd,
    appendOldSourceTarget_pair]
  apply appendOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Append endpoint norm regularity and moving-chain injectivity

The independent endpoint polynomial is regular on the full append-old ELV
quotient. A largest moving exponent detects every nonzero coefficient. The
reverse chain then proves injectivity of G (`qMap`), without using P or QP
injectivity. This proves the cancellation required in DeformedBoundaryDivision §2;
the reverse boundary comparison of §3 is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem rightContext_sourceDotPower (i : I) (v : List I) (b d : ℕ) (hb : b < v.length) :
    rightContext D Sc cutoff [i] v v (sourceDotPower D Sc cutoff v b d) =
      affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ d) := by
  change rightContext D Sc cutoff [i] v v
    (affineUnit D Sc cutoff v v (dotE D Sc v b ^ d)) = _
  rw [rightContext_affineUnit]
  congr 1
  change whiskerWordRingHom D Sc v [i] (dotE D Sc v b ^ d) = _
  rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc v [i] b hb]

theorem appendProjection_old_dotPower (i : I) (v w : List I) (b d : ℕ) (hb : b < v.length)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ d) ≫ h) =
      appendOldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b d)
        (appendProjection D Sc cutoff i v w h) := by
  change _ = appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v v (sourceDotPower D Sc cutoff v b d) ≫ h)
  rw [rightContext_sourceDotPower D Sc cutoff i v b d hb]

theorem appendProjection_powerDifference_regular (i : I) (v w : List I) (b d : ℕ)
    (hb : b < v.length) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (v ++ [i]) v.length ^ d - dotE D Sc (v ++ [i]) b ^ d) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  rw [map_sub, Preadditive.sub_comp, map_sub, appendProjection_old_dotPower D Sc cutoff i v w b d hb] at hh
  exact appendMovingPower_eq_oldSource D Sc cutoff 0 i v w d hd hpos
    (sourceDotPower D Sc cutoff v b d) _ (sub_eq_zero.mp hh)

theorem appendProjection_powerSum_regular (i : I) (v w : List I) (b d : ℕ)
    (hb : b < v.length) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (v ++ [i]) b ^ d + dotE D Sc (v ++ [i]) v.length ^ d) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  rw [map_add, Preadditive.add_comp, map_add, appendProjection_old_dotPower D Sc cutoff i v w b d hb] at hh
  apply appendMovingPower_eq_oldSource D Sc cutoff 0 i v w d hd hpos
    (-sourceDotPower D Sc cutoff v b d)
  change _ = appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v v (-sourceDotPower D Sc cutoff v b d) ≫ h)
  rw [map_neg, Preadditive.neg_comp, map_neg]
  exact eq_neg_of_add_eq_zero_right hh

theorem appendProjection_qLeft_regular (i j : I) (hji : j ≠ i) (v w : List I)
    (b : ℕ) (hb : b < v.length) (hd : D.d j i ≠ 0)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (IntertwinerMeet.qLeft (B := End ((pres D Sc).obj (ob D (v ++ [i]))))
        (dotE D Sc (v ++ [i]) b) (dotE D Sc (v ++ [i]) v.length)
        (D.dn j i) (D.dn i j) (Sc.t j i : k) (Sc.t i j : k) (Sc.s j i)) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  let z := appendProjection D Sc cutoff i v w h
  let f := appendOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (appendOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hpos : 0 < D.dn i j := by
    have hc := D.dn_cast hji.symm
    have hz : D.d i j ≠ 0 := fun hz => hd ((D.d_eq_zero_iff j i).mpr hz)
    omega
  have hpar : D.dn i j • D.parity i = 0 := by
    simpa only [nsmul_eq_mul] using dn_mul_parity D i j
  have hbound (e : ℕ) (he : e < D.dn i j) :
      ∀ t ∈ f.support, e + t.1.1 < (q.representative.shift (D.dn i j)).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change e + t.1.1 < D.dn i j + q.representative.1.1
    omega
  have hlow (a e : ℕ) (he : e < D.dn i j) (hep : e • D.parity i = 0) :
      appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) b ^ a * dotE D Sc (v ++ [i]) v.length ^ e) ≫ h)) = 0 := by
    rw [End.mul_def, affineUnit_comp]
    rw [← rightContext_sourceDotPower D Sc cutoff i v b a hb]
    change appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
      (appendProjection D Sc cutoff i v w
        ((appendMovingPower D Sc cutoff i v e ≫
          rightContext D Sc cutoff [i] v v (sourceDotPower D Sc cutoff v b a)) ≫ h)) = 0
    rw [appendMovingPower_rightContext_cross D Sc cutoff i e hep, Category.assoc]
    have H := appendOldSource_movingPower_above D Sc cutoff 0
      (q.representative.shift (D.dn i j)) e hep (sourceDotPower D Sc cutoff v b a) f
      (hbound e he)
    rw [appendOldReconstruct_coordinateEquiv] at H
    exact H
  have hold : appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ D.dn j i) ≫ h)) = 0 := by
    simpa only [pow_zero, mul_one] using hlow (D.dn j i) 0 hpos (by simp)
  rw [IntertwinerMeet.qLeft, map_add, map_add, Preadditive.add_comp,
    Preadditive.add_comp, map_add, map_add] at hh
  have he := congrArg (appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))) hh
  simp only [map_add, map_zero, map_sum, Preadditive.sum_comp, map_smul,
    Linear.smul_comp] at he
  have hl : (∑ a ∈ Finset.range (D.dn j i), ∑ e ∈ Finset.range (D.dn i j),
      Sc.s j i a e • appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) b ^ a * dotE D Sc (v ++ [i]) v.length ^ e) ≫ h))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro e he'
    by_cases hs : Sc.s j i a e = 0
    · rw [hs, zero_smul]
    · have hep : e • D.parity i = 0 := by
        rw [nsmul_eq_mul]
        apply zmod_two_eq_zero_of_ne_one
        intro hp
        apply hs
        rw [Sc.s_symm]
        exact Sc.s_eq_zero i j e a hp
      rw [hlow a e (Finset.mem_range.mp he') hep, smul_zero]
  rw [hl, hold, smul_zero, zero_add, zero_add] at he
  have hm := appendMovingPower_coordinate_shift D Sc cutoff 0 q (D.dn i j) hpar f
  rw [appendOldReconstruct_coordinateEquiv] at hm
  change appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
    (appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ D.dn i j) ≫ h)) = f q at hm
  rw [hm] at he
  exact (DFinsupp.mem_support_iff.mp hq) ((Sc.t i j).isUnit.smul_eq_zero.mp he)

/-- Every append endpoint factor is regular on the full old-only quotient. -/
theorem appendProjection_endpointNormFactor_regular (i j : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (endpointNormFactor D Sc
        (B := End ((pres D Sc).obj (ob D (v ++ [i])))) j i
        (dotE D Sc (v ++ [i]) b) (dotE D Sc (v ++ [i]) v.length)) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  unfold endpointNormFactor at hh
  split_ifs at hh with hji hp hd
  · subst j
    rw [map_neg, Preadditive.neg_comp, map_neg, neg_eq_zero,
      End.mul_def, affineUnit_comp, Category.assoc] at hh
    have hs := appendProjection_powerSum_regular D Sc cutoff i v w b 2 hb
      ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide) _ hh
    rw [pow_two (dotE D Sc (v ++ [i]) v.length ^ 2 - dotE D Sc (v ++ [i]) b ^ 2),
      End.mul_def, affineUnit_comp, Category.assoc] at hs
    exact appendProjection_powerDifference_regular D Sc cutoff i v w b 2 hb
      ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide) h
      (appendProjection_powerDifference_regular D Sc cutoff i v w b 2 hb ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide) _ hs)
  · subst j
    have hp0 := parity_eq_zero_of_ne_one hp
    rw [map_neg, Preadditive.neg_comp, map_neg, neg_eq_zero,
      pow_two, End.mul_def, affineUnit_comp, Category.assoc] at hh
    have he := appendProjection_powerDifference_regular D Sc cutoff i v w b 1 hb
      (by simp [hp0]) (by decide)
    simp only [pow_one] at he
    exact he h (he _ hh)
  · rw [Algebra.algebraMap_eq_smul_one, map_smul, End.one_def, affineUnit_id,
      Linear.smul_comp, Category.id_comp, map_smul] at hh
    exact (Sc.t j i).isUnit.smul_eq_zero.mp hh
  · exact appendProjection_qLeft_regular D Sc cutoff i j hji v w b hb hd h hh

/-- Cancel the ordered norm recursively without changing its ambient word. -/
theorem appendProjection_endpointNormAux_regular (i : I) (v w ν : List I) (b : ℕ)
    (hb : b + ν.length ≤ v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (endpointNormAux D Sc i (v ++ [i]) v.length b ν) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  induction ν generalizing b h with
  | nil => simpa only [endpointNormAux, End.one_def, affineUnit_id, Category.id_comp] using hh
  | cons j ν ih =>
    rw [endpointNormAux, End.mul_def, affineUnit_comp, Category.assoc] at hh
    have ht := ih (b + 1) (by simp only [List.length_cons] at hb; omega) _ hh
    exact appendProjection_endpointNormFactor_regular D Sc cutoff i j v w b
      (by simp only [List.length_cons] at hb; omega) h ht

/-- The independently defined append endpoint norm detects every old-only ELV class.
The proof uses finite append PBW support, including all exterior coefficients. -/
theorem appendProjection_endpointNorm_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (endpointNorm D Sc i [] v) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  apply appendProjection_endpointNormAux_regular D Sc cutoff i v w v 0 (by simp) h
  simpa only [endpointNorm, List.nil_append, List.length_nil, zero_add] using hh

/-- The moving-chain map G is injective on the actual append-old quotient.
Only its reverse composite and independent append norm regularity are used. -/
theorem qMap_injective (i : I) (v w : List I) :
    Function.Injective (qMap D Sc cutoff i v w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  have he := congrArg (rMap D Sc cutoff i v w) hz
  rw [rMap_qMap_projection, map_zero,
    reverseMoveHom_comp_moveHom_eq_endpointNorm] at he
  exact appendProjection_endpointNorm_regular D Sc cutoff i v w h he

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordered reverse boundary polynomial and corrected iterates

`pMap_move_projection` gives the literal reverse QP polynomial identity on the
old-only append quotient, canceling G on its proved domain.
`pMap_boundaryRho_move_iterate` and `pMap_evenDot_move_iterate` give every
corrected right-dot iterate in both parities. These are the quotient-level
inputs to `DeformedBoundaryDivision.md` §§3–4, not an identification with
longest-output coordinates, and not the full reverse-chain norm.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem affineQP_comp_move (i : I) (v : List I) :
    affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ move D Sc cutoff i v =
      move D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) := by
  change affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫
      affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v) =
    affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v) ≫
      affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v)
  rw [← affineUnit_comp, ← affineUnit_comp]
  exact congrArg (affineUnit D Sc cutoff (i :: v) (v ++ [i]))
    (qpProduct_comp_moveHom D Sc i v)

/-- The reverse boundary polynomial identity in the append-old quotient.
The endpoint polynomial is explicit and ordered, and G is canceled only on
its proved old-only domain. -/
theorem pMap_move_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    pMap D Sc cutoff i v w
      (projection D Sc cutoff i v w (move D Sc cutoff i v ≫ h)) =
    sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h) := by
  apply qMap_injective D Sc cutoff i v w
  rw [qMap_pMap_projection, map_smul, qMap_projection]
  rw [Category.assoc, ← Category.assoc (relation D Sc cutoff i v), relation_comp_move,
    Linear.smul_comp, Linear.comp_smul, map_smul]
  congr 1
  rw [← Category.assoc, ← Category.assoc, affineQP_comp_move]
  change projection D Sc cutoff i v w
      (((move D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v)) ≫
        endpointELV D Sc cutoff i v) ≫ h) =
    projection D Sc cutoff i v w
      (move D Sc cutoff i v ≫ (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
        (endpointELV D Sc cutoff i v ≫ h)))
  simp only [Category.assoc]

/-- Every corrected odd iterate has the ordered right-dot image.
This is a quotient identity prior to longest-output extraction. -/
theorem pMap_boundaryRho_move_iterate (j : {i : I // D.parity i = 1})
    (v w : List I) (d : ℕ) (h : hom D Sc cutoff (v ++ [j.1]) w) :
    pMap D Sc cutoff j.1 v w
      ((boundaryRho D Sc cutoff j v w)^[d]
        (projection D Sc cutoff j.1 v w (move D Sc cutoff j.1 v ≫ h))) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendProjection D Sc cutoff j.1 v w
        (appendMovingPower D Sc cutoff j.1 v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
          endpointELV D Sc cutoff j.1 v ≫ h) := by
  rw [pMap_boundaryRho_iterate, pMap_move_projection, map_smul,
    appendMovingPowerTarget_projection]
private theorem pMap_evenDot_iterate (i : I) (hi : D.parity i = 0)
    (v w : List I) (d : ℕ) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w
      ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d] z) =
    appendMovingPowerTarget D Sc cutoff i v w d (pMap D Sc cutoff i v w z) := by
  induction d with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
    simp only [Function.iterate_zero, id_eq, pMap_projection,
      appendMovingPowerTarget_projection, appendMovingPower, pow_zero,
      End.one_def, affineUnit_id, Category.id_comp]
  | succ d ih =>
    rw [Function.iterate_succ_apply', pMap_movingEvenDot D Sc cutoff i hi, ih,
      appendMovingPowerTarget_add, Nat.add_comm 1 d]

/-- At even colour the same ordered reverse identity needs no correction. -/
theorem pMap_evenDot_move_iterate (i : I) (hi : D.parity i = 0)
    (v w : List I) (d : ℕ) (h : hom D Sc cutoff (v ++ [i]) w) :
    pMap D Sc cutoff i v w
      ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d]
        (projection D Sc cutoff i v w (move D Sc cutoff i v ≫ h))) =
      appendProjection D Sc cutoff i v w
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h) := by
  rw [pMap_evenDot_iterate D Sc cutoff i hi, pMap_move_projection]
  simp only [hi, nsmul_zero, zero_mul, sign_zero, one_smul,
    appendMovingPowerTarget_projection]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Prescribed P on the compatible output lifts

This is the unprojected comparison in `DeformedMackeyBoundary.md` §3: the
actual P applied to the constructed section intertwines corrected output rho
with the actual append moving dot. It does not identify a polynomial projection
against the chronological crossing image. That additional full-ELV append
splitting is necessary before deriving the degree-zero polynomial defect.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The literal P-image of the specified compatible long section. -/
def outputLiftBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] AppendTarget D Sc cutoff j.1 v (v ++ [j.1]) :=
  (pMap D Sc cutoff j.1 v (v ++ [j.1])).comp (outputLongSection D Sc cutoff p j.1 v)

/-- Actual first-order intertwining before the crossing/polynomial splitting. -/
theorem outputLiftBoundary_rho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLiftBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (outputLiftBoundary D Sc cutoff p j v f) := by
  change pMap D Sc cutoff j.1 v (v ++ [j.1])
    (outputLongSection D Sc cutoff p j.1 v (outputCoefficientRho D Sc cutoff p j v f)) = _
  rw [← boundaryRho_outputLongSection, pMap_boundaryRho]
  rfl

/-- The P-image of every source class differs from that of its specified long
lift by an actual chronological crossing class. This is the needed concrete
factorization statement before constructing the polynomial projection. -/
theorem pMap_sub_outputLiftBoundary_mem (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    pMap D Sc cutoff j.1 v (v ++ [j.1]) z -
      outputLiftBoundary D Sc cutoff p j v (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalCrossingSpan D Sc cutoff j.1 v v := by
  have hs : z - outputLongSection D Sc cutoff p j.1 v
      (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalShortSpan D Sc cutoff j.1 v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p j.1 v]
    change outputLongExtraction D Sc cutoff p j.1 v _ = 0
    rw [map_sub, outputLongExtraction_section, sub_self]
  have h := pMap_chronologicalShortSpan_le D Sc cutoff j.1 v v
    (Submodule.mem_map.mpr ⟨_, hs, rfl⟩)
  simpa only [map_sub, outputLiftBoundary, LinearMap.comp_apply] using h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Corrected rho iterates of the independent output polynomial

`outputLongExtraction_boundaryRho_move_independentS` identifies every corrected
source iterate with the finite sum of the prescribed corrected long coordinates.
The coefficients are the independently defined ordered square product, not an
extraction-defined polynomial. Their even support and total-twist invariance are
proved before using the corrected even/odd lift formulas.
`outputLongExtraction_boundaryRho_move_polynomial` further gives the literal
finite operator sum S(rhobar) w_d, where w_d is the actual corrected lift of
the old identity. Chronological coefficient postcomposition intertwines
rhobar by `outputCoefficientRho_postcomp`; centrality is not assumed.

`reverseBoundary_sub_correctedS_mem` couples this extraction to the ordered
reverse-QP P-image modulo the chronological crossing image. This is the input
from `DeformedBoundaryDivision.md` §4 for the augmented boundary matrix; it does
not assume or construct C₀, S-division, or a matrix inverse. The global library
sign is retained, rather than replaced by the source-convention sign.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem independentOutputS_oldTwist (i : I) (v : List I) (n : ℕ) (q : ZMod 2) :
    oldTwist D Sc cutoff q v v (independentOutputS D Sc cutoff i v n) =
      independentOutputS D Sc cutoff i v n := by
  rw [independentOutputS_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [map_smul]
    congr 1
    change (ideal D Sc cutoff v v).mkQ (twist k q _) = _
    rw [leadingSourceOldArrow_twist]
  · exact map_zero _

theorem independentOutputS_support_even (i : I) (hi : D.parity i = 1)
    (v : List I) {n : ℕ} (hn : n ∈ (independentOutputS D Sc cutoff i v).support) :
    Even n := by
  by_contra he
  have hz : independentOutputS D Sc cutoff i v n = 0 := by
    rw [independentOutputS_apply]
    have hsum : (∑ c : MoveChoices v,
        if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
          leadingMoveCoeff D (k := k) i v c •
            (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [ite_eq_right]
      intro h
      apply he
      rw [← h]
      exact Nat.even_iff.mpr (sourceMovingDegree_leadingSourceDots_even D i hi 0 v c)
    rw [hsum, smul_zero]
  exact (Finsupp.mem_support_iff.mp hn) hz

theorem outputLongExtraction_boundaryRho_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d] z) =
      (outputCoefficientRho D Sc cutoff p j v)^[d]
        (outputLongExtraction D Sc cutoff p j.1 v z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', outputLongExtraction_boundaryRho, ih,
      Function.iterate_succ_apply']

theorem outputCoefficientRho_iterate_even_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ) (hn : Even n)
    (b : Old D Sc cutoff v v) :
    (outputCoefficientRho D Sc cutoff p j v)^[n] (Finsupp.single 0 b) =
      Finsupp.single n b := by
  obtain ⟨q, hq⟩ := hn
  have h : n = 2 * q := by omega
  rw [h]
  rw [← outputLongExtraction_correctedLift, outputCorrectedLift_even,
    outputLongExtraction_lift]

theorem outputCoefficientRho_iterate_independentS (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    (outputCoefficientRho D Sc cutoff p j v)^[d] (independentOutputS D Sc cutoff j.1 v) =
      ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
        outputLongExtraction D Sc cutoff p j.1 v
          (outputCorrectedLift D Sc cutoff p j v (d + n)
            (independentOutputS D Sc cutoff j.1 v n)) := by
  conv_lhs => rw [← Finsupp.sum_single (independentOutputS D Sc cutoff j.1 v)]
  rw [← Module.End.coe_pow]
  change (outputCoefficientRho D Sc cutoff p j v ^ d)
    (∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
      Finsupp.single n (independentOutputS D Sc cutoff j.1 v n)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Module.End.pow_apply, outputLongExtraction_correctedLift,
    Function.iterate_add_apply,
    outputCoefficientRho_iterate_even_single D Sc cutoff p j v n
      (independentOutputS_support_even D Sc cutoff j.1 j.2 v hn)]

theorem outputLongExtraction_boundaryRho_move_independentS (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff (j.1 :: v) (v ++ [j.1]) (moveHom D Sc j.1 [] v)))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (independentOutputS D Sc cutoff j.1 v n)) := by
  rw [outputLongExtraction_boundaryRho_iterate, outputLongExtraction_move_independentS,
    ← Module.End.coe_pow, map_smul, Module.End.pow_apply,
    outputCoefficientRho_iterate_independentS]

private theorem twist_oldComp (p : ZMod 2) (v : List I) (b c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff p v v (oldComp D Sc cutoff v v v b c) =
      oldComp D Sc cutoff v v v (oldTwist D Sc cutoff p v v b)
        (oldTwist D Sc cutoff p v v c) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k p (b ≫ c)) =
    (ideal D Sc cutoff v v).mkQ (twist k p b ≫ twist k p c)
  rw [twist_comp]

private theorem precomp_oldComp (v : List I) (a : hom D Sc cutoff v v)
    (b c : Old D Sc cutoff v v) :
    oldPrecomp D Sc cutoff v v a (oldComp D Sc cutoff v v v b c) =
      oldComp D Sc cutoff v v v (oldPrecomp D Sc cutoff v v a b) c := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (a ≫ (b ≫ c)) =
    (ideal D Sc cutoff v v).mkQ ((a ≫ b) ≫ c)
  rw [Category.assoc]

/-- Coefficient-operator intertwining in chronological composition order.
No commutation or centrality of the old coefficient is assumed. -/
theorem outputCoefficientRho_postcomp (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (c : Old D Sc cutoff v v)
    (hc : oldTwist D Sc cutoff (D.parity j.1) v v c = c)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputCoefficientRho D Sc cutoff p j v
      (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip c) f) =
      Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip c)
        (outputCoefficientRho D Sc cutoff p j v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      LinearMap.flip_apply, outputCoefficientRho_single, map_add, map_smul]
    rw [twist_oldComp, hc, precomp_oldComp]

theorem outputCoefficientRho_iterate_postcomp (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (c : Old D Sc cutoff v v)
    (hc : oldTwist D Sc cutoff (D.parity j.1) v v c = c)
    (d : ℕ) (f : ℕ →₀ Old D Sc cutoff v v) :
    (outputCoefficientRho D Sc cutoff p j v)^[d]
      (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip c) f) =
      Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip c)
        ((outputCoefficientRho D Sc cutoff p j v)^[d] f) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, outputCoefficientRho_postcomp D Sc cutoff p j v c hc,
      Function.iterate_succ_apply']

theorem outputCorrectedLift_coefficient (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (c : Old D Sc cutoff v v)
    (hc : oldTwist D Sc cutoff (D.parity j.1) v v c = c) :
    outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c) =
      Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip c)
        (outputLongExtraction D Sc cutoff p j.1 v
          (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))) := by
  rw [outputLongExtraction_correctedLift, outputLongExtraction_correctedLift,
    ← outputCoefficientRho_iterate_postcomp D Sc cutoff p j v c hc]
  congr 1
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, LinearMap.flip_apply]
  congr 1
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  rw [oldComp_mk, Category.id_comp]

/-- The independent polynomial evaluated at the actual coefficient rho on the
prescribed corrected unit vector. Coefficient action is chronological
postcomposition, and its intertwining is proved, not stipulated. -/
theorem outputLongExtraction_boundaryRho_move_polynomial (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff (j.1 :: v) (v ++ [j.1]) (moveHom D Sc j.1 [] v)))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          Finsupp.mapRange.linearMap
            ((oldComp D Sc cutoff v v v).flip (independentOutputS D Sc cutoff j.1 v n))
            ((outputCoefficientRho D Sc cutoff p j v)^[n]
              (outputLongExtraction D Sc cutoff p j.1 v
                (outputCorrectedLift D Sc cutoff p j v d
                  ((ideal D Sc cutoff v v).mkQ (𝟙 _))))) := by
  rw [outputLongExtraction_boundaryRho_move_independentS]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [outputCorrectedLift_coefficient D Sc cutoff p j v (d + n) _
    (independentOutputS_oldTwist D Sc cutoff j.1 v n (D.parity j.1)),
    outputLongExtraction_correctedLift, outputLongExtraction_correctedLift,
    Nat.add_comm d n, Function.iterate_add_apply]
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Highest append-PBW coefficients of the actual signed QP factors

`appendQPFactor_top` identifies the literal unit highest coefficient, including
disconnected colours and repeated-even signs. `appendQPFactor_above` proves
the accompanying degree bound. Finite maximal append support then proves
`appendProjection_qpProduct_regular` for the actual all-word ordered product.
These are direct append-side inputs to `DeformedBoundaryDivision.md` §3,
not a transported prepend regularity or the full reverse-chain norm.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def appendQPDegree (i j : I) : ℕ :=
  if j = i then if D.parity i = 1 then 2 else 0 else D.dn i j

def appendQPUnit (i j : I) : kˣ :=
  if j = i then if D.parity i = 1 then 1 else -1 else Sc.t i j

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Actual endpoint ELV highest coefficient and ordered numerator cancellation

`endpointELV_top` and `endpointELV_above` prove the leading unit and support
bound of the literal finite polynomial for every cutoff and colour. The
leading action retains the full old-Hom parity twist. Direct finite maximal
append support proves its regularity and, with the independently proved
QP factor regularity, `appendProjection_qp_endpointELV_regular` cancels the
actual ordered numerator from `DeformedBoundaryDivision.md` §3.
No injectivity on the final full cyclotomic quotient is used or claimed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def appendCoefficientTerm (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (d : ℕ) :
    hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  a ⊗ₜ[k] (dotE D Sc (v ++ [i]) v.length ^ d : End _)

@[simp] theorem appendCoefficientTerm_one (i : I) (v : List I) (d : ℕ) :
    appendCoefficientTerm D Sc cutoff i v 1 d = appendMovingPower D Sc cutoff i v d := rfl

theorem append_coefficient_monomial (i : I) (v : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    appendCoefficientTerm D Sc cutoff i v a d =
      appendMovingPower D Sc cutoff i v d ≫
        rightContext D Sc cutoff [i] v v (ELVPScalar.scalar D Sc cutoff v a) := by
  rw [ELVPScalar.rightContext_scalar]
  exact (affineUnit_comp_scalar D Sc cutoff (dotE D Sc (v ++ [i]) v.length ^ d) a).symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Signed old-Hom division by the ordered endpoint–QP numerator

`endpointQP_top` and `endpointQP_above` assemble the actual unit highest action,
including the full old-Hom twist. `endpointQP_division` uses these statements
and finite support to divide every old-only append target by the prescribed
chronological numerator, leaving support strictly below its moving degree.
No arbitrary polynomial-evaluation multiplicativity or output S identity is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def endpointQPDegree (i : I) (v : List I) : ℕ := cutoff i +
  ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum

def appendQPProductUnit (i : I) (v : List I) : kˣ :=
  ((List.range v.length).map (fun b => appendQPUnit D Sc i (v.getD b i))).prod

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The source presentation of the literal old ELV quotient

SwappedVacuumCoordinates §§5–6. The coefficient quotient has exactly its
specified coefficient-ideal kernel; tensor right exactness is sufficient,
with no flatness assumption. The next comparison identifies the actual
first-boundary old ideal with the image of the full source relation span.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Surjectivity of the actual full-coefficient categorical quotient. -/
theorem elvQuotientMap_surjective (s t : List I) :
    Function.Surjective
      (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) :=
  TensorProduct.map_surjective
    ((RingCon.mkₐ_surjective (α := k) (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon).comp
      (SKM.SYM.polynomialExteriorEquiv D k).symm.surjective) Function.surjective_id

private theorem source_unit_comp_coefficient {s t : List I} (c : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    sourceCoefficientHom D Sc 1 f ≫ sourceCoefficientHom D Sc c (𝟙 _) =
      sourceCoefficientHom D Sc c f := by
  have h1 : SKM.SYM.polynomialExteriorEquiv D k (1 : SKM.SYM D k) ∈
      SKM.SYM.polynomialExteriorParity D k 0 := by
    rw [map_one]; exact SetLike.GradedOne.one_mem
  rw [sourceCoefficientHom_comp D Sc h1 c f (id_mem _)]
  simp only [koszulSign_zero_left, one_smul, mul_one, Category.comp_id]

/-- Every pure coefficient-kernel tensor is in the literal coefficient
arm of the contextual source relations, including nonhomogeneous coefficients. -/
theorem sourceCoefficientHom_mem_coefficientRelationSpan {s t : List I}
    {c : SKM.SYM D k} (hc : c ∈ SKM.SYM.elvCoefficientIdeal D k cutoff)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    sourceCoefficientHom D Sc c f ∈ ELVCoefficientRelationSpan D Sc cutoff s t := by
  by_cases hlen : s.length = t.length
  · apply Submodule.subset_span
    refine ⟨t, hlen.symm, c, hc, sourceCoefficientHom D Sc 1 f, 𝟙 _, ?_⟩
    rw [Category.comp_id, source_unit_comp_coefficient]
  · have hf : f = 0 := hom_eq_zero_of_content_ne D Sc (fun h => hlen (by
      have hh := congrArg Multiset.card h
      simpa using hh)) f
    rw [hf, sourceCoefficientHom_zero_right]
    exact Submodule.zero_mem _

/-- Exactness of the full coefficient quotient: its kernel is precisely the
specified two-sided coefficient span, with all exterior coefficients retained. -/
theorem elvQuotientMap_ker_eq_coefficientRelationSpan (s t : List I) :
    LinearMap.ker
      (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVCoefficientRelationSpan D Sc cutoff s t := by
  apply le_antisymm
  · let q := (SKM.SYM.elvModelQuotient (k := k) D cutoff).toLinearMap
    let A := (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)
    have hq : Function.Surjective q :=
      (RingCon.mkₐ_surjective (α := k) (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon).comp
        (SKM.SYM.polynomialExteriorEquiv D k).symm.surjective
    have hfg : Function.Exact (LinearMap.ker q).subtype q := q.exact_subtype_ker_map
    have he := (rTensor_exact (R := k) (M := LinearMap.ker q) A hfg hq).linearMap_ker_eq
    intro x hx
    have hx' : x ∈ LinearMap.range (LinearMap.rTensor A (LinearMap.ker q).subtype) := by
      rw [← he]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    clear hx
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simpa only [map_add] using
        Submodule.add_mem (ELVCoefficientRelationSpan D Sc cutoff s t) hy hz
    | tmul c f =>
      let a := (SKM.SYM.polynomialExteriorEquiv D k).symm c.val
      have ha : a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff := Quotient.exact c.property
      have h := sourceCoefficientHom_mem_coefficientRelationSpan D Sc cutoff ha f
      simpa only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
        sourceCoefficientHom, coefficientHom, a, AlgEquiv.apply_symm_apply,
        BoxProd.tmulHom, SuperalgebraCat.ofElem] using h
  · exact elvQuotientMap_kills_span D Sc cutoff s t

private theorem elvGenerator_image_mem_oldIdeal {v : List I}
    {r : coefficientObj D Sc v ⟶ coefficientObj D Sc v}
    (hr : ELVGenerator D Sc cutoff v r) :
    elvQuotientMap D Sc cutoff _ _ r ∈ ELVOld.ideal D Sc cutoff v v := by
  rcases hr with ⟨a, ha, rfl⟩ | ⟨i, tail, h, rfl⟩ | ⟨i, hi, tail, h, rfl⟩
  · rw [elvQuotientMap_kills D Sc ha]
    exact Submodule.zero_mem _
  · subst v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hrel : elvQuotientMap D Sc cutoff _ _
        (elvCyclotomic D Sc i tail (cutoff i.1)) = ELVOld.relation D Sc cutoff i.1 tail := by
      rw [ELVOld.relation, dite_eq_left i.property]
      rfl
    rw [hrel]
    exact ELVOld.relation_mem D Sc cutoff i.1 tail
  · subst v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hn : D.parity i ≠ 1 := by rw [hi]; exact zero_ne_one
    have hrel : elvQuotientMap D Sc cutoff _ _
        (evenCyclotomic D Sc i tail (cutoff i)) = ELVOld.relation D Sc cutoff i tail := by
      rw [ELVOld.relation, dite_eq_right hn]
      rfl
    rw [hrel]
    exact ELVOld.relation_mem D Sc cutoff i tail

private theorem oldRelation_source_lift (j : I) (tail : List I) :
    ∃ r : coefficientObj D Sc (j :: tail) ⟶ coefficientObj D Sc (j :: tail),
      ELVGenerator D Sc cutoff (j :: tail) r ∧
        elvQuotientMap D Sc cutoff _ _ r = ELVOld.relation D Sc cutoff j tail := by
  by_cases hj : D.parity j = 1
  · refine ⟨elvCyclotomic D Sc ⟨j, hj⟩ tail (cutoff j),
      Or.inr (Or.inl ⟨⟨j, hj⟩, tail, rfl, by simp⟩), ?_⟩
    rw [ELVOld.relation, dite_eq_left hj]
    rfl
  · have hz : D.parity j = 0 := (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    refine ⟨evenCyclotomic D Sc j tail (cutoff j),
      Or.inr (Or.inr ⟨j, hz, tail, rfl, by simp⟩), ?_⟩
    rw [ELVOld.relation, dite_eq_right hj]
    rfl

/-- The source relation span maps onto the literal old cyclotomic ideal.
Every target coefficient and context is lifted through the actual quotient. -/
theorem map_elvRelationSpan_eq_oldIdeal (s t : List I) :
    (ELVRelationSpan D Sc cutoff s t).map
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVOld.ideal D Sc cutoff s t := by
  apply le_antisymm
  · apply (Submodule.map_le_iff_le_comap).mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, r, hr, a, b, rfl⟩
    change elvQuotientMap D Sc cutoff _ _ (a ≫ r ≫ b) ∈ ELVOld.ideal D Sc cutoff s t
    rw [elvQuotientMap_comp, elvQuotientMap_comp]
    exact ELVOld.comp_ideal D Sc cutoff _
      (ELVOld.ideal_comp D Sc cutoff (elvGenerator_image_mem_oldIdeal D Sc cutoff hr) _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, v, a, b, rfl⟩
    by_cases hlen : (j :: v).length = s.length
    · obtain ⟨a', ha⟩ := elvQuotientMap_surjective D Sc cutoff s (j :: v) a
      obtain ⟨b', hb⟩ := elvQuotientMap_surjective D Sc cutoff (j :: v) t b
      obtain ⟨r, hr, hrel⟩ := oldRelation_source_lift D Sc cutoff j v
      refine ⟨a' ≫ r ≫ b', Submodule.subset_span ⟨j :: v, hlen, r, hr, a', b', rfl⟩, ?_⟩
      rw [elvQuotientMap_comp, elvQuotientMap_comp, ha, hb, hrel]
    · have ha : a = 0 := ELVOld.hom_eq_zero_of_length_ne D Sc cutoff (Ne.symm hlen) a
      rw [ha, Limits.zero_comp]
      exact Submodule.zero_mem _

/-- The actual quotient projection to old cyclotomic Homs. -/
def sourceToOldHom (s t : List I) :=
  (ELVOld.ideal D Sc cutoff s t).mkQ ∘ₗ
    elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)

end OddMath.QuiverHecke
end

end

section

/-! # Literal coefficient generators in the actual old presentation kernel

SwappedVacuumCoordinates §§5–6 and the literal power ideal of
SwappedNondegeneracy §2. This compares two-sided coefficient spans inside
existing full ELV Hom modules. The first-boundary ideal remains the literal
old ideal, and powers are the actual elementary coefficient powers.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual full-coefficient two-sided span of specified scalar generators
in old coefficient Homs, before the strand cyclotomic ideal is imposed. -/
def coefficientGeneratorHomSpan
    (S : Set (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) (s t : List I) :
    Submodule k (hom D Sc cutoff s t) :=
  Submodule.span k {f | ∃ v : List I, v.length = s.length ∧ ∃ a ∈ S,
    ∃ x : hom D Sc cutoff s v, ∃ y : hom D Sc cutoff v t,
      x ≫ (a ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D v))) : hom D Sc cutoff v v) ≫ y = f}

/-- The actual coefficient-generator span is the image of its full source
span. Both context multipliers are lifted through the surjective quotient. -/
theorem map_coefficientGeneratorSpan (T : Set (SKM.SYM D k)) (s t : List I) :
    (CoefficientGeneratorSpan D Sc T s t).map
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      coefficientGeneratorHomSpan D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff '' T) s t := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, a, ha, x, y, rfl⟩
    change elvQuotientMap D Sc cutoff _ _
      (x ≫ sourceCoefficientHom D Sc a (𝟙 _) ≫ y) ∈
        coefficientGeneratorHomSpan D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff '' T) s t
    rw [elvQuotientMap_comp, elvQuotientMap_comp, elvQuotientMap_source]
    exact Submodule.subset_span ⟨v, hv, SKM.SYM.elvCoefficientQuotient D cutoff a,
      ⟨a, ha, rfl⟩, _, _, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, a, ⟨a', ha', rfl⟩, x, y, rfl⟩
    obtain ⟨x', hx⟩ := elvQuotientMap_surjective D Sc cutoff s v x
    obtain ⟨y', hy⟩ := elvQuotientMap_surjective D Sc cutoff v t y
    refine ⟨x' ≫ sourceCoefficientHom D Sc a' (𝟙 _) ≫ y',
      Submodule.subset_span ⟨v, hv, a', ha', x', y', rfl⟩, ?_⟩
    rw [elvQuotientMap_comp, elvQuotientMap_comp, elvQuotientMap_source, hx, hy]

/-- The full old ideal and the specified scalar ideal together have precisely
the full source presentation plus the same coefficient generators as preimage. -/
theorem comap_oldIdeal_sup_coefficientGenerators (T : Set (SKM.SYM D k)) (s t : List I) :
    (ideal D Sc cutoff s t ⊔ coefficientGeneratorHomSpan D Sc cutoff
        (SKM.SYM.elvCoefficientQuotient D cutoff '' T) s t).comap
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVRelationSpan D Sc cutoff s t ⊔ CoefficientGeneratorSpan D Sc T s t := by
  rw [← map_elvRelationSpan_eq_oldIdeal D Sc cutoff s t,
    ← map_coefficientGeneratorSpan D Sc cutoff T s t, ← Submodule.map_sup]
  apply Submodule.comap_map_eq_self
  rw [elvQuotientMap_ker_eq_coefficientRelationSpan]
  exact (elvCoefficientRelationSpan_le D Sc cutoff s t).trans le_sup_left

/-- The literal elementary-power contribution in existing old coefficient Homs. -/
abbrev elementaryPowerHomSpan (L : I × ℕ → ℕ) (s t : List I) :=
  coefficientGeneratorHomSpan D Sc cutoff
    (Set.range fun a => elementaryCoefficients (k := k) D cutoff a ^ L a) s t

private theorem elementaryPower_image (L : I × ℕ → ℕ) :
    SKM.SYM.elvCoefficientQuotient (k := k) D cutoff ''
        Set.range (fun a : I × ℕ => SKM.SYM.e D k a.1 a.2 ^ L a) =
      Set.range (fun a => elementaryCoefficients (k := k) D cutoff a ^ L a) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (map_pow (SKM.SYM.elvCoefficientQuotient D cutoff) _ _).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, map_pow (SKM.SYM.elvCoefficientQuotient D cutoff) _ _⟩

/-- The presentation preimage for the paper's literal powers. In particular,
no equality between a weighted ideal and a power ideal is used. -/
theorem comap_oldIdeal_sup_elementaryPowers (L : I × ℕ → ℕ) (s t : List I) :
    (ideal D Sc cutoff s t ⊔ elementaryPowerHomSpan D Sc cutoff L s t).comap
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVRelationSpan D Sc cutoff s t ⊔
        CoefficientGeneratorSpan D Sc
          (Set.range fun a : I × ℕ => SKM.SYM.e D k a.1 a.2 ^ L a) s t := by
  have h := comap_oldIdeal_sup_coefficientGenerators D Sc cutoff
    (Set.range fun a : I × ℕ => SKM.SYM.e D k a.1 a.2 ^ L a) s t
  rw [elementaryPower_image] at h
  exact h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The equal-colour braid in the untruncated old quotient

Brundan–Ellis Definition 1.5, the same-colour braid: the two independently
appended old crossings satisfy the braid before induction. This is the
coefficient input for the evaluated probe's three-induction relation.
No coefficient-power truncation or scalar faithfulness is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem affineEqual_braid (v : List I) (i : I) :
    (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [i])) ≫
        crossLast D Sc (v ++ [i]) i i ≫
          (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [i])) =
      crossLast D Sc (v ++ [i]) i i ≫
        (crossLast D Sc v i i ▷ (pres D Sc).obj (ob D [i])) ≫
          crossLast D Sc (v ++ [i]) i i := by
  rw [crossLast_whiskerRight_cl, crossLast, cl_comp_three, cl_comp_three]
  refine (braid_ne_gen D Sc v [] i i i (by simp) ?_ ?_ ?_ ?_ _ _).symm <;>
    simp [List.append_assoc]

/-- The literal prefix and suffix old crossings satisfy the three-strand braid. -/
theorem equalCrossComponent_braid (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (equalCrossComponent D Sc cutoff i s) ≫
        equalCrossComponent D Sc cutoff i ((append D Sc cutoff i).obj s) ≫
          (append D Sc cutoff i).map (equalCrossComponent D Sc cutoff i s) =
      equalCrossComponent D Sc cutoff i ((append D Sc cutoff i).obj s) ≫
        (append D Sc cutoff i).map (equalCrossComponent D Sc cutoff i s) ≫
          equalCrossComponent D Sc cutoff i ((append D Sc cutoff i).obj s) := by
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i] ++ [i])
      (s.word ++ [i] ++ [i] ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
        rightContext D Sc cutoff [i] _ _
          (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))) =
    (ideal D Sc cutoff (s.word ++ [i] ++ [i] ++ [i])
      (s.word ++ [i] ++ [i] ++ [i])).mkQ
      (affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
        rightContext D Sc cutoff [i] _ _
          (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i))
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
      (crossLast D Sc s.word i i ▷ (pres D Sc).obj (ob D [i])) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
          affineUnit D Sc cutoff _ _
            (crossLast D Sc s.word i i ▷ (pres D Sc).obj (ob D [i]))) =
    (ideal D Sc cutoff _ _).mkQ
      (affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i) ≫
        affineUnit D Sc cutoff _ _
          (crossLast D Sc s.word i i ▷ (pres D Sc).obj (ob D [i])) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc (s.word ++ [i]) i i))
  rw [← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp, ← affineUnit_comp]
  exact congrArg (fun f =>
    (ideal D Sc cutoff (s.word ++ [i] ++ [i] ++ [i])
      (s.word ++ [i] ++ [i] ++ [i])).mkQ
      (affineUnit D Sc cutoff _ _ f)) (affineEqual_braid D Sc s.word i)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end
