/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation
import OddMath.QuiverHecke.CentreFinite
import OddMath.SKM.BubbleSubstitution
/-! # Odd one-strand detection after coefficient truncation

At cyclotomic cutoff two and coefficient-weight cutoff three, evaluation at
zero dot and zero elementary coefficients retains the odd exterior generator.
The evaluation kills both two-sided Hom ideals, including contexts through
arbitrary intermediate words. It detects the delta class in `TruncatedOld`,
not merely in its coefficient algebra. No faithfulness is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
open SKM.SYM
variable (D : SKM.Datum Unit ℤ) (Sc : SKM.Scalars D ℚ)

private theorem exteriorProjection_e (i : Unit) (r : ℕ) :
    exteriorProjection D ℚ (e D ℚ i r) = 0 := by
  unfold exteriorProjection e ι SKM.SYM.mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rfl

private def constantToExterior :
    MvPolynomial (Unit × ℕ) ℚ →ₐ[ℚ] ExteriorAlgebra ℚ (OddModule D ℚ) where
  toRingHom := (algebraMap ℚ _).comp MvPolynomial.constantCoeff
  commutes' r := by simp [MvPolynomial.algebraMap_eq]

private theorem projection_polynomial :
    (exteriorProjection D ℚ).comp (polynomialInclude D ℚ) = constantToExterior D := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [constantToExterior, exteriorProjection_e]

private theorem projection_basis_high (a : CoefficientIndex D)
    (ha : 3 ≤ coefficientWeight D a) :
    exteriorProjection D ℚ (coefficientBasis D ℚ a) = 0 := by
  have hn : a.1 ≠ 0 := by
    intro hz
    have hc : a.2.card ≤ 1 := Finset.card_le_one_of_subsingleton _
    simp only [coefficientWeight, hz, Finsupp.sum_zero_index, zero_add] at ha
    omega
  have hp : exteriorProjection D ℚ
      (polynomialInclude D ℚ (MvPolynomial.monomial a.1 1)) = 0 := by
    have h := DFunLike.congr_fun (projection_polynomial D)
      (MvPolynomial.monomial a.1 (1 : ℚ))
    simpa [constantToExterior, MvPolynomial.constantCoeff_monomial, hn] using h
  rw [coefficientBasis_eq_mul, map_mul, hp, zero_mul]

private theorem projection_high {x : SKM.SYM D ℚ}
    (hx : x ∈ CoefficientAtLeast D ℚ 3) : exteriorProjection D ℚ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact projection_basis_high D a ha
  | zero => simp
  | add x y _ _ ihx ihy => simp [ihx, ihy]
  | smul c x _ ih => simp [ih]

private theorem projection_elvIdeal {x : SKM.SYM D ℚ}
    (hx : x ∈ elvCoefficientIdeal D ℚ (fun _ => 2)) : exteriorProjection D ℚ x = 0 := by
  apply projection_high D
  apply (mem_coefficientIdeal_iff D ℚ 3 x).mp
  exact elvCoefficientIdeal_le_weight D ℚ (N := 2) (fun _ => le_rfl) hx

def coefficientEval : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2) →ₐ[ℚ]
    ExteriorAlgebra ℚ (OddModule D ℚ) :=
  (elvCoefficientIdeal D ℚ (fun _ => 2)).ringCon.liftₐ (exteriorProjection D ℚ) (by
    intro a b hab
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact projection_elvIdeal D ((TwoSidedIdeal.rel_iff _ _ _).mp hab))

@[simp] theorem coefficientEval_mk (x : SKM.SYM D ℚ) :
    coefficientEval D (elvCoefficientQuotient D (fun _ => 2) x) = exteriorProjection D ℚ x := rfl

def dotZero : End ((pres D Sc).obj (ob D [()])) →ₐ[ℚ] ℚ :=
  (_root_.Polynomial.aeval (0 : ℚ)).comp (singlePolynomialEquiv D Sc ()).symm.toAlgHom

@[simp] theorem dotZero_pow (n : ℕ) :
    dotZero D Sc (dotE D Sc [()] 0 ^ n) = if n = 0 then 1 else 0 := by
  have h : dotZero D Sc (dotE D Sc [()] 0) = 0 := by
    change _root_.Polynomial.aeval (0 : ℚ)
      ((singlePolynomialEquiv D Sc ()).symm (dotE D Sc [()] 0)) = 0
    rw [← singlePolynomialEquiv_X D Sc (), AlgEquiv.symm_apply_apply,
      _root_.Polynomial.aeval_X]
  rw [map_pow, h]
  split_ifs with hn
  · simp [hn]
  · exact zero_pow hn

def singleEval : hom D Sc (fun _ => 2) [()] [()] →ₗ[ℚ]
    ExteriorAlgebra ℚ (OddModule D ℚ) :=
  (TensorProduct.rid ℚ _).toLinearMap.comp
    (TensorProduct.map (coefficientEval D).toLinearMap (dotZero D Sc).toLinearMap)

@[simp] theorem singleEval_term (a : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2))
    (n : ℕ) : singleEval D Sc (singleTerm D Sc (fun _ => 2) () a n) =
      if n = 0 then coefficientEval D a else 0 := by
  change dotZero D Sc (dotE D Sc [()] 0 ^ n) • coefficientEval D a = _
  rw [dotZero_pow]
  split_ifs <;> simp

private theorem hom_zero_of_ne_single {t : List Unit} (ht : t ≠ [()])
    (f : hom D Sc (fun _ => 2) [()] t) : f = 0 := by
  have hp : ¬ t.Perm [()] := by simpa using ht
  suffices h : ∀ y : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2) ⊗[ℚ]
    ((pres D Sc).obj (ob D [()]) ⟶ (pres D Sc).obj (ob D t)), y = 0 from h f
  intro y
  induction y using TensorProduct.inductionOn with
  | add f g hf hg => rw [hf, hg, add_zero]
  | tmul a f => rw [hom_eq_zero_of_not_perm D Sc hp f, TensorProduct.tmul_zero]

private theorem dotZero_twist (p : ZMod 2) (f : End ((pres D Sc).obj (ob D [()]))) :
    dotZero D Sc (twist ℚ p f) = dotZero D Sc f := by
  suffices he : (dotZero D Sc).toLinearMap.comp (twist ℚ p) = (dotZero D Sc).toLinearMap from
    DFunLike.congr_fun he f
  apply (singleDotBasis D Sc ()).ext
  intro n
  rw [singleDotBasis_apply]
  change dotZero D Sc (twist ℚ p (dotE D Sc [()] 0 ^ n)) =
    dotZero D Sc (dotE D Sc [()] 0 ^ n)
  have hm : (dotE D Sc [()] 0 ^ n : End _) ∈
      parity (R := ℚ) _ _ (n • D.parity ()) := by
    induction n with
    | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := ℚ) _
    | succ n ih =>
      have hd : dotE D Sc [()] 0 ∈ parity (R := ℚ) _ _ (D.parity ()) :=
        positionedDot_parity D Sc [] [] ()
      simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using comp_mem hd ih
  rw [twist_of_mem p hm, map_smul, dotZero_pow]
  split_ifs with hn
  · subst n
    simp
  · simp

@[simp] theorem singleEval_tmul (a : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2))
    (f : End ((pres D Sc).obj (ob D [()]))) :
    singleEval D Sc (a ⊗ₜ[ℚ] f) = dotZero D Sc f • coefficientEval D a := rfl

private theorem singleEval_comp_tmul
    (a b : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2))
    (f g : End ((pres D Sc).obj (ob D [()]))) :
    singleEval D Sc (((a ⊗ₜ[ℚ] f) : hom D Sc (fun _ => 2) [()] [()]) ≫
      ((b ⊗ₜ[ℚ] g) : hom D Sc (fun _ => 2) [()] [()])) =
      singleEval D Sc (b ⊗ₜ[ℚ] g) * singleEval D Sc (a ⊗ₜ[ℚ] f) := by
  change singleEval D Sc (BoxProd.tmulHom (X := obj D Sc (fun _ => 2) [()])
    (Y := obj D Sc (fun _ => 2) [()]) a f ≫ BoxProd.tmulHom b g) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  erw [map_add]
  let a₀ : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2) :=
    proj ℚ 0 (X := (obj D Sc (fun _ => 2) [()]).fst)
      (Y := (obj D Sc (fun _ => 2) [()]).fst) a
  let a₁ : ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2) :=
    proj ℚ 1 (X := (obj D Sc (fun _ => 2) [()]).fst)
      (Y := (obj D Sc (fun _ => 2) [()]).fst) a
  have ha : a₀ + a₁ = a := proj_add_proj (R := ℚ) (X := (obj D Sc (fun _ => 2) [()]).fst)
    (Y := (obj D Sc (fun _ => 2) [()]).fst) a
  let g' : End ((pres D Sc).obj (ob D [()])) := twist ℚ 1 g
  change dotZero D Sc (g * f) • coefficientEval D (b * a₀) +
    dotZero D Sc (g' * f) • coefficientEval D (b * a₁) = _
  have hg' : dotZero D Sc g' = dotZero D Sc g := dotZero_twist D Sc 1 g
  rw [map_mul, map_mul, map_mul, map_mul, hg', ← smul_add,
    ← mul_add, ← map_add, ha]
  change (dotZero D Sc g * dotZero D Sc f) •
    (coefficientEval D b * coefficientEval D a) =
    (dotZero D Sc g • coefficientEval D b) * (dotZero D Sc f • coefficientEval D a)
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem singleEval_comp (f g : hom D Sc (fun _ => 2) [()] [()]) :
    singleEval D Sc (f ≫ g) = singleEval D Sc g * singleEval D Sc f := by
  let A := ELVCoefficientAlgebra (k := ℚ) D (fun _ => 2)
  let B := End ((pres D Sc).obj (ob D [()]))
  suffices h : ∀ x y : A ⊗[ℚ] B,
      singleEval D Sc ((show hom D Sc (fun _ => 2) [()] [()] from x) ≫
        (show hom D Sc (fun _ => 2) [()] [()] from y)) =
      singleEval D Sc y * singleEval D Sc x from h f g
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    erw [Preadditive.add_comp, map_add, map_add, hx, hx', mul_add]
  | tmul a f =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      erw [Preadditive.comp_add, map_add, map_add, hy, hy', add_mul]
    | tmul b g => exact singleEval_comp_tmul D Sc a b f g

private theorem singleEval_relation (hodd : D.parity () = 1) :
    singleEval D Sc (relation D Sc (fun _ => 2) () []) = 0 := by
  rw [single_relation, map_sum]
  simp [singleEval_term, singleCoefficient, hodd, SKM.SYM.elvMonicCoefficient,
    SKM.SYM.elvCoefficient, SKM.SYM.elvChi, exteriorProjection_e]

theorem singleEval_ideal (hodd : D.parity () = 1)
    {f : hom D Sc (fun _ => 2) [()] [()]}
    (hf : f ∈ ideal D Sc (fun _ => 2) [()] [()]) : singleEval D Sc f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    by_cases ht : j :: t = [()]
    · cases j
      have ht' : t = [] := List.cons.inj ht |>.2
      subst t
      rw [singleEval_comp, singleEval_comp, singleEval_relation D Sc hodd, mul_zero, zero_mul]
    · rw [hom_zero_of_ne_single D Sc ht a, Limits.zero_comp, map_zero]
  | zero => exact map_zero _
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul c f _ hf => rw [map_smul, hf, smul_zero]

theorem singleEval_coefficientIdeal
    {f : hom D Sc (fun _ => 2) [()] [()]}
    (hf : f ∈ coefficientHomIdeal D Sc (fun _ => 2) 3 [()] [()]) :
    singleEval D Sc f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, a, ha, l, r, rfl⟩ := hf
    by_cases ht : t = [()]
    · subst t
      have hz : singleEval D Sc (coefficientIdentity D Sc (fun _ => 2) [()]
          (coefficientBasis D ℚ a)) = 0 := by
        change singleEval D Sc (singleTerm D Sc (fun _ => 2) ()
          (elvCoefficientQuotient D (fun _ => 2) (coefficientBasis D ℚ a)) 0) = 0
        rw [singleEval_term, ite_eq_left rfl, coefficientEval_mk]
        exact projection_basis_high D a ha
      rw [singleEval_comp, singleEval_comp, hz, mul_zero, zero_mul]
    · rw [hom_zero_of_ne_single D Sc ht l, Limits.zero_comp, map_zero]
  | zero => exact map_zero _
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul c f _ hf => rw [map_smul, hf, smul_zero]

/-- Evaluation at zero dot and elementary coefficients, retaining the odd generator.
Both ideals are killed with all intermediate words and both surrounding morphisms. -/
def truncatedSingleEval (hodd : D.parity () = 1) :
    TruncatedOld D Sc (fun _ => 2) 3 [()] [()] →ₗ[ℚ]
      ExteriorAlgebra ℚ (OddModule D ℚ) :=
  (truncatedIdeal D Sc (fun _ => 2) 3 [()] [()]).liftQ (singleEval D Sc) (by
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    change singleEval D Sc (a + b) = 0
    rw [map_add, singleEval_ideal D Sc hodd ha, singleEval_coefficientIdeal D Sc hb, add_zero])

@[simp] theorem truncatedSingleEval_delta (hodd : D.parity () = 1) :
    truncatedSingleEval D Sc hodd
      (truncatedSingle D Sc (fun _ => 2) 3 () (delta D ℚ ⟨(), hodd⟩) 0) =
        ExteriorAlgebra.ι ℚ (Finsupp.single ⟨(), hodd⟩ 1) := by
  change singleEval D Sc (singleTerm D Sc (fun _ => 2) ()
    (elvCoefficientQuotient D (fun _ => 2) (delta D ℚ ⟨(), hodd⟩)) 0) = _
  rw [singleEval_term, ite_eq_left rfl, coefficientEval_mk, exteriorProjection_delta]

/-- An odd class survives in the positive-content coefficient-truncated quotient. -/
theorem truncatedSingle_delta_ne_zero (hodd : D.parity () = 1) :
    truncatedSingle D Sc (fun _ => 2) 3 () (delta D ℚ ⟨(), hodd⟩) 0 ≠ 0 := by
  intro hz
  have he := congrArg (truncatedSingleEval D Sc hodd) hz
  rw [truncatedSingleEval_delta, map_zero] at he
  have hz' := (ExteriorAlgebra.ι_eq_zero_iff (R := ℚ) _).mp he
  have hh := congrArg (fun f : OddModule D ℚ => f ⟨(), hodd⟩) hz'
  simp at hh

end OddMath.QuiverHecke.ELVOld
