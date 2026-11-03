import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleQuadratic

/-! # The distinct-colour quadratic in the untruncated old quotient

Brundan–Ellis (1.7) and DeformedActionAssembly §6 (9): the literal
positive old crossings compose to the prescribed ordered dot polynomial.
On the probe parameter family `parameterTwist D Sc`, the crossing-square
sign recovers the signed evaluation with the original parameters `Sc`.
No truncation, quadratic premise or action premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem crossLast_quadratic (v : List I) {i j : I} (hij : i ≠ j) :
    crossLast D Sc v j i ≫ crossLast D Sc v i j =
      pairQuadPoly D Sc j i
        (dotE D Sc (v ++ [j] ++ [i]) v.length)
        (dotE D Sc (v ++ [j] ++ [i]) (v.length + 1)) := by
  rw [crossLast, crossLast, cl_comp]
  have aux {t : List I} (ht : t = v ++ [j,i] ++ [])
      (h : SChain t (pl t [.cross v.length, .cross v.length]) t) :
      cl D Sc t t [.cross v.length, .cross v.length] h =
        pairQuadPoly D Sc j i (dotE D Sc t v.length) (dotE D Sc t (v.length + 1)) := by
    subst t
    unfold pairQuadPoly
    split_ifs with hd
    · exact cross_cross_ne_zero D Sc v [] hij.symm hd h
    · exact cross_cross_ne D Sc v [] hij.symm hd h
  exact aux (by simp [List.append_assoc]) _

/-- The two literal positive distinct crossings satisfy the full source quadratic. -/
theorem crossComponent_quadratic {i j : I} (hij : i ≠ j)
    (s : OldCategory D Sc cutoff) :
    crossComponent D Sc cutoff i j s ≫ crossComponent D Sc cutoff j i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (pairQuadPoly D Sc (R := End ((pres D Sc).obj (ob D (s.word ++ [j] ++ [i])))) j i
          (dotE D Sc (s.word ++ [j] ++ [i]) s.word.length)
          (dotE D Sc (s.word ++ [j] ++ [i]) (s.word.length + 1)))) := by
  change oldComp D Sc cutoff (s.word ++ [j] ++ [i]) (s.word ++ [i] ++ [j])
    (s.word ++ [j] ++ [i]) ((ideal D Sc cutoff _ _).mkQ _)
    ((ideal D Sc cutoff _ _).mkQ _) = _
  rw [oldComp_mk, ← affineUnit_comp, crossLast_quadratic D Sc s.word hij]
  rfl

/-- The probe's parameter involution leaves exactly the original ordered signed polynomial. -/
theorem crossComponent_parameterUntwist {i j : I} (hij : i ≠ j)
    (s : OldCategory D (parameterTwist D Sc) cutoff) :
    sign k (D.parity i * D.parity j) •
        (crossComponent D (parameterTwist D Sc) cutoff i j s ≫
          crossComponent D (parameterTwist D Sc) cutoff j i s) =
      (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
        (affineUnit D (parameterTwist D Sc) cutoff _ _
          (elvSignedPairQuadEval D Sc
            (R := End ((pres D (parameterTwist D Sc)).obj (ob D (s.word ++ [j] ++ [i])))) j i
            (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) s.word.length)
            (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) (s.word.length + 1)))) := by
  rw [crossComponent_quadratic D _ cutoff hij]
  have h := pairQuadPoly_parameterTwist_reversed_eval D Sc
    (R := End ((pres D (parameterTwist D Sc)).obj (ob D (s.word ++ [j] ++ [i])))) hij
    (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) s.word.length)
    (dotE D (parameterTwist D Sc) (s.word ++ [j] ++ [i]) (s.word.length + 1))
  simpa only [map_smul, sign_eq_zsign] using congrArg
    (fun a => (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
      (affineUnit D (parameterTwist D Sc) cutoff _ _ a)) h

/-- Original-parameter signed polynomial on the two appended source positions. -/
def signedQuadraticComponent (i j : I)
    (s : OldCategory D (parameterTwist D Sc) cutoff) :
    End (((append D (parameterTwist D Sc) cutoff i) ⋙
      (append D (parameterTwist D Sc) cutoff j)).obj s) :=
  (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
    (affineUnit D (parameterTwist D Sc) cutoff _ _
      (elvSignedPairQuadEval D Sc
        (R := End ((pres D (parameterTwist D Sc)).obj (ob D (s.word ++ [i] ++ [j])))) i j
        (dotE D (parameterTwist D Sc) (s.word ++ [i] ++ [j]) s.word.length)
        (dotE D (parameterTwist D Sc) (s.word ++ [i] ++ [j]) (s.word.length + 1))))

private theorem twist_cross_kernel {C : Type u} [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {x y t : C} {p : ZMod 2}
    (a : y ⟶ x) (b : x ⟶ y) (f : x ⟶ t)
    (ha : a ∈ parity (R := k) y x p) :
    b ≫ twist k p (𝟙 y ≫ a ≫ twist k p f) = (sign k p • (b ≫ a)) ≫ f := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  rw [Category.id_comp, twist_comp, twist_of_mem _ ha, ← twist_add,
    hpp, twist_zero, hsq, Linear.smul_comp, Linear.comp_smul]
  rw [Linear.smul_comp]
  exact congrArg (fun q => sign k p • q) (Category.assoc b a f).symm

/-- The actual balanced double induction crossing square evaluates the same polynomial.
The tensor coefficient is arbitrary, so its full parity twist is retained and cancelled. -/
theorem mixedCrossComponent_quadratic_tensor {i j : I} (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D (parameterTwist D Sc) cutoff) (SVec k))
    (s w t : OldCategory D (parameterTwist D Sc) cutoff)
    (g : (append D (parameterTwist D Sc) cutoff j).obj w ⟶ t)
    (h : (append D (parameterTwist D Sc) cutoff i).obj s ⟶ w) (b : N.obj s) :
    (BalancedInduction.mixedCrossComponent
        (append D (parameterTwist D Sc) cutoff j) (append D (parameterTwist D Sc) cutoff i)
        (cross_supernatural D (parameterTwist D Sc) cutoff j i) N).total t
      ((BalancedInduction.mixedCrossComponent
          (append D (parameterTwist D Sc) cutoff i) (append D (parameterTwist D Sc) cutoff j)
          (cross_supernatural D (parameterTwist D Sc) cutoff i j) N).total t
        (BalancedInduction.tensor (append D (parameterTwist D Sc) cutoff j)
          (BalancedInduction.induced (append D (parameterTwist D Sc) cutoff i) N).toFunctor
          w g (BalancedInduction.tensor (append D (parameterTwist D Sc) cutoff i)
            N.toFunctor s h b))) =
      BalancedInduction.tensor (append D (parameterTwist D Sc) cutoff j)
        (BalancedInduction.induced (append D (parameterTwist D Sc) cutoff i) N).toFunctor
        ((append D (parameterTwist D Sc) cutoff i).obj s)
        (signedQuadraticComponent D Sc cutoff i j s ≫
          ((append D (parameterTwist D Sc) cutoff j).map h ≫ g))
        (BalancedInduction.tensor (append D (parameterTwist D Sc) cutoff i)
          N.toFunctor s (𝟙 _) b) := by
  have hp : D.parity j * D.parity i = D.parity i * D.parity j := mul_comm _ _
  have hq := crossComponent_parameterUntwist D Sc cutoff hij.symm s
  rw [hp] at hq
  change sign k (D.parity i * D.parity j) •
      (crossComponent D (parameterTwist D Sc) cutoff j i s ≫
        crossComponent D (parameterTwist D Sc) cutoff i j s) =
    signedQuadraticComponent D Sc cutoff i j s at hq
  have hk : crossComponent D (parameterTwist D Sc) cutoff j i s ≫
        twist k (D.parity j * D.parity i)
          ((append D (parameterTwist D Sc) cutoff i).map (𝟙 _) ≫
            crossComponent D (parameterTwist D Sc) cutoff i j s ≫
              twist k (D.parity i * D.parity j)
                ((append D (parameterTwist D Sc) cutoff j).map h ≫ g)) =
      signedQuadraticComponent D Sc cutoff i j s ≫
        ((append D (parameterTwist D Sc) cutoff j).map h ≫ g) := by
    rw [CategoryTheory.Functor.map_id, hp]
    exact (twist_cross_kernel
      (crossComponent D (parameterTwist D Sc) cutoff i j s)
      (crossComponent D (parameterTwist D Sc) cutoff j i s)
      ((append D (parameterTwist D Sc) cutoff j).map h ≫ g)
      ((cross_supernatural D (parameterTwist D Sc) cutoff i j).mem s)).trans
      (congrArg (fun q => q ≫ ((append D (parameterTwist D Sc) cutoff j).map h ≫ g)) hq)
  rw [BalancedInduction.mixedCrossComponent_total_tensor,
    BalancedInduction.mixedCrossComponent_total_tensor]
  exact congrArg (fun q => BalancedInduction.tensor
    (append D (parameterTwist D Sc) cutoff j)
    (BalancedInduction.induced (append D (parameterTwist D Sc) cutoff i) N).toFunctor
    ((append D (parameterTwist D Sc) cutoff i).obj s) q
    (BalancedInduction.tensor (append D (parameterTwist D Sc) cutoff i)
      N.toFunctor s (𝟙 _) b)) hk

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
