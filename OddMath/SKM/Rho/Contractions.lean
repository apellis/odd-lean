import OddMath.SKM.Rho.Extension

/-!
# Contractions for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/

noncomputable section
namespace OddMath.SKM.RhoMates
open CategoryTheory StringDiagrams Presentation RhoWords RhoEvaluator RhoInversionKernel RhoTwo RhoExtension
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem unmate_mate (μ : X) {U V U' V' : List (Letter I)}
    {CuU CuV CaU CaV A : List (LayerData I)}
    (hCuV : SChain [] CuV (V' ++ V))
    (hCaU : SChain (U ++ U') CaU []) (hCaV : SChain (V ++ V') CaV [])
    (hA : SChain U A V) (eCuV : parsum D CuV = 0) (eCaU : parsum D CaU = 0)
    (zU : ZigE D Sc CuU CaU U) (zV : ZigE D Sc CuV CaV V) :
    cl D Sc μ U V (CuV.map (whL U []) ++
      (mateB CuU A CaV U' V').map (whL U V) ++ CaU.map (whL [] V)) =
      cl D Sc μ U V A := by
  have hB : SChain (U ++ V') (A.map (whL [] V') ++ CaV) [] :=
    (hA.wh [] V' (by simp) (by simp)).append hCaV
  have swap := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := U) (T := V)
    (CuV.map (whL U []) ++ CuU.map (whL U (V' ++ V))) [] [] [] V
    hCaU hB (Or.inl eCaU)
  have step1 : cl D Sc μ U V (CuV.map (whL U []) ++
      (mateB CuU A CaV U' V').map (whL U V) ++ CaU.map (whL [] V)) =
    cl D Sc μ U V (CuV.map (whL U []) ++ CuU.map (whL U (V' ++ V)) ++
      CaU.map (whL [] (U ++ (V' ++ V))) ++ (A.map (whL [] V') ++ CaV).map (whL [] V)) := by
    simpa [mateB, List.append_assoc] using swap.symm
  rw [step1]
  have hz := cl_zigE_ctx zU μ (s₀ := U) (t₀ := V) (CuV.map (whL U []))
    ((A.map (whL [] V') ++ CaV).map (whL [] V)) [] (V' ++ V)
    (hCuV.wh U [] (by simp) (by simp))
    (hB.wh [] V (by simp [List.append_assoc]) (by simp))
  simp only [List.nil_append] at hz
  rw [hz]
  have swap2 := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := U) (T := V)
    [] (CaV.map (whL [] V)) [] [] [] hA hCuV (Or.inr eCuV)
  have step2 : cl D Sc μ U V (CuV.map (whL U []) ++
      (A.map (whL [] V') ++ CaV).map (whL [] V)) =
    cl D Sc μ U V (A ++ CuV.map (whL V []) ++ CaV.map (whL [] V)) := by
    simpa [List.append_assoc] using swap2.symm
  rw [step2]
  simpa using cl_zigE_ctx zV μ (s₀ := U) (t₀ := V) A [] [] []
    (by simpa using hA) (by simp [SChain])

end OddMath.SKM.RhoMates
