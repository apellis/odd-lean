import OddMath.QuiverHecke.SwappedAssembly.SupportedMatrixModules

/-! # Presentation equations on the supported matrix modules

The presentation attachment of SwappedActionAssembly F4/(A1). The
supported path-Hom charts identify every matrix module with the chosen
factor module. Keeping its native ambient operators transports every
whiskered presentation equation, with no new support-closure premise.
The final functor construction is intermediate: it takes the original
presentation obligations, including the still separate central inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly

namespace ModuleInterpretation
universe w u₀ u₁ u₂ v₀ v₁ v₂ v₃
variable {S : Signature.{u₀,u₁,u₂}} {R : Type w} [CommRing R]
  {ι : Type v₀} {V : Type v₁} [AddCommGroup V] [Module R V]
  {M : ι → Type v₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (Q : LocalInterpretation S R V M)
  (N : ι → Type v₃) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (e : ∀ i, N i ≃ₗ[R] M i)

/-- Change the displayed modules by their computed charts while keeping the ambient operators. -/
def congrModules : LocalInterpretation S R V N where
  κ := Q.κ
  ext i := Q.ext i ∘ₗ (e i).toLinearMap
  res i := (e i).symm.toLinearMap ∘ₗ Q.res i
  op := Q.op
  res_comp_ext i := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Q.res_ext_apply,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply]
  res_op_ext_res L hv := by
    ext x
    change (e _).symm (Q.res _ (Q.op L (Q.ext _ ((e _) ((e _).symm (Q.res _ x)))))) =
      (e _).symm (Q.res _ (Q.op L x))
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg (e _).symm (LinearMap.congr_fun (Q.res_op_ext_res L hv) x)

/-- No ambient operator changes under the matrix-module charts. -/
theorem congrModules_opList (ls : List (Layer S)) :
    (congrModules Q N e).opList ls = Q.opList ls := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    change (congrModules Q N e).opList ls ∘ₗ Q.op L = Q.opList ls ∘ₗ Q.op L
    rw [ih]

/-- Every whiskered linear combination is evaluated by conjugating the native map. -/
theorem congrModules_evalW_apply (i j : ι) (u : Obj S) (v : List S.Colour)
    {a b : Obj S} (f : LinDiagram R a b) (x : N i) :
    (congrModules Q N e).evalW i j u v f x =
      (e j).symm (Q.evalW i j u v f ((e i) x)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [LinearMap.add_apply, hf, hg, map_add]
  | single d r =>
    simp only [LocalInterpretation.evalW_single, LinearMap.smul_apply, LinearMap.comp_apply,
      congrModules_opList]
    change r • (e j).symm (Q.res j (Q.opList _ (Q.ext i ((e i) x)))) =
      (e j).symm (r • Q.res j (Q.opList _ (Q.ext i ((e i) x))))
    exact ((e j).symm.map_smul r _).symm

/-- The computed module charts both preserve and reflect all whiskered equations. -/
theorem congrModules_evalW_eq_zero_iff (i j : ι) (u : Obj S) (v : List S.Colour)
    {a b : Obj S} (f : LinDiagram R a b) :
    (congrModules Q N e).evalW i j u v f = 0 ↔ Q.evalW i j u v f = 0 := by
  constructor
  · intro h
    ext x
    apply (e j).symm.injective
    have hx := LinearMap.congr_fun h ((e i).symm x)
    rw [congrModules_evalW_apply] at hx
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.zero_apply, map_zero] using hx
  · intro h
    ext x
    rw [congrModules_evalW_apply, h]
    simp

end ModuleInterpretation

universe uAction vAction
private def upwardModuleActionOfFunctor
    {I X k : Type uAction} [AddCommGroup X] [CommRing k]
    (D : Datum I X) (Sc : Scalars D k)
    (F : (SKM.pres D Sc).Presented ⥤ ModuleCat.{vAction} k)
    [F.Additive] [F.Linear k] (μ : X) : UpwardModuleAction D Sc μ where
  V t := F.obj ((SKM.pres D Sc).obj (SKM.ob D μ (upWord t)))
  act t t' :=
    { toFun f := (F.map f).hom
      map_add' f g := by rw [Functor.map_add, ModuleCat.hom_add]
      map_smul' r f := by rw [Functor.map_smul, ModuleCat.hom_smul]; rfl }
  act_id t := by ext x; simp
  act_comp t t' t'' f g := by ext x; simp

namespace SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance presentationHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]

/-- The literal supported matrix modules interpreted by the chosen factor operators. -/
def interpretation (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X) (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (gens : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).Generators) :=
  ModuleInterpretation.congrModules (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)) gens).toLocal
    (matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys)
    (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys)

/-- All already-proved native relation equations hold on the supported matrices. -/
theorem interpretation_evalW_eq_zero_iff (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X) (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (gens : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).Generators)
    (i j u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour)
    {a b : Obj (SKM.sig D)} (f : LinDiagram k a b) :
    (interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens).evalW i j u v f = 0 ↔
      (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)) gens).toLocal.evalW i j u v f = 0 :=
  ModuleInterpretation.congrModules_evalW_eq_zero_iff _ _ _ i j u v f

/-- Intermediate assembly from the native presentation obligations. This does not construct
the still separate central inverse, but adds no supported-category hypothesis. -/
theorem respectsOfObligations (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X) (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (gens : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).Generators) (h : SwappedObligations Sc (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)) gens)) :
    (SKM.pres D Sc).Respects
      (interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens).functor := by
  apply LocalInterpretation.respects_of
  · intro r u v hw
    exact (interpretation_evalW_eq_zero_iff D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens _ _ u v _).2
      (h.relHolds r u v hw)
  · intro x hx u v hw
    exact (interpretation_evalW_eq_zero_iff D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens _ _ u v _).2
      (h.interchange x hx u v hw)

/-- The supported functor from the presented category, conditional only on the original
native obligations. This intermediate construction asserts no new inverse theorem. -/
def functorOfObligations (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X) (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (gens : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).Generators) (h : SwappedObligations Sc (((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)) gens)) :
    (SKM.pres D Sc).Presented ⥤ ModuleCat.{u + 1} k :=
  (SKM.pres D Sc).lift (respectsOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens h)

/-- The supported upward module action required by bounded vacuum observations.
This is intermediate and retains precisely the original native obligations. -/
def upwardModuleActionOfObligations (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ)
    (bound : ℕ) (ΛP ΛR : X) (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (gens : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).Generators)
    (h : SwappedObligations Sc ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).layerRep
      (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens)) (μ : X) :
    UpwardModuleAction D Sc μ := by
  let F := functorOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens h
  let _ : F.Additive := Presentation.lift_additive
    (respectsOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens h)
  let _ : F.Linear k := Presentation.lift_linear
    (respectsOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens h)
  exact upwardModuleActionOfFunctor D Sc F μ

end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
