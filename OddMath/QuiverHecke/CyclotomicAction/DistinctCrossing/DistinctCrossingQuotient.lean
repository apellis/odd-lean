import StringDiagrams.Super.SCat
import OddMath.QuiverHecke.CyclotomicAction.DistinctCrossing.DistinctModuleMate
import OddMath.QuiverHecke.CyclotomicAction.EvenBoundaryRecurrence.EvenCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.InductionRepresentable

/-!
# Distinct crossing

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The mixed crossing after both outer cyclotomic quotients

The full-coefficient crossing isomorphism required in Brundan–Ellis (1.12),
`DeformedActionAssembly.md` §§2–4. Equality (9.3) identifies the output-old
quotient with the first-factor quotient in the independently balanced source.
The literal cup-crossing-cap comparison is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary output postcomposition in the old-only append quotient. -/
def outputPost (i : I) (v : List I) {w z : List I} (r : hom D Sc cutoff w z) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v z :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v z)
    (Linear.rightComp k _ r) (fun _ hh => appendRelations_comp D Sc cutoff i hh r)

@[simp] theorem outputPost_projection (i : I) (v : List I) {w z : List I}
    (r : hom D Sc cutoff w z) (f : hom D Sc cutoff (v ++ [i]) w) :
    outputPost D Sc cutoff i v r (appendProjection D Sc cutoff i v w f) =
      appendProjection D Sc cutoff i v z (f ≫ r) := rfl

/-- Postcomposing a crossing class by an old ideal arrow lands in the
image of the literal first-factor tensor ideal. -/
theorem outputPost_shortCross_mem_map (i j : I) (v w z : List I)
    (r : hom D Sc cutoff w z) (hr : r ∈ ideal D Sc cutoff w z)
    (a : ShortTarget D Sc cutoff i j v w) :
    outputPost D Sc cutoff i v (rightContext D Sc cutoff [j] _ _ r)
      (shortCross D Sc cutoff i j v w a) ∈
      (firstIdeal D Sc cutoff i j v z).map (shortCross D Sc cutoff i j v z) := by
  let S := (firstIdeal D Sc cutoff i j v z).map (shortCross D Sc cutoff i j v z)
  have hzero : S.mkQ ∘ₗ outputPost D Sc cutoff i v
      (rightContext D Sc cutoff [j] _ _ r) ∘ₗ shortCross D Sc cutoff i j v w = 0 := by
    apply BalancedInduction.hom_ext
    intro s c b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j])).mkQ_surjective b
    change S.mkQ (outputPost D Sc cutoff i v _
      (shortCross D Sc cutoff i j v w (shortTensor D Sc cutoff i j v s.word w c _))) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨shortTensor D Sc cutoff i j v s.word z (c ≫ r)
      ((ideal D Sc cutoff v (s.word ++ [j])).mkQ b),
        Submodule.subset_span ⟨s.word, c ≫ r, comp_ideal D Sc cutoff c hr, _, rfl⟩, ?_⟩
    rw [shortCross_tensor, shortCrossPair_mk, shortCross_tensor, shortCrossPair_mk,
      outputPost_projection, rightContext_comp]
    simp only [Category.assoc]
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun hzero a)

/-- The second outer ideal is precisely accounted for by the first tensor ideal. -/
theorem projection_outputOldRelations_mem_map (i j : I) (hij : i ≠ j) (v t : List I)
    (f : hom D Sc cutoff (v ++ [i]) (t ++ [j]))
    (hf : f ∈ outputOldRelations D Sc cutoff j (v ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [j]) f ∈
      (firstIdeal D Sc cutoff i j v t).map (shortCross D Sc cutoff i j v t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, r, hr, c, rfl⟩ := hf
    obtain ⟨a, ha⟩ := shortCross_surjective D Sc cutoff i j hij v s
      (appendProjection D Sc cutoff i v (s ++ [j]) c)
    have hs := outputPost_shortCross_mem_map D Sc cutoff i j v s t r hr a
    rw [ha, outputPost_projection] at hs
    exact hs
  | zero =>
    simpa only [map_zero] using Submodule.zero_mem
      ((firstIdeal D Sc cutoff i j v t).map (shortCross D Sc cutoff i j v t))
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul a b _ hb => simpa only [map_smul] using Submodule.smul_mem _ a hb

/-- Exact kernel after identifying both outer quotient spans by (9.3). -/
theorem ker_canonical_shortCross (i j : I) (hij : i ≠ j) (v t : List I) :
    LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ
      shortCross D Sc cutoff i j v t) = firstIdeal D Sc cutoff i j v t := by
  apply le_antisymm
  · intro a ha
    obtain ⟨f, hf⟩ := appendProjection_surjective D Sc cutoff i v (t ++ [j])
      (shortCross D Sc cutoff i j v t a)
    have hi : f ∈ ideal D Sc cutoff (v ++ [i]) (t ++ [j]) := by
      have hz := LinearMap.mem_ker.mp ha
      change canonicalAppendTarget D Sc cutoff i v (t ++ [j])
        (shortCross D Sc cutoff i j v t a) = 0 at hz
      rw [← hf, canonicalAppendTarget_projection] at hz
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [ideal_eq_appendRelations_sup_outputOldRelations D Sc cutoff i j hij v t] at hi
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hi
    have he : appendProjection D Sc cutoff i v (t ++ [j]) c =
        shortCross D Sc cutoff i j v t a := by
      rw [← hf, ← hbc, map_add, (appendProjection_eq_zero_iff D Sc cutoff i v _ b).mpr hb,
        zero_add]
    obtain ⟨a', ha', h⟩ := projection_outputOldRelations_mem_map D Sc cutoff i j hij v t c hc
    have hsame : a' = a := shortCross_injective D Sc cutoff i j hij v t (h.trans he)
    exact hsame ▸ ha'
  · intro a ha
    rw [shortCross_quotient_square]
    change toCyclotomic D Sc cutoff i j v t (q D Sc cutoff i j v t a) = 0
    rw [LinearMap.mem_ker.mp (firstIdeal_le_ker_q D Sc cutoff i j v t ha), map_zero]

/-- Injectivity after both outer quotients, without tensor flatness. -/
theorem toCyclotomic_injective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Injective (toCyclotomic D Sc cutoff i j v t) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i j v t z
  have ha : a ∈ LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ
      shortCross D Sc cutoff i j v t) := by
    rw [shortCross_quotient_square]
    exact hz
  rw [ker_canonical_shortCross D Sc cutoff i j hij v t] at ha
  exact firstIdeal_le_ker_q D Sc cutoff i j v t ha

/-- Surjectivity after both outer quotients. -/
theorem toCyclotomic_surjective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Surjective (toCyclotomic D Sc cutoff i j v t) := by
  intro z
  obtain ⟨a, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [j]) z
  obtain ⟨b, rfl⟩ := shortCross_surjective D Sc cutoff i j hij v t a
  refine ⟨q D Sc cutoff i j v t b, ?_⟩
  exact (LinearMap.congr_fun (shortCross_quotient_square D Sc cutoff i j v t) b).symm

/-- The prescribed balanced crossing is an isomorphism in every distinct corner. -/
def cyclotomicEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    Source D Sc cutoff i j v t ≃ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff i j v t)
    ⟨toCyclotomic_injective D Sc cutoff i j hij v t,
      toCyclotomic_surjective D Sc cutoff i j hij v t⟩

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The prescribed distinct mate and the cyclotomic crossing decoder

Brundan–Ellis (1.12), via `DeformedActionAssembly.md` §4: the literal positive
cup-crossing-cap equals the checked crossing isomorphism after canonical J.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev ModuleSource (i j : I) (v t : List I) :=
  ((BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff j)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)

/-- The canonical coefficient-zero identification, induced from the fixed module iso. -/
def moduleSourceZeroEquiv (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] SourceWithParity D Sc cutoff 0 i j v t :=
  moduleIsoLinearEquiv
    (((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientRestrictionModuleIso D Sc cutoff j v)).symm)
    (⟨t⟩ : OldCategory D Sc cutoff)

private theorem coefficientRestriction_inv_app (j : I) (v : List I) (q : ZMod 2)
    (s : OldCategory D Sc cutoff) :
    (coefficientRestrictionModuleIso D Sc cutoff j v).inv.app q s =
      if q = 0 then LinearMap.id else 0 := rfl

@[simp] theorem moduleSourceZeroEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    moduleSourceZeroEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b) =
      parityTensor D Sc cutoff 0 i j v s t g b := by
  have h := BalancedInduction.moduleMap_total_tensor (append D Sc cutoff i)
    (coefficientRestrictionModuleIso D Sc cutoff j v).inv
    (⟨t⟩ : OldCategory D Sc cutoff) (⟨s⟩ : OldCategory D Sc cutoff) g b
  rw [coefficientRestriction_inv_app, coefficientRestriction_inv_app] at h
  simp only [↓reduceIte, one_ne_zero] at h
  change _ = BalancedInduction.tensor (append D Sc cutoff i)
      (coefficientZeroModule D Sc cutoff j v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i) (coefficientZeroModule D Sc cutoff j v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) (twist k 1 g) (0 : Old D Sc cutoff v (s ++ [j])) at h
  rw [BalancedInduction.tensor_zero_right, add_zero] at h
  exact h

/-- The prescribed J twists the whole first factor, including exterior coefficients. -/
def moduleSourceParityEquiv (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] Source D Sc cutoff i j v t :=
  (moduleSourceZeroEquiv D Sc cutoff i j v t).trans (sourceParityEquiv D Sc cutoff i j v t)

@[simp] theorem moduleSourceParityEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    moduleSourceParityEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b) =
      tensor D Sc cutoff i j v s t
        (oldTwist D Sc cutoff (D.parity i * D.parity j) (s ++ [i]) t g) b := by
  rw [moduleSourceParityEquiv, LinearEquiv.trans_apply, moduleSourceZeroEquiv_tensor]
  change parityTransport D Sc cutoff 0 _ i j v t (parityTensor D Sc cutoff 0 i j v s t g b) = _
  rw [parityTransport_tensor, zero_add]
  rfl

theorem pairing_eq_append_comp (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    pairing D Sc cutoff i j v s t g b =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫
        crossComponent D Sc cutoff i j ⟨s⟩ ≫
        (append D Sc cutoff j).map
          (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
  rfl

/-- Co-Yoneda evaluation of the literal rectangular mate, with its target
endpoint fixed before comparing source carriers. -/
def evaluatedMate (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (OldInductionRepresentable.equiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)).toLinearMap ∘ₗ
    SVec.toLinearMap (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total ⟨t⟩)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The ordinary-right kernel of the prescribed distinct mate

The arbitrary-module extension in `DeformedActionAssembly.md` §4, for
Brundan–Ellis (1.12), requires naturality under literal ordinary right
precomposition. The kernel map below is the evaluated categorical mate,
with its checked PBW inverse. No signed representing map is substituted
for the ordinary-right kernel action.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The source coefficient tensor retains ordinary precomposition on its
second factor. -/
abbrev sourceKernel (i j : I) (t : OldCategory D Sc cutoff) :=
  MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t

abbrev targetKernel (i j : I) (t : OldCategory D Sc cutoff) :=
  BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
    ((append D Sc cutoff j).obj t)

/-- The prescribed crossing-mate formula, before choosing its PBW inverse. -/
def kernelMateComponent (i j : I) (v t : OldCategory D Sc cutoff) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) v t →ₗ[k]
      ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff j).obj t) :=
  MixedIndResKernel.mateComponent (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) v t

@[simp] theorem kernelMateComponent_tensor (i j : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff j).obj s) :
    kernelMateComponent D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      (append D Sc cutoff i).map b ≫ crossComponent D Sc cutoff i j s ≫
        twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g) :=
  MixedIndResKernel.mateComponent_tensor (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) v s t g b

/-- Ordinary-right naturality holds for every old arrow, including odd
and inhomogeneous full exterior coefficients. -/
theorem kernelMateComponent_precompose (i j : I) (u v t : OldCategory D Sc cutoff)
    (r : u ⟶ v) :
    kernelMateComponent D Sc cutoff i j u t ∘ₗ
      MixedIndResKernel.precompose (k := k) (append D Sc cutoff i) (append D Sc cutoff j) r t =
      (Linear.leftComp k _ ((append D Sc cutoff i).map r)) ∘ₗ
        kernelMateComponent D Sc cutoff i j v t :=
  MixedIndResKernel.mateComponent_precompose (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) u v t r

/-- The zero-shift coefficient is identified before induction, using only
an ordinary coefficient natural isomorphism. -/
def kernelSourceCoefficientIso (j : I) (v : List I) :
    ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ≅
      coefficient D Sc cutoff 0 j v :=
  (coefficientRestrictionIso D Sc cutoff j v).symm

def kernelSourceZeroEquiv (i j : I) (v t : List I) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) ⟨v⟩ ⟨t⟩ ≃ₗ[k]
      SourceWithParity D Sc cutoff 0 i j v t :=
  BalancedInduction.coefficientEquiv (append D Sc cutoff i)
    (kernelSourceCoefficientIso D Sc cutoff j v) ⟨t⟩

@[simp] theorem kernelSourceZeroEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    kernelSourceZeroEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b) =
      parityTensor D Sc cutoff 0 i j v s t g b := by
  exact BalancedInduction.coefficientEquiv_tensor (append D Sc cutoff i)
    (kernelSourceCoefficientIso D Sc cutoff j v) ⟨t⟩ ⟨s⟩ g b

/-- The full quotient decoder and canonical J provide this kernel equivalence. -/
def kernelCrossingEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) ⟨v⟩ ⟨t⟩ ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (kernelSourceZeroEquiv D Sc cutoff i j v t).trans
    ((sourceParityEquiv D Sc cutoff i j v t).trans (cyclotomicEquiv D Sc cutoff i j hij v t))

theorem kernelCrossingEquiv_tensor (i j : I) (hij : i ≠ j) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    kernelCrossingEquiv D Sc cutoff i j hij v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b) =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫
      twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map
        (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g) := by
  change toCyclotomic D Sc cutoff i j v t
    (parityTransport D Sc cutoff 0 (D.parity i * D.parity j) i j v t
      (kernelSourceZeroEquiv D Sc cutoff i j v t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b))) = _
  rw [kernelSourceZeroEquiv_tensor, parityTransport_tensor, zero_add]
  change toCyclotomic D Sc cutoff i j v t
    (tensor D Sc cutoff i j v s t (oldTwist D Sc cutoff _ (s ++ [i]) t g) b) = _
  rw [toCyclotomic_tensor, pairing_eq_append_comp]
  have h := map_twist (R := k) (append D Sc cutoff j) (D.parity i * D.parity j)
    (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g
  rw [oldCategory_twist] at h
  exact congrArg (fun f :
      (append D Sc cutoff j).obj ((append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) ⟶
        (append D Sc cutoff j).obj (⟨t⟩ : OldCategory D Sc cutoff) =>
    (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
      (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫ f) h

private theorem kernelMateComponent_eq (i j : I) (hij : i ≠ j) (v t : List I) :
    kernelMateComponent D Sc cutoff i j ⟨v⟩ ⟨t⟩ =
      (kernelCrossingEquiv D Sc cutoff i j hij v t).toLinearMap := by
  apply BalancedInduction.hom_ext
  intro s g b
  rcases s with ⟨s⟩
  have hK := kernelMateComponent_tensor D Sc cutoff i j ⟨v⟩ ⟨s⟩ ⟨t⟩ g b
  have hE := kernelCrossingEquiv_tensor D Sc cutoff i j hij v s t g b
  exact hK.trans hE.symm

/-- Bijectivity of the literal ordinary-right kernel map follows from the
constructed PBW quotient decoder and source parity transport. -/
theorem kernelMateComponent_bijective (i j : I) (hij : i ≠ j) (v t : OldCategory D Sc cutoff) :
    Function.Bijective (kernelMateComponent D Sc cutoff i j v t) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  rw [kernelMateComponent_eq D Sc cutoff i j hij v t]
  exact (kernelCrossingEquiv D Sc cutoff i j hij v t).bijective

private def kernelNatTrans
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v)) : K ⟶ L where
  app v := ModuleCat.ofHom (f v)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact hf a

/-- The literal mate as a natural transformation of ordinary-right kernels. -/
def kernelMate (i j : I) (t : OldCategory D Sc cutoff) :
    sourceKernel D Sc cutoff i j t ⟶ targetKernel D Sc cutoff i j t :=
  kernelNatTrans (sourceKernel D Sc cutoff i j t) (targetKernel D Sc cutoff i j t)
    (fun v => kernelMateComponent D Sc cutoff i j v.unop t)
    (fun {v w} r => kernelMateComponent_precompose D Sc cutoff i j w.unop v.unop t r.unop)

/-- Inverse naturality follows from the constructed component inverse. -/
def kernelMateIso (i j : I) (hij : i ≠ j) (t : OldCategory D Sc cutoff) :
    sourceKernel D Sc cutoff i j t ≅ targetKernel D Sc cutoff i j t :=
  BalancedKernelTensor.coefficientIso (kernelMate D Sc cutoff i j t)
    (fun v => kernelMateComponent_bijective D Sc cutoff i j hij v.unop t)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The prescribed distinct mate on arbitrary old modules

Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4: tensor the ordinary-right
coefficient kernel isomorphism with the entire input module. The explicit
coend comparison identifies the resulting map with the fixed rectangular
cup-crossing-cap. No flatness or projectivity is required.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The fixed categorical mate with source and target coends exposed. -/
def moduleMateLinear (i j : I) (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) :=
  BalancedInduction.orderedMixedMateCoend (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) N t

@[simp] theorem moduleMateLinear_tensor (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : N.obj ((append D Sc cutoff j).obj s)) :
    moduleMateLinear D Sc cutoff i j N t
      (BalancedInduction.tensor (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj s)
        (crossComponent D Sc cutoff i j s ≫
          twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g)) b :=
  BalancedInduction.orderedMixedMateCoend_tensor (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) N s t g b

private theorem moduleMate_evaluate (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (v t : OldCategory D Sc cutoff)
    (m : N.obj v) :
    moduleMateLinear D Sc cutoff i j N t ∘ₗ
      MixedIndResKernel.evaluate (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor v t m =
      BalancedInduction.inclusion (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) v ∘ₗ
        (TensorProduct.mk k _ _).flip m ∘ₗ kernelMateComponent D Sc cutoff i j v t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, MixedIndResKernel.evaluate_tensor,
    moduleMateLinear_tensor, kernelMateComponent_tensor, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  change BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor
      ((append D Sc cutoff j).obj s) _ (N.map b m) =
    BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor v _ m
  exact (BalancedInduction.balance (append D Sc cutoff i) N.toFunctor b
    (crossComponent D Sc cutoff i j s ≫
      twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g)) m).symm

/-- Tensor the constructed ordinary-right kernel inverse with any old module. -/
def moduleMateUnderlyingEquiv (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) t ≃ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) :=
  (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t).symm |>.trans
    ((BalancedKernelTensor.equiv N.toFunctor (kernelMateIso D Sc cutoff i j hij t)).trans
      (BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) N.toFunctor
        ((append D Sc cutoff j).obj t)))

private theorem moduleMateUnderlyingEquiv_forward_tensor (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (v t : OldCategory D Sc cutoff)
    (x : MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) v t)
    (m : N.obj v) :
    moduleMateUnderlyingEquiv D Sc cutoff i j hij N t
      (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t
        (BalancedKernelTensor.tensor (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor v x m)) =
      BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor v
        (kernelMateComponent D Sc cutoff i j v t x) m := by
  change ((MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t).symm.trans
    ((BalancedKernelTensor.equiv N.toFunctor (kernelMateIso D Sc cutoff i j hij t)).trans
      (BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) N.toFunctor
        ((append D Sc cutoff j).obj t))))
    ((MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t)
      (BalancedKernelTensor.tensor (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor v x m)) = _
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    BalancedKernelTensor.equiv_tensor, BalancedKernelTensor.inductionKernelEquiv_tensor]
  rfl

private theorem equiv_eq_on_kernel_tensors
    {C : Type u} [Category.{u} C] (K : Cᵒᵖ ⥤ ModuleCat k) (M : C ⥤ SVec k)
    {V W : Type u} [AddCommMonoid V] [Module k V] [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (f : V →ₗ[k] W) (q : BalancedKernelTensor.Obj K M ≃ₗ[k] V)
    (h : ∀ v (x : K.obj (op v)) (m : M.obj v),
      e (q (BalancedKernelTensor.tensor K M v x m)) =
        f (q (BalancedKernelTensor.tensor K M v x m))) : e.toLinearMap = f := by
  apply LinearMap.cancel_right q.surjective |>.mp
  apply BalancedKernelTensor.hom_ext
  intro v x m
  exact h v x m

private theorem coend_left_apply
    {C B : Type u} [Category.{u} C] [Category.{u} B] [Preadditive B] [Linear k B]
    (J : C ⥤ B) (M : C ⥤ SVec k) (w : B) (v : C)
    {V : Type u} [AddCommMonoid V] [Module k V] (L : V →ₗ[k] (J.obj v ⟶ w))
    (m : M.obj v) (x : V) :
    (BalancedInduction.inclusion J M w v ∘ₗ (TensorProduct.mk k _ _).flip m ∘ₗ L) x =
      BalancedInduction.tensor J M v (L x) m := rfl

/-- The quotient-level inverse has exactly the prescribed categorical forward map. -/
theorem moduleMateUnderlyingEquiv_toLinearMap (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    (moduleMateUnderlyingEquiv D Sc cutoff i j hij N t).toLinearMap =
      moduleMateLinear D Sc cutoff i j N t := by
  apply equiv_eq_on_kernel_tensors (k := k)
    (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor
    (moduleMateUnderlyingEquiv D Sc cutoff i j hij N t) (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t)
  intro v x m
  have hL := moduleMateUnderlyingEquiv_forward_tensor D Sc cutoff i j hij N v t x m
  have hF := congrArg (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.equiv_tensor (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t v x m)
  have hA := LinearMap.congr_fun (moduleMate_evaluate D Sc cutoff i j N v t m) x
  have hA0 := (LinearMap.comp_apply (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.evaluate (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor v t m) x).symm.trans hA
  have hA1 := hA0.trans (coend_left_apply (k := k) (append D Sc cutoff i) N.toFunctor
    ((append D Sc cutoff j).obj t) v (kernelMateComponent D Sc cutoff i j v t) m x)
  exact hL.trans (hF.trans hA1).symm

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.Distinct
end

end
