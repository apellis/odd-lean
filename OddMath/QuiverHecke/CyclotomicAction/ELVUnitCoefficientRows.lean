import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixInverse

/-! # Coefficient extraction from the prescribed unit-matrix inverse

Research issue #345, toward the normalized vacuum bubbles in
`docs/Nondegeneracy/SwappedVacuumNonpositiveBubbles.md`, §§2–4.
The inverse rows of the actual ordinary-unit/dotted-unit matrix give the
coefficient-extraction window on every old supermodule. The rows retain
the prescribed parity-shifted source coordinates; no independent
coefficient-extraction functional or basis hypothesis is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

/-- A selected coefficient row of the prescribed inverse. Its target is the
literal shifted source summand, including the mate summand at `none`. -/
def moduleUnitCoefficientRow (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I)))) :
    mateTargetSpace D Sc cutoff i M t ⟶
      (unitMatrixFamily D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t :=
  (LinearMap.proj a).comp ((moduleUnitMatrixIso D Sc cutoff M i t hh).inv)

/-- The inverse row extracts its literal source coordinate after the whole
prescribed matrix, without changing or rescaling any entry. -/
theorem moduleUnitCoefficientRow_component (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I))))
    (z : unitMatrixSourceSpace D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) t) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a
      (unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t z) = z a := by
  have h := congrArg (fun f : unitMatrixSourceSpace D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) t ⟶
        unitMatrixSourceSpace D Sc cutoff i M
          (contentUnitCount D cutoff i (t.word : Multiset I)) t => f z)
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom_inv_id
  rw [moduleUnitMatrixIso_hom] at h
  have h' : (moduleUnitMatrixIso D Sc cutoff M i t hh).inv
      (unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t z) = z := by
    simpa only [SVec.comp_apply, SVec.id_apply] using h
  exact congrFun h' a

private theorem assembled_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → SVec k) (W : SVec k) (f : ∀ a, V a ⟶ W) (a : ι) (z : V a) :
    OddMath.FiniteSuperspace.assembleColumns V W f (Pi.single a z) = f a z := by
  change (∑ b, f b ((Pi.single a z : (b : ι) → V b) b)) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    exact map_zero _
  · simp

private theorem unitMatrixComponent_single (i : I) (m : ℕ)
    (t : OldCategory D Sc cutoff) (a : Option (Fin m))
    (z : (unitMatrixFamily D Sc cutoff i M m a).obj t) :
    unitMatrixComponent D Sc cutoff i M m t (Pi.single a z) =
      (unitMatrixEntry D Sc cutoff i M m a).total t z := by
  classical
  exact assembled_single (fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t)
    (mateTargetSpace D Sc cutoff i M t)
    (fun a => (unitMatrixEntry D Sc cutoff i M m a).total t) a z

/-- Each inverse coefficient row is a left inverse to its prescribed
dotted-unit column (or the first mate column). -/
theorem moduleUnitCoefficientRow_entry (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I))))
    (z : (unitMatrixFamily D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a
      ((unitMatrixEntry D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) a).total t z) = z := by
  classical
  have h := moduleUnitCoefficientRow_component D Sc cutoff M i t hh a (Pi.single a z)
  rw [unitMatrixComponent_single] at h
  simpa only [Pi.single_eq_same] using h

/-- Distinct inverse rows kill each prescribed shifted unit/mate column. -/
theorem moduleUnitCoefficientRow_entry_ne (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a b : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I))))
    (hab : a ≠ b)
    (z : (unitMatrixFamily D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) b).obj t) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a
      ((unitMatrixEntry D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) b).total t z) = 0 := by
  classical
  have h := moduleUnitCoefficientRow_component D Sc cutoff M i t hh a (Pi.single b z)
  rw [unitMatrixComponent_single] at h
  simpa only [Pi.single_eq_of_ne hab] using h

/-- The extraction row is even in its prescribed shifted coordinates. -/
theorem moduleUnitCoefficientRow_even (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I)))) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i M t)
      ((unitMatrixFamily D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t) 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q z hz
  rw [add_zero]
  have h := SVec.apply_mem_part
    (moduleUnitMatrixIso_inv_even D Sc cutoff M i t hh) hz
  rw [add_zero] at h
  change (moduleUnitMatrixIso D Sc cutoff M i t hh).inv z ∈
    (OddMath.FiniteSuperspace.product fun a => (unitMatrixFamily D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t).part q at h
  exact (OddMath.FiniteSuperspace.mem_product_part _ q _).mp h a

local instance unitCoefficientRowsPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Removing the selected source shift gives a coefficient functional on
the original module component. The shift is the prescribed r-th-dot shift. -/
def moduleUnitCoefficient (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) :
    mateTargetSpace D Sc cutoff i M t →ₗ[k] M.obj t :=
  (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) t).toLinearMap.comp
      (moduleUnitCoefficientRow D Sc cutoff M i t hh (some r))

private theorem homogeneous_total_mem
    {F G : Superfunctor k (OldCategory D Sc cutoff) (SVec k)}
    {f : F ⟶ G} {p : ZMod 2} (hf : f ∈ parity (R := k) F G p)
    (t : OldCategory D Sc cutoff) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · have h : f.total t = f.app 0 t := by
      rw [SuperNatTrans.total,
        Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
    rw [h]
    exact f.app_mem 0 t
  · have h : f.total t = f.app 1 t := by
      rw [SuperNatTrans.total,
        Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
    rw [h]
    exact f.app_mem 1 t

private theorem homogeneous_total_eq_app
    {F G : Superfunctor k (OldCategory D Sc cutoff) (SVec k)}
    {f : F ⟶ G} {p : ZMod 2} (hf : f ∈ parity (R := k) F G p)
    (t : OldCategory D Sc cutoff) : f.total t = f.app p t := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

/-- In original module coordinates the r-th coefficient functional has
the prescribed parity r*p. In particular the top vacuum row has parity
(N-1)*p; odd coefficients may not be moved through it unsigned. -/
theorem moduleUnitCoefficient_mem (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) :
    moduleUnitCoefficient D Sc cutoff M i t hh r ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i M t) (M.obj t) (r.val • D.parity i) := by
  have he := homogeneous_total_mem D Sc cutoff
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).hom_mem M) t
  change moduleUnitCoefficientRow D Sc cutoff M i t hh (some r) ≫
    (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total t) ∈ _
  simpa only [zero_add] using comp_mem
    (moduleUnitCoefficientRow_even D Sc cutoff M i t hh (some r)) he

/-- The functional extracts the r-th literal ordinary unit/dot column,
after cancelling the canonical homogeneous comparison on its source. -/
theorem moduleUnitCoefficient_column (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (z : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      ((moduleUnitColumn D Sc cutoff i M r.val).total t z) = z := by
  let e := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) t
  let row : mateTargetSpace D Sc cutoff i M t →ₗ[k]
      (((SKM.homParityShift (k := k) (r.val • D.parity i)).obj M).obj t) :=
    moduleUnitCoefficientRow D Sc cutoff M i t hh (some r)
  let col := (moduleUnitColumn D Sc cutoff i M r.val).total t
  have hcolumn : (unitMatrixEntry D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) (some r)).total t (e.symm z) = col z :=
    (unitMatrixEntry_some_total D Sc cutoff i M t _ r (e.symm z)).trans
      (congrArg col (e.apply_symm_apply z))
  have hentry := moduleUnitCoefficientRow_entry D Sc cutoff M i t hh (some r) (e.symm z)
  have hrow : row (col z) = e.symm z :=
    (congrArg row hcolumn).symm.trans hentry
  change e (row (col z)) = z
  exact (congrArg e hrow).trans (e.apply_symm_apply z)

/-- Every other low dotted-unit column is killed in the original module
coordinates. Together with the preceding equality this supplies the full
coefficient-extraction window, rather than assuming it. -/
theorem moduleUnitCoefficient_column_ne (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r s : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (hrs : r ≠ s)
    (z : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      ((moduleUnitColumn D Sc cutoff i M s.val).total t z) = 0 := by
  let e := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (s.val • D.parity i)).iso M) t
  let er := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) t
  let row : mateTargetSpace D Sc cutoff i M t →ₗ[k]
      (((SKM.homParityShift (k := k) (r.val • D.parity i)).obj M).obj t) :=
    moduleUnitCoefficientRow D Sc cutoff M i t hh (some r)
  let col := (moduleUnitColumn D Sc cutoff i M s.val).total t
  have hcolumn : (unitMatrixEntry D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) (some s)).total t (e.symm z) = col z :=
    (unitMatrixEntry_some_total D Sc cutoff i M t _ s (e.symm z)).trans
      (congrArg col (e.apply_symm_apply z))
  have hentry := moduleUnitCoefficientRow_entry_ne D Sc cutoff M i t hh (some r) (some s)
    (by simpa only [ne_eq, Option.some.injEq] using hrs) (e.symm z)
  have hrow : row (col z) = 0 := (congrArg row hcolumn).symm.trans hentry
  change er (row (col z)) = 0
  exact (congrArg er hrow).trans (map_zero er)

/-- The coefficient-extraction window on the chosen signed induction dot
and ordinary adjunction unit, with no unit-column abstraction remaining. -/
theorem moduleUnitCoefficient_dot_window (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (t.word : Multiset I)) (z : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      (((inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ a)
        ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t) z)) =
      if a = r.val then z else 0 := by
  have hcol := LinearMap.congr_fun (moduleUnitColumn_total D Sc cutoff i M t a) z
  change (moduleUnitColumn D Sc cutoff i M a).total t z =
    (((inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ a)
      ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t) z)) at hcol
  rw [← hcol]
  by_cases h : a = r.val
  · rw [ite_eq_left h, h]
    exact moduleUnitCoefficient_column D Sc cutoff M i t hh r z
  · rw [ite_eq_right h]
    exact moduleUnitCoefficient_column_ne D Sc cutoff M i t hh r ⟨a, ha⟩
      (by intro e; exact h (congrArg Fin.val e).symm) z

/-- Homogeneous endomorphisms of the output object satisfy the exact
supernatural coefficient rule. At the vacuum this is the full
exterior-coefficient superlinearity of the extraction functional. -/
theorem moduleUnitCoefficient_end_naturality (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    {q : ZMod 2} (f : t ⟶ t) (hf : f ∈ parity (R := k) t t q) :
    (moduleUnitCoefficient D Sc cutoff M i t hh r).comp
        (SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
          ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).map f)) =
      koszulSign (r.val • D.parity i) q •
        ((SVec.toLinearMap (M.map f)).comp
          (moduleUnitCoefficient D Sc cutoff M i t hh r)) := by
  let m := contentUnitCount D cutoff i (t.word : Multiset I)
  let S := unitMatrixSourceModule D Sc cutoff M i m
  let T := (BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)
  let e := moduleUnitMatrixIso D Sc cutoff M i t hh
  let es := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  let pr : S.obj t ⟶ (unitMatrixFamily D Sc cutoff i M m (some r)).obj t := LinearMap.proj (some r)
  have hn : S.map f ≫ e.hom = e.hom ≫ T.map f := by
    dsimp only [e]
    rw [moduleUnitMatrixIso_hom]
    exact (unitMatrixNatTrans D Sc cutoff M i m).naturality f
  have hi : T.map f ≫ e.inv = e.inv ≫ S.map f := by
    have h := congrArg (fun g => e.inv ≫ g ≫ e.inv) hn
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using h.symm
  have hp : S.map f ≫ pr = pr ≫ (unitMatrixFamily D Sc cutoff i M m (some r)).map f := by
    apply LinearMap.ext
    intro z
    rfl
  have hs : (unitMatrixFamily D Sc cutoff i M m (some r)).map f ≫ es.hom.total t =
      koszulSign (r.val • D.parity i) q • (es.hom.total t ≫ M.map f) := by
    have hmem := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).hom_mem M
    rw [homogeneous_total_eq_app D Sc cutoff hmem t]
    exact es.hom.naturality (r.val • D.parity i) f hf
  change T.map f ≫ e.inv ≫ pr ≫ es.hom.total t =
    koszulSign (r.val • D.parity i) q • (e.inv ≫ pr ≫ es.hom.total t ≫ M.map f)
  rw [← Category.assoc (T.map f) e.inv, hi, Category.assoc,
    ← Category.assoc (S.map f) pr, hp, Category.assoc, hs]
  simp only [Preadditive.comp_zsmul]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates

namespace OddMath.QuiverHecke.ELVOld.VacuumCoefficient
open CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The old empty-word representable retains the full coefficient algebra. -/
def coefficientModule : Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  oldRepresentable D Sc cutoff (⟨[]⟩ : OldCategory D Sc cutoff)

@[simp] theorem count (i : I) :
    contentUnitCount D cutoff i (([] : List I) : Multiset I) = cutoff i := by
  simp [contentUnitCount, contentCrossingHeight]

private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cutoff i) :
    Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
  ⟨cutoff i - 1, by rw [count]; omega⟩

/-- The normalized top coefficient functional on the actual old induction
of the empty-word representable, in its original module coordinates. -/
def functional (i : I) (hN : 0 < cutoff i) :
    mateTargetSpace D Sc cutoff i (coefficientModule D Sc cutoff)
      (⟨[]⟩ : OldCategory D Sc cutoff) →ₗ[k]
        (coefficientModule D Sc cutoff).obj (⟨[]⟩ : OldCategory D Sc cutoff) :=
  moduleUnitCoefficient D Sc cutoff (coefficientModule D Sc cutoff) i ⟨[]⟩
    (height D cutoff i) (topSlot D cutoff i hN)

theorem functional_mem (i : I) (hN : 0 < cutoff i) :
    functional D Sc cutoff i hN ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i (coefficientModule D Sc cutoff) ⟨[]⟩)
      ((coefficientModule D Sc cutoff).obj ⟨[]⟩) ((cutoff i - 1) • D.parity i) :=
  moduleUnitCoefficient_mem D Sc cutoff (coefficientModule D Sc cutoff) i ⟨[]⟩
    (height D cutoff i) (topSlot D cutoff i hN)

/-- The literal signed-dot/ordinary-unit extraction window required by
the inverse-cap polynomial calculation. All its inputs are constructed. -/
theorem functional_dot_window (i : I) (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i)
    (z : (coefficientModule D Sc cutoff).obj (⟨[]⟩ : OldCategory D Sc cutoff)) :
    functional D Sc cutoff i hN
      (((inductionDot D Sc cutoff i (coefficientModule D Sc cutoff)
          ((append D Sc cutoff i).obj ⟨[]⟩)) ^ a)
        ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
          (coefficientModule D Sc cutoff)).total ⟨[]⟩) z)) =
      if a + 1 = cutoff i then z else 0 := by
  have he : (a = cutoff i - 1) ↔ a + 1 = cutoff i := by omega
  have h := moduleUnitCoefficient_dot_window D Sc cutoff (coefficientModule D Sc cutoff) i
    ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN) a (by simpa only [count] using ha) z
  simpa only [functional, topSlot, he] using h

end OddMath.QuiverHecke.ELVOld.VacuumCoefficient
