import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor

/-! # Balanced tensors of many-object kernels

The kernel-tensor step in DeformedMatrixComparison, section 4: an isomorphism
of ordinary-right coefficient kernels remains an isomorphism after tensoring
with any module. The quotient is constructed explicitly over the ground ring.
No colimit in the category of supernatural module maps is assumed. Parity
shifts belong to the coefficient kernels; compatibility with their gradings
and identification of a particular action kernel are separate statements.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams TensorProduct
open scoped DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
variable (K : Cᵒᵖ ⥤ ModuleCat k) (M : C ⥤ SVec k)

abbrev Raw := ⨁ v : C, (K.obj (op v)) ⊗[k] M.obj v

def rawTensor (v : C) (x : K.obj (op v)) (m : M.obj v) : Raw K M :=
  DirectSum.lof k C (fun v => (K.obj (op v)) ⊗[k] M.obj v) v (x ⊗ₜ[k] m)

/-- All source arrows occur in the balance, including inhomogeneous arrows. -/
def relations : Submodule k (Raw K M) :=
  Submodule.span k {z | ∃ (v w : C) (a : v ⟶ w)
    (x : K.obj (op w)) (m : M.obj v),
    z = rawTensor K M v (K.map a.op x) m - rawTensor K M w x (M.map a m)}

abbrev Obj := Raw K M ⧸ relations K M

def inclusion (v : C) : (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] Obj K M :=
  (relations K M).mkQ ∘ₗ DirectSum.lof k C
    (fun v => (K.obj (op v)) ⊗[k] M.obj v) v

def tensor (v : C) (x : K.obj (op v)) (m : M.obj v) : Obj K M :=
  inclusion K M v (x ⊗ₜ[k] m)

theorem balance {v w : C} (a : v ⟶ w) (x : K.obj (op w)) (m : M.obj v) :
    tensor K M v (K.map a.op x) m = tensor K M w x (M.map a m) := by
  apply sub_eq_zero.mp
  change (relations K M).mkQ (rawTensor K M v (K.map a.op x) m) -
    (relations K M).mkQ (rawTensor K M w x (M.map a m)) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨v, w, a, x, m, rfl⟩)

variable {V : Type u} [AddCommGroup V] [Module k V]

def lift (q : ∀ v : C, (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] V)
    (hq : ∀ (v w : C) (a : v ⟶ w) (x : K.obj (op w)) (m : M.obj v),
      q v ((K.map a.op x) ⊗ₜ[k] m) = q w (x ⊗ₜ[k] M.map a m)) :
    Obj K M →ₗ[k] V :=
  (relations K M).liftQ (DirectSum.toModule k C V q) (by
    apply Submodule.span_le.mpr
    rintro z ⟨v, w, a, x, m, rfl⟩
    simp only [map_sub, rawTensor, DirectSum.toModule_lof]
    exact sub_eq_zero.mpr (hq v w a x m))

@[simp] theorem lift_tensor
    (q : ∀ v : C, (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] V) (hq)
    (v : C) (x : K.obj (op v)) (m : M.obj v) :
    lift K M q hq (tensor K M v x m) = q v (x ⊗ₜ[k] m) := by
  simp [lift, tensor, inclusion]

@[ext] theorem hom_ext {a b : Obj K M →ₗ[k] V}
    (h : ∀ (v : C) (x : K.obj (op v)) (m : M.obj v),
      a (tensor K M v x m) = b (tensor K M v x m)) : a = b := by
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations K M)) |>.mp
  apply DirectSum.linearMap_ext
  intro v
  apply TensorProduct.ext
  ext x m
  exact h v x m

variable {K} {L P : Cᵒᵖ ⥤ ModuleCat k}

/-- A natural coefficient-kernel map descends through the literal balance. -/
def map (e : K ⟶ L) : Obj K M →ₗ[k] Obj L M :=
  lift K M (fun v => inclusion L M v ∘ₗ
    TensorProduct.map (e.app (op v)).hom LinearMap.id) (by
    intro v w a x m
    have he := congrArg (fun f : K.obj (op w) ⟶ L.obj (op v) => f x)
      (e.naturality a.op)
    change e.app (op v) (K.map a.op x) = L.map a.op (e.app (op w) x) at he
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [he]
    exact balance L M a (e.app (op w) x) m)

@[simp] theorem map_tensor (e : K ⟶ L) (v : C)
    (x : K.obj (op v)) (m : M.obj v) :
    map M e (tensor K M v x m) = tensor L M v (e.app (op v) x) m := by
  rw [map, lift_tensor]
  rfl

@[simp] theorem map_id : map M (𝟙 K) = LinearMap.id := by
  apply hom_ext
  intro v x m
  rw [map_tensor]
  rfl

theorem map_comp (e : K ⟶ L) (f : L ⟶ P) :
    map M (e ≫ f) = map M f ∘ₗ map M e := by
  apply hom_ext
  intro v x m
  simp only [map_tensor, LinearMap.comp_apply]
  rfl

/-- Tensoring a coefficient-kernel natural isomorphism with any module.
This is a quotient-level theorem, with no flatness or projectivity hypothesis. -/
def equiv (e : K ≅ L) : Obj K M ≃ₗ[k] Obj L M :=
  LinearEquiv.ofLinearMap (map M e.hom) (map M e.inv)
    (by rw [← map_comp, e.inv_hom_id, map_id])
    (by rw [← map_comp, e.hom_inv_id, map_id])

@[simp] theorem equiv_tensor (e : K ≅ L) (v : C)
    (x : K.obj (op v)) (m : M.obj v) :
    equiv M e (tensor K M v x m) = tensor L M v (e.hom.app (op v) x) m :=
  map_tensor M e.hom v x m

/-- Bijectivity of the forward components supplies inverse naturality.
No chosen component inverse is assumed natural as an additional hypothesis. -/
def coefficientIso (e : K ⟶ L) (he : ∀ v, Function.Bijective (e.app v)) : K ≅ L :=
  NatIso.ofComponents
    (fun v => (LinearEquiv.ofBijective (e.app v).hom (he v)).toModuleIso)
    (by
      intro v w a
      change K.map a ≫ e.app w = e.app v ≫ L.map a
      exact e.naturality a)

/-- Componentwise bijective natural kernel maps induce quotient equivalences. -/
def equivOfBijective (e : K ⟶ L) (he : ∀ v, Function.Bijective (e.app v)) :
    Obj K M ≃ₗ[k] Obj L M :=
  equiv M (coefficientIso e he)

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
