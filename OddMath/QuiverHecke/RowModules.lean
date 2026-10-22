/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GradedModules

/-!
# The projective modules `1_j · Mat obj` and the Yoneda bijection

Brundan–Ellis, arXiv:1701.04133v2, §11: the projective `H_n`-supermodules attached to words.
For an index `j`, the row module `1_j · Mat obj` (`rowModule j`) is the module of finite-support
rows `(f_l : obj l ⟶ obj j)_l` with `Mat obj` acting by matrix multiplication on the right. Its
generator `1_j` has degree and parity zero, and morphisms out of it are determined by the image of
`1_j` (`rowHomEquiv`): for every module `M`,
`Hom(Q^m Π^a (1_j · Mat obj), M) ≅ {x ∈ M of degree m and parity a | x · 1_j = x}`.
Consequently `1_j · Mat obj` is projective (`isProjective_rowModule`), and morphisms between
shifted row modules are the homogeneous morphisms of the underlying category
(`rowModuleHomEquiv`): `Hom(Q^m Π^a (1_j A), Q^n Π^b (1_i A))` is the space of morphisms
`obj j ⟶ obj i` of degree `m - n` and parity `a - b`.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams

namespace OddMath.FiniteHomMatrix

universe u v w t z

/-! ## Entrywise gradings of finitely supported families -/

section DFinsuppGrading

variable {k : Type u} [CommRing k] {ι : Type t} {Γ : Type z} {β : ι → Type w}
  [∀ x, AddCommGroup (β x)] [∀ x, Module k (β x)]

/-- Families whose entries lie in the given homogeneous submodules. -/
def entrywise (G : (x : ι) → Γ → Submodule k (β x)) (d : Γ) : Submodule k (Π₀ x, β x) where
  carrier := {v | ∀ x, v x ∈ G x d}
  zero_mem' := fun x => (G x d).zero_mem
  add_mem' ha hb x := (G x d).add_mem (ha x) (hb x)
  smul_mem' r _ ha x := (G x d).smul_mem r (ha x)

@[simp] theorem mem_entrywise (G : (x : ι) → Γ → Submodule k (β x)) (d : Γ) (v : Π₀ x, β x) :
    v ∈ entrywise G d ↔ ∀ x, v x ∈ G x d := Iff.rfl

theorem single_mem_entrywise {G : (x : ι) → Γ → Submodule k (β x)} {d : Γ} (x : ι) {f : β x}
    (hf : f ∈ G x d) : DFinsupp.single x f ∈ entrywise G d := by
  intro y
  by_cases h : y = x
  · subst y; simpa using hf
  · simp [DFinsupp.single_eq_of_ne h]

/-- Entrywise direct-sum gradings are internal on finitely supported families. -/
theorem isInternal_entrywise [DecidableEq Γ] (G : (x : ι) → Γ → Submodule k (β x))
    (hG : ∀ x, DirectSum.IsInternal (G x)) : DirectSum.IsInternal (entrywise G) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s a ha hz d hd
    ext x
    have h := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (G x)).mp
      (hG x).submodule_iSupIndep s (fun d => a d x) (fun d hd => ha d hd x)
    apply h _ d hd
    simpa using congrArg (fun a : Π₀ x, β x => a x) hz
  · apply top_le_iff.mp
    intro a ha
    clear ha
    induction a using DFinsupp.induction with
    | h0 => exact Submodule.zero_mem _
    | ha x f a _ _ ih =>
      refine Submodule.add_mem _ ?_ ih
      let := (hG x).chooseDecomposition
      apply DirectSum.Decomposition.inductionOn (G x) (motive := fun f =>
        DFinsupp.single x f ∈ ⨆ d, entrywise G d) ?_ ?_ ?_ f
      · simp
      · intro d f
        exact (le_iSup (entrywise G) d) (single_mem_entrywise x f.property)
      · intro f g hf hg
        simpa [DFinsupp.single_add] using (⨆ d, entrywise G d).add_mem hf hg

end DFinsuppGrading

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  {J : Type t} {obj : J → C}

/-! ## Rows -/

/-- Finitely supported rows with entries `obj l ⟶ obj j`. -/
abbrev Row (obj : J → C) (j : J) := Π₀ l : J, (obj l ⟶ obj j)

/-- A row as a matrix supported in row `j`. -/
def rowToMat (j : J) : Row obj j →ₗ[k] Mat obj :=
  DFinsupp.lsum k fun l => DFinsupp.lsingle (M := fun p : J × J => obj p.2 ⟶ obj p.1) (j, l)

@[simp] theorem rowToMat_single (j l : J) (f : obj l ⟶ obj j) :
    rowToMat (k := k) j (DFinsupp.single l f) = single j l f := by
  simp [rowToMat, single]

theorem rowToMat_apply_self (j : J) (v : Row obj j) (l : J) :
    rowToMat (k := k) j v (j, l) = v l := by
  induction v using DFinsupp.induction with
  | h0 => simp
  | ha l' f v _ _ ih =>
    rw [map_add, DFinsupp.add_apply, DFinsupp.add_apply, ih, rowToMat_single]
    by_cases h : l = l'
    · subst l'; simp [single]
    · simp [single, DFinsupp.single_apply, Ne.symm h]

theorem rowToMat_apply_ne (j : J) (v : Row obj j) {i : J} (l : J) (h : i ≠ j) :
    rowToMat (k := k) j v (i, l) = 0 := by
  induction v using DFinsupp.induction with
  | h0 => simp
  | ha l' f v _ _ ih =>
    rw [map_add, DFinsupp.add_apply, ih, rowToMat_single]
    simp [single, DFinsupp.single_apply, Ne.symm h]

/-- Row `j` of a matrix. -/
def matToRow (j : J) : Mat obj →ₗ[k] Row obj j where
  toFun x := DFinsupp.comapDomain (fun l : J => (j, l)) (fun _ _ h => (Prod.ext_iff.mp h).2) x
  map_add' x y := by ext l; simp
  map_smul' r x := by ext l; simp

@[simp] theorem matToRow_apply (j : J) (x : Mat obj) (l : J) :
    matToRow (k := k) j x l = x (j, l) := rfl

theorem matToRow_rowToMat (j : J) (v : Row obj j) :
    matToRow (k := k) j (rowToMat (k := k) j v) = v := by
  induction v using DFinsupp.induction with
  | h0 => simp
  | ha l f v _ _ ih =>
    rw [map_add, map_add, ih, rowToMat_single]
    congr 1
    ext l'
    by_cases h : l' = l
    · subst l'; simp [single]
    · simp [single, DFinsupp.single_apply, Ne.symm h]

theorem rowToMat_matToRow (j : J) (x : Mat obj) :
    rowToMat (k := k) j (matToRow (k := k) j x) = idem j * x := by
  induction x using induction with
  | hz => simp
  | ha a b ha hb => rw [map_add, map_add, ha, hb, mul_add]
  | hs i l f =>
    by_cases h : i = j
    · subst i
      rw [idem_mul_single]
      have : matToRow (k := k) j (single j l f) = DFinsupp.single l f := by
        ext l'
        by_cases h' : l' = l
        · subst l'; simp [single]
        · simp [single, DFinsupp.single_apply, Ne.symm h']
      rw [this, rowToMat_single]
    · rw [idem, single_mul_single_of_ne j j i l (Ne.symm h)]
      have : matToRow (k := k) j (single i l f) = 0 := by
        ext l'
        simp [single, DFinsupp.single_apply, h]
      rw [this, map_zero]

theorem idem_mul_rowToMat (j : J) (v : Row obj j) :
    idem j * rowToMat (k := k) j v = rowToMat (k := k) j v := by
  rw [← rowToMat_matToRow (k := k), matToRow_rowToMat]

theorem rowToMat_injective (j : J) : Function.Injective (rowToMat (k := k) (obj := obj) j) :=
  Function.LeftInverse.injective (matToRow_rowToMat (k := k) j)

/-- The right action of `Mat obj` on rows: `v · a`. -/
def rowAct (j : J) : Mat obj →ₗ[k] Row obj j →ₗ[k] Row obj j :=
  LinearMap.mk₂ k (fun a v => matToRow j (rowToMat j v * a))
    (fun a a' v => by rw [mul_add, map_add])
    (fun r a v => by rw [mul_smul_comm, map_smul])
    (fun a v v' => by rw [map_add, add_mul, map_add])
    (fun r a v => by rw [map_smul, smul_mul_assoc, map_smul])

@[simp] theorem rowAct_apply (j : J) (a : Mat obj) (v : Row obj j) :
    rowAct (k := k) j a v = matToRow (k := k) j (rowToMat (k := k) j v * a) := rfl

/-! ## Row modules -/

variable [Supercategory k C] [GradedSupercategory k C]

/-- The homogeneous pieces of a row. -/
abbrev rowPiece (j : J) : ℤ × ZMod 2 → Submodule k (Row obj j) :=
  entrywise fun l => GradedSupercategory.bidegree (R := k) (obj l) (obj j)

theorem isInternal_rowPiece (j : J) : DirectSum.IsInternal (rowPiece (k := k) (obj := obj) j) :=
  isInternal_entrywise _ fun l => GradedSupercategory.isInternal_bigrading (R := k) (obj l) (obj j)

theorem rowToMat_mem_bidegree {j : J} {d : ℤ × ZMod 2} {v : Row obj j}
    (hv : v ∈ rowPiece (k := k) j d) : rowToMat (k := k) j v ∈ bidegree (k := k) d := by
  rintro ⟨i, l⟩
  by_cases h : i = j
  · subst i; rw [rowToMat_apply_self]; exact hv l
  · rw [rowToMat_apply_ne j v l h]; exact Submodule.zero_mem _

theorem matToRow_mem_rowPiece {j : J} {d : ℤ × ZMod 2} {x : Mat obj}
    (hx : x ∈ bidegree (k := k) d) : matToRow (k := k) j x ∈ rowPiece (k := k) j d :=
  fun l => hx (j, l)

/-- **BE2 §11.** The projective module `1_j · Mat obj`, generated by `1_j` in degree and parity
zero. -/
def rowModule (j : J) : GSMod.{u, v, w, t, max t w} k obj where
  carrier := Row obj j
  piece := rowPiece (k := k) j
  isInternal_piece := isInternal_rowPiece j
  act := rowAct (k := k) j
  act_mul a b v := by
    simp only [rowAct_apply, rowToMat_matToRow, ← mul_assoc, idem_mul_rowToMat]
  exists_localUnit v := by
    obtain ⟨s, hs⟩ := exists_localUnit (rowToMat (k := k) j v)
    exact ⟨s, by rw [rowAct_apply, (hs s le_rfl).2, matToRow_rowToMat]⟩
  act_mem {d e a v} ha hv := by
    rw [rowAct_apply, add_comm]
    exact matToRow_mem_rowPiece (mul_mem_bidegree (rowToMat_mem_bidegree hv) ha)

/-- The generator `1_j` of `1_j · Mat obj`. -/
def rowGen (j : J) : Row obj j := DFinsupp.single j (𝟙 (obj j))

omit [Supercategory k C] [GradedSupercategory k C] in
@[simp] theorem rowToMat_rowGen (j : J) : rowToMat (k := k) j (rowGen (obj := obj) j) = idem j := by
  simp [rowGen, idem]

theorem rowGen_mem (j : J) : rowGen (obj := obj) j ∈ rowPiece (k := k) j 0 :=
  single_mem_entrywise j ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩

omit [Supercategory k C] [GradedSupercategory k C] in
/-- Every row is `1_j` times its own matrix. -/
theorem rowAct_rowGen (j : J) (v : Row obj j) :
    rowAct (k := k) j (rowToMat (k := k) j v) (rowGen j) = v := by
  rw [rowAct_apply, rowToMat_rowGen, idem_mul_rowToMat, matToRow_rowToMat]

omit [Supercategory k C] [GradedSupercategory k C] in
/-- Right multiplication by `1_l` keeps the `l`-th entry of a row. -/
theorem rowAct_idem (j l : J) (v : Row obj j) :
    rowAct (k := k) j (idem l) v = DFinsupp.single l (v l) := by
  induction v using DFinsupp.induction with
  | h0 => simp
  | ha l' f v _ _ ih =>
    rw [map_add, ih, DFinsupp.add_apply, DFinsupp.single_add, rowAct_apply, rowToMat_single]
    congr 1
    by_cases h : l' = l
    · subst l'
      rw [idem, single_mul_single, Category.id_comp]
      ext l''
      by_cases h' : l'' = l
      · subst l''; simp [single]
      · simp [single, DFinsupp.single_apply, Ne.symm h']
    · rw [idem, single_mul_single_of_ne _ _ _ _ h, map_zero]
      simp [h]

namespace GSMod

variable {M : GSMod.{u, v, w, t, max t w} k obj}

/-- The morphism `v ↦ m · v` out of a shifted row module; it sends `1_j` to `m · 1_j`. -/
def rowHom (s : ℤ × ZMod 2) (j : J) (m : M) (hm : m ∈ M.piece s) :
    GSMod.shift s (rowModule (k := k) j) ⟶ M where
  toLinearMap := M.act.flip m ∘ₗ rowToMat (k := k) j
  map_act a v := by
    change M.act (rowToMat j (rowAct j a v)) m = M.act a (M.act (rowToMat j v) m)
    rw [rowAct_apply, rowToMat_matToRow, ← M.act_mul, ← matrix_mul_assoc, idem_mul_rowToMat]
  map_piece d v hv := by
    change M.act (rowToMat j v) m ∈ M.piece d
    have := M.act_mem (rowToMat_mem_bidegree (k := k) (d := d - s) hv) hm
    rwa [sub_add_cancel] at this

@[simp] theorem rowHom_apply (s : ℤ × ZMod 2) (j : J) (m : M) (hm : m ∈ M.piece s)
    (v : Row obj j) :
    (rowHom s j m hm).toLinearMap v = M.act (rowToMat (k := k) j v) m := rfl

/-- **Yoneda for row modules.** Morphisms `Q^m Π^a (1_j · Mat obj) ⟶ M` are the vectors of `M`
of degree `m` and parity `a` fixed by `1_j`, through the image of the generator `1_j`. -/
def rowHomEquiv (s : ℤ × ZMod 2) (j : J) :
    (GSMod.shift s (rowModule (k := k) j) ⟶ M) ≃
      {m : M // m ∈ M.piece s ∧ M.act (idem j) m = m} where
  toFun φ := ⟨φ.toLinearMap (rowGen j), φ.map_piece s _ (by
      change rowGen j ∈ rowPiece (k := k) j (s - s); rw [sub_self]; exact rowGen_mem j),
    by
      rw [← φ.map_act]
      change φ.toLinearMap (rowAct j (idem j) (rowGen j)) = _
      rw [← rowToMat_rowGen (k := k), rowAct_rowGen]⟩
  invFun m := rowHom s j m.1 m.2.1
  left_inv φ := by
    ext v
    change M.act (rowToMat j v) (φ.toLinearMap (rowGen j)) = φ.toLinearMap v
    rw [← φ.map_act]
    change φ.toLinearMap (rowAct j (rowToMat j v) (rowGen j)) = _
    rw [rowAct_rowGen]
  right_inv m := by
    ext
    change M.act (rowToMat j (rowGen j)) m.1 = m.1
    rw [rowToMat_rowGen, m.2.2]

@[simp] theorem rowHomEquiv_apply (s : ℤ × ZMod 2) (j : J)
    (φ : GSMod.shift s (rowModule (k := k) j) ⟶ M) :
    (rowHomEquiv s j φ : M) = φ.toLinearMap (rowGen j) := rfl

/-- Two morphisms out of a shifted row module agree if they agree on the generator `1_j`. -/
theorem rowHom_ext {s : ℤ × ZMod 2} {j : J} {φ ψ : GSMod.shift s (rowModule (k := k) j) ⟶ M}
    (h : φ.toLinearMap (rowGen j) = ψ.toLinearMap (rowGen j)) : φ = ψ :=
  (rowHomEquiv s j).injective (Subtype.ext h)

/-- **BE2 §11.** The shifted row modules `Q^m Π^a (1_j · Mat obj)` are projective. -/
theorem isProjective_rowModule (s : ℤ × ZMod 2) (j : J) :
    IsProjective (GSMod.shift s (rowModule (k := k) (obj := obj) j)) := by
  intro E X e he f
  have hidem : idem (obj := obj) j ∈ bidegree (k := k) 0 := idem_mem_bidegree j
  let x := f.toLinearMap (rowGen j)
  have hx : x ∈ X.piece s ∧ X.act (idem j) x = x := (rowHomEquiv s j f).2
  obtain ⟨y, hy⟩ := he x
  let y' := E.proj s (E.act (idem j) y)
  have hy'u : E.act (idem j) y' = y' := by
    simp only [y']
    rw [E.act_proj hidem, ← E.act_mul, idem_sq]
  have hey' : e.toLinearMap y' = x := by
    simp only [y']
    rw [proj_map e.toLinearMap e.map_piece, e.map_act, hy, hx.2]
    exact X.proj_of_mem_same hx.1
  refine ⟨rowHom s j y' (E.proj_mem s _), rowHom_ext ?_⟩
  change e.toLinearMap (E.act (rowToMat j (rowGen j)) y') = x
  rw [rowToMat_rowGen, hy'u, hey']

end GSMod

/-- Rows fixed by `1_j` in a given degree are the homogeneous morphisms `obj j ⟶ obj i`. -/
def fixedRowEquiv (i j : J) (d : ℤ × ZMod 2) :
    {v : Row obj i // v ∈ rowPiece (k := k) i d ∧ rowAct (k := k) i (idem j) v = v} ≃
      GradedSupercategory.bidegree (R := k) (obj j) (obj i) d where
  toFun v := ⟨v.1 j, v.2.1 j⟩
  invFun f := ⟨DFinsupp.single j f.1, single_mem_entrywise j f.2, by
    rw [rowAct_idem]; simp⟩
  left_inv v := by
    ext l
    have := congrArg (fun w : Row obj i => w l) v.2.2
    simp only [rowAct_idem] at this
    simpa using this
  right_inv f := by simp

namespace GSMod

/-- **BE2 §11.** Morphisms `Q^m Π^a (1_j · Mat obj) ⟶ Q^n Π^b (1_i · Mat obj)` are the
morphisms `obj j ⟶ obj i` of degree `m - n` and parity `a - b`, through the image of `1_j`. -/
def rowModuleHomEquiv (s t : ℤ × ZMod 2) (i j : J) :
    (GSMod.shift s (rowModule (k := k) (obj := obj) j) ⟶ GSMod.shift t (rowModule (k := k) i)) ≃
      GradedSupercategory.bidegree (R := k) (obj j) (obj i) (s - t) :=
  (rowHomEquiv s j).trans (fixedRowEquiv i j (s - t))

theorem rowModuleHomEquiv_apply (s t : ℤ × ZMod 2) (i j : J)
    (φ : GSMod.shift s (rowModule (k := k) (obj := obj) j) ⟶
      GSMod.shift t (rowModule (k := k) i)) :
    (rowModuleHomEquiv s t i j φ : obj j ⟶ obj i) =
      (show Row obj i from φ.toLinearMap (rowGen j)) j := rfl

end GSMod

end OddMath.FiniteHomMatrix
