/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.PreF.Restrict
import OddMath.CoveringQuantum.SerreForm

/-!
# Restriction of a super Cartan datum to a subset of the index set

For an injective map `e : J → I`, a super Cartan datum on `I` restricts to one on `J`
(`SuperCartanDatum.comap`, with matrix `a ∘ (e × e)`). The bicharacter and the normalization of
the restriction are those of the datum on the image, the inclusion `'f_J → 'f_I` carries Serre
elements to Serre elements, and it induces an algebra map of the Serre presentations.

Since every element of `'f_I` involves finitely many generators, the identification of the Serre
ideal with the radical of the form ([BE2] §10, [CHW1] Prop. 3.4.1) for all finite restrictions
implies it for the datum itself (`SuperCartanDatum.serreIdeal_eq_radical_of_finset`).

## Main definitions

* `SuperCartanDatum.comap C e he`: the restriction of `C` along an injective `e : J → I`.
* `SuperCartanDatum.serreRestrict`: the induced map of Serre presentations.

## Main results

* `SuperCartanDatum.incl_serreElt`: the inclusion maps Serre elements to Serre elements.
* `SuperCartanDatum.serreIdeal_eq_radical_of_finset`: reduction to finite index sets.
-/

noncomputable section

namespace OddMath.CoveringQuantum.SuperCartanDatum

open PreF

variable {I J : Type*} (C : SuperCartanDatum I) (e : J → I) (he : Function.Injective e)

/-- The restriction of a super Cartan datum along an injective map of index sets. -/
def comap : SuperCartanDatum J where
  a := C.a.submatrix e e
  isGCM :=
    { diag := fun i ↦ C.isGCM.diag (e i)
      offDiag_nonpos := fun i j hij ↦ C.isGCM.offDiag_nonpos (e i) (e j) (he.ne hij)
      zero_comm := fun i j ↦ C.isGCM.zero_comm (e i) (e j) }
  d := C.d ∘ e
  d_pos := fun i ↦ C.d_pos (e i)
  d_mul_symm := fun i j ↦ C.d_mul_symm (e i) (e j)
  parity := C.parity ∘ e
  even_of_odd := fun i j h ↦ C.even_of_odd (e i) (e j) h

@[simp] theorem comap_a (i j : J) : (C.comap e he).a i j = C.a (e i) (e j) := rfl

@[simp] theorem comap_d (i : J) : (C.comap e he).d i = C.d (e i) := rfl

@[simp] theorem comap_parity (i : J) : (C.comap e he).parity i = C.parity (e i) := rfl

/-- Bar-consistency ([BE2] (10.2)) passes to restrictions. -/
theorem BarConsistent.comap {C : SuperCartanDatum I} (hC : C.BarConsistent) :
    (C.comap e he).BarConsistent := fun i ↦ hC (e i)

variable {k : Type*} [CommRing k] (q : kˣ) (π : k)

theorem comap_chi (i j : J) : (C.comap e he).chi q π i j = C.chi q π (e i) (e j) := rfl

theorem comap_norm (i : J) : (C.comap e he).norm q π i = C.norm q π (e i) := rfl

/-- The inclusion `'f_J → 'f_I` maps Serre elements to Serre elements. -/
theorem incl_serreElt (i j : J) :
    incl k e ((C.comap e he).serreElt q π i j) = C.serreElt q π (e i) (e j) := by
  simp only [serreElt, map_sum, map_smul, map_mul, map_pow, incl_θ]
  rfl

/-- The map of Serre presentations induced by the inclusion `'f_J → 'f_I`. -/
def serreRestrict : (C.comap e he).serreF q π →ₐ[k] C.serreF q π :=
  RingQuot.liftAlgHom k ⟨(C.toSerreF q π).comp (incl k e), by
    rintro _ _ ⟨i, j, hij⟩
    simp only [AlgHom.comp_apply, incl_serreElt, map_zero]
    exact C.toSerreF_serreElt q π (he.ne hij)⟩

theorem serreRestrict_toSerreF (x : PreF k J) :
    C.serreRestrict e he q π ((C.comap e he).toSerreF q π x) = C.toSerreF q π (incl k e x) := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

variable [DecidableEq I]

/-- The identification of the Serre ideal with the radical of the form reduces to finite index
sets: if it holds for the restriction of `C` to every finite set of indices, it holds for `C`. -/
theorem serreIdeal_eq_radical_of_finset (hπ : π ^ 2 = 1)
    (h : ∀ s : Finset I,
      (C.comap ((↑) : s → I) Subtype.val_injective).serreIdeal q π =
        PreF.radical ((C.comap ((↑) : s → I) Subtype.val_injective).chi q π)
          ((C.comap ((↑) : s → I) Subtype.val_injective).norm q π)) :
    C.serreIdeal q π = PreF.radical (C.chi q π) (C.norm q π) := by
  refine le_antisymm (C.serreIdeal_le_radical q π hπ) fun x hx ↦ ?_
  obtain ⟨s, y, rfl⟩ := exists_finset_mem_range_incl (k := k) x
  have hy := mem_radical_of_incl_mem (C.chi q π)
    ((C.comap ((↑) : s → I) Subtype.val_injective).chi q π) _ (fun _ _ ↦ rfl)
    (C.norm q π) ((C.comap ((↑) : s → I) Subtype.val_injective).norm q π) (fun _ ↦ rfl)
    Subtype.val_injective hx
  rw [← h s, mem_serreIdeal] at hy
  rw [mem_serreIdeal]
  change C.toSerreF q π (incl k _ y) = 0
  rw [← serreRestrict_toSerreF, hy, map_zero]

end OddMath.CoveringQuantum.SuperCartanDatum
