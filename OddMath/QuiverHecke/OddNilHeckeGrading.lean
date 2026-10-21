import OddMath.QuiverHecke.OddNilHecke
import OddMath.Frontier.EQOnhDGCompare

/-!
# Homogeneity of the odd same-colour map

BE2, arXiv:1701.04133v2, Lemma 11.1: transporting the intrinsic
odd nilHecke grading to the independent quiver Hecke category.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open OddMath.Frontier NilHeckeAction
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

private theorem oddFunctor_mem_degree {A : Type*} [AddCommMonoid A]
    (i : I) (hi : D.parity i = 1) (deg : (sig D).Gen → A)
    {a b : Obj Diagrams.OddNilHecke.sig}
    {f : (Diagrams.OddNilHecke.pres k).obj a ⟶ (Diagrams.OddNilHecke.pres k).obj b}
    {d : A}
    (hf : f ∈ (Diagrams.OddNilHecke.pres k).homDeg
      (fun g => deg ((oddColour D i).gen g)) a b d) :
    (oddFunctor D Sc i hi).map f ∈ (pres D Sc).homDeg deg
      ((oddColour D i).obj a) ((oddColour D i).obj b) d :=
  LayerMap.lift_mem_homDeg (oddColour D i).whiskerData (fun _ => trivial)
    (fun _ => oddColour_rel D Sc i hi)
    (fun _ _ hx => (oddColour D i).toPresented_interchange (pres D Sc)
      (fun _ => 1) (oddColour_odd D i hi) hx) () (fun _ => rfl) hf

private theorem oddCorner_mem_degree {A : Type*} [AddCommMonoid A]
    (i : I) (hi : D.parity i = 1) (r : ℕ) (deg : (sig D).Gen → A)
    {f : End ((Diagrams.OddNilHecke.pres k).obj (Diagrams.OddNilHecke.strands r))}
    {d : A}
    (hf : f ∈ (Diagrams.OddNilHecke.pres k).homDeg
      (fun g => deg ((oddColour D i).gen g)) _ _ d) :
    oddCorner D Sc i hi r f ∈ (pres D Sc).homDeg deg
      (ob D (List.replicate r i)) (ob D (List.replicate r i)) d := by
  dsimp only [oddCorner, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  simpa only [zero_add, add_zero, Category.assoc] using
    Presentation.comp_mem_homDeg
      (Presentation.comp_mem_homDeg (Presentation.eqToHom_mem_homDeg deg _)
        (oddFunctor_mem_degree D Sc i hi deg hf))
      (Presentation.eqToHom_mem_homDeg deg _)

private theorem toDiagramsOver_word_degree {A : Type*} [AddCommGroup A]
    (δ : A) (deg : Diagrams.OddNilHecke.Gen → A)
    (hd : deg .dot = δ) (hc : deg .cross = -δ) {n : ℕ}
    (w : List (Sum (Fin (n + 2)) (Fin (n + 1)))) :
    Diagrams.OddNilHecke.toDiagramsOver k n (NilHeckeGrading.wordValue w) ∈
      (Diagrams.OddNilHecke.pres k).homDeg deg _ _
        (EQOnhDG.halfWordDegree w • δ) := by
  induction w with
  | nil =>
    simpa [NilHeckeGrading.wordValue, EQOnhDG.halfWordDegree] using
      (Diagrams.OddNilHecke.pres k).id_mem_homDeg deg (Diagrams.OddNilHecke.strands (n + 2))
  | cons g w ih =>
    simp only [NilHeckeGrading.wordValue, List.map_cons, List.prod_cons, map_mul]
    have hg : Diagrams.OddNilHecke.toDiagramsOver k n
        (Sum.elim (dot n) (crossing n) g) ∈
        (Diagrams.OddNilHecke.pres k).homDeg deg _ _
          (EQOnhDG.halfWordDegree [g] • δ) := by
      cases g with
      | inl j =>
        rw [Sum.elim_inl, Diagrams.OddNilHecke.toDiagramsOver_dot,
          Diagrams.OddNilHecke.x_def k j.isLt]
        apply Presentation.diag_mem_homDeg'
        simp [Diagram.degree, Diagrams.OddNilHecke.layers_dlay,
          Diagrams.OddNilHecke.lay, EQOnhDG.halfWordDegree, EQOnhDG.halfLetterDegree, hd]
      | inr j =>
        rw [Sum.elim_inr, Diagrams.OddNilHecke.toDiagramsOver_crossing,
          Diagrams.OddNilHecke.ψ_def k (by omega)]
        apply Presentation.diag_mem_homDeg'
        simp [Diagram.degree, Diagrams.OddNilHecke.layers_dlay,
          Diagrams.OddNilHecke.lay, EQOnhDG.halfWordDegree, EQOnhDG.halfLetterDegree, hc]
    have h := Presentation.comp_mem_homDeg ih hg
    simpa [NilHeckeGrading.wordValue, NilHeckeGrading.letterValue,
      EQOnhDG.halfWordDegree, add_zsmul, add_comm] using h

/-- The same-colour map scales the intrinsic half-degree by the chosen dot degree.
The statement works for both the integer and the independent parity grading. -/
theorem oddNilHecke_mem_degree {A : Type*} [AddCommGroup A]
    (i : I) (hi : D.parity i = 1) (deg : (sig D).Gen → A) (δ : A)
    (hd : deg (.dot i) = δ) (hc : deg (.cross i i) = -δ)
    {n : ℕ} {d : ℤ} {x : Presented n} (hx : x ∈ EQOnhDG.grading n d) :
    oddNilHecke D Sc i hi n x ∈ (pres D Sc).homDeg deg
      (ob D (List.replicate (n + 2) i)) (ob D (List.replicate (n + 2) i)) (d • δ) := by
  apply oddCorner_mem_degree D Sc i hi (n + 2) deg
  have hx' := EQOnhDG.grading_le_degreePiece d hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hw : NilHeckeGrading.wordDegree w = 2 * d := hw
    rw [EQOnhDG.wordDegree_eq_two_mul] at hw
    have he : EQOnhDG.halfWordDegree w = d := by omega
    exact he ▸ toDiagramsOver_word_degree (k := k) δ
      (fun g => deg ((oddColour D i).gen g)) hd hc w
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [map_zsmul]
    exact ((Diagrams.OddNilHecke.pres k).homDeg
      (fun g => deg ((oddColour D i).gen g)) _ _ (d • δ)).toAddSubgroup.zsmul_mem hy r

/-- Integer degree scales by twice the symmetrizer, with no bar-consistency premise. -/
theorem oddNilHecke_mem_integerDegree (sy : SKM.Symmetrizer D)
    (i : I) (hi : D.parity i = 1) {n : ℕ} {d : ℤ} {x : Presented n}
    (hx : x ∈ EQOnhDG.grading n d) :
    oddNilHecke D Sc i hi n x ∈ homDegree D sy Sc
      (List.replicate (n + 2) i) (List.replicate (n + 2) i) (2 * sy.d i * d) := by
  have h := oddNilHecke_mem_degree D Sc i hi (gdeg D sy) (2 * sy.d i)
    rfl (by simp [gdeg, D.d_self, mul_comm]) hx
  simpa [homDegree, zsmul_eq_mul, mul_comm] using h

/-- Parity is transported independently of the symmetrizer. -/
theorem oddNilHecke_mem_parity (i : I) (hi : D.parity i = 1)
    {n : ℕ} {d : ℤ} {x : Presented n} (hx : x ∈ EQOnhDG.grading n d) :
    oddNilHecke D Sc i hi n x ∈ (pres D Sc).homDeg
      (Presentation.parityDeg (sig D)) (ob D (List.replicate (n + 2) i))
      (ob D (List.replicate (n + 2) i)) (d : ZMod 2) := by
  have h := oddNilHecke_mem_degree D Sc i hi (Presentation.parityDeg (sig D))
    (1 : ZMod 2) (by simp [Presentation.parityDeg, sig, Shape.parity, hi])
    (by
      change (if decide (D.parity i * D.parity i = 1) then (1 : ZMod 2) else 0) = -1
      rw [hi]
      decide) hx
  simpa using h

#print axioms oddNilHecke_mem_integerDegree
#print axioms oddNilHecke_mem_parity

end OddMath.QuiverHecke
