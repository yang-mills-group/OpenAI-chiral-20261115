import ExactRunning.Finite.Shift

/-!
# Reindexing cuts
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

namespace ModeCut
variable {δ γ : Type} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
variable {P : ModeCut α} {Q : ModeCut β} {R : ModeCut γ} {S : ModeCut δ}
variable {u : α ≃ β} {v : β ≃ γ}

def Carries (P : ModeCut α) (Q : ModeCut β) (u : α ≃ β) :=
  repackM u u P.e = Q.e

namespace Carries
lemma apply (h : P.Carries Q u) : repackM u u P.e = Q.e := h
lemma ext : P.Carries Q u ↔ ∀ i j, P.e i j = Q.e (u i) (u j) := by
  constructor
  · intro h i j; simpa only [repackM, submatrix_apply, Equiv.symm_apply_apply] using
      congr_fun (congr_fun h.apply (u i)) (u j)
  intro he
  exact Matrix.ext fun i j => by simpa only [repackM,submatrix_apply,Equiv.apply_symm_apply] using he (u.symm i) (u.symm j)

lemma refl (P : ModeCut α) : P.Carries P (Equiv.refl _) := rfl

lemma symm (h : P.Carries Q u) : Q.Carries P u.symm :=
  ext.mpr fun _ _ => (congr_fun (congr_fun h.apply _) _).symm
lemma trans (h : P.Carries Q u) (i : Q.Carries R v) : P.Carries R (u.trans v) :=
  ext.mpr fun _ _ => (ext.mp h _ _).trans (ext.mp i _ _)

lemma pack (h : P.Carries Q u) (X : Matrix α α ℝ) :
    Q.compMat (repackM u u X) = repackM u u (P.compMat X) := by
  unfold ModeCut.compMat
  rw [← h.apply, ← repack_multiply, ← repack_multiply, ← repack_unit u]
  rfl

lemma det (h : P.Carries Q u) (X : Matrix α α ℝ) :
    Q.cutdet (repackM u u X) = P.cutdet X := by
  unfold ModeCut.cutdet; rw [h.pack, repack_det]
lemma log (h : P.Carries Q u) (X : Matrix α α ℝ) :
    Q.cutlog (repackM u u X) = P.cutlog X := congr_arg _ (h.det X)

lemma direct (h : P.Carries Q u) {w : γ ≃ δ} (i : R.Carries S w) :
    (P.direct R).Carries (Q.direct S) (u.sumCongr w) := by
  apply ext.mpr; rintro (a|a) (b|b)
  · exact ext.mp h a b
  · rfl
  · rfl
  exact ext.mp i a b

lemma scroll_iff : P.Carries Q u ↔ P.e * scroll u = scroll u * Q.e := by
  constructor
  · intro h
    exact Matrix.ext fun i j => by simpa only [mul_scroll, scroll_mul,Equiv.apply_symm_apply] using ext.mp h i (u.symm j)
  intro h
  exact ext.mpr fun i j => by simpa only [mul_scroll, scroll_mul,Equiv.symm_apply_apply] using congr_fun (congr_fun h i) (u j)

end Carries

lemma _root_.ExactRunning.Fit.repack {X : ℝ → Matrix α γ ℝ}
    (h : Fit P R X) {w : γ ≃ δ}
    (hu : P.Carries Q u) (hw : R.Carries S w) :
    Fit Q S (fun x => repackM u w (X x)) := by
  refine ⟨(fun _ _ => h.cont ..),?_⟩
  simp only [← hu.apply, ← hw.apply, ← repack_multiply]
  exact fun _ _ => h.van ..

lemma _root_.ExactRunning.Fit.unpack {X : ℝ → Matrix α γ ℝ} {w : γ ≃ δ}
    (h : Fit Q S (fun x => repackM u w (X x))) (hu : P.Carries Q u) (hw : R.Carries S w) :
    Fit P R X := by
  refine (h.repack hu.symm hw.symm).congr ?_
  exact Eventually.of_forall fun x => Matrix.ext fun i j => by simp [repackM]

end ModeCut
namespace Latitude
variable {D E : Latitude}

lemma carries {n : Side} (hr : D.radius = E.radius)
    (e : (Co m α) ≃ (Co n β)) (he : ∀ x, e (D.shift m α x) = E.shift n β (e x)) :
    (D.cut m α).Carries (E.cut n β) e := by
  apply ModeCut.Carries.scroll_iff.mpr (Latitude.cut_of_spin hr _)
  apply Matrix.ext_of_mulVec_single;intro i
  rw [← mulVec_mulVec,← mulVec_mulVec]
  ext j; simp only [spin,scroll_mulVec,Function.comp_apply,he]

lemma direct_carries (D : Latitude) (m : Side) (α β : Type)
    [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    ((D.cut m α).direct (D.cut m β)).Carries (D.cut m (α⊕β)) (Equiv.prodSumDistrib _ _ _).symm := by
  let e := Equiv.prodSumDistrib (Site m) α β
  let Y := fromBlocks (approached (D.cut m α).e) 0 0 (approached (D.cut m β).e)
  unfold ModeCut.Carries
  apply approached_inj
  have he : approached ((D.cut m α).direct (D.cut m β)).e = Y := by
    ext (a|a) (b|b) <;> simp [approached,Y]
  change repackM e.symm e.symm (approached ((D.cut m α).direct (D.cut m β)).e) = _
  rw [he]
  apply mat_ext_on_tune; intro p v
  rw [cut_tune]

  let w := tune p v ∘ e.symm
  have hv : tune p v = w ∘ e.symm.symm := funext fun i => (congr_arg (tune p v) (e.symm_apply_apply i)).symm
  rw [hv, repack_act]

  have hy :
      Y *ᵥ w = (if D.active (mon p) then (1:ℂ) else 0) • w := by
    have l : w ∘ Sum.inl = tune p (v ∘ Sum.inl) := rfl
    have r : w ∘ Sum.inr = tune p (v ∘ Sum.inr) := rfl
    rw [show Y=_ from rfl, fromBlocks_mulVec,l,r,cut_tune,cut_tune,zero_mulVec,zero_mulVec,zero_add,add_zero]
    ext (k|k) <;> rfl
  rw [hy]; rfl
end Latitude
end ExactRunning
