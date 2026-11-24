/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Shoot Wilson Lattice MeasureTheory Filter
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {c n : Side} {b : BudgetPoint}
private theorem blankCalm (n : Side) {r : ℝ} (h : 0≤r) : (1:Config G n)∈calm G n r := by
  intro i _; change G.chord 1 ≤ _; rw [G.chord_one]; linarith

lemma chord_suc (p : Face (Per n)) : G.chord (faceValue (1:Config G n) p) = 0 :=
  le_antisymm (faceBound (blankCalm n le_rfl) _) (G.chord_nonneg _)
private lemma pull_flat (s : Signed) : pull s 0 (1:Config G n) = 1 := by
  funext i; unfold pull Step.read; split <;> simp
private lemma slot_flat (d : Slot) (x : Site n) : d.atSite (1:Config G n) x = 0 := by
  apply norm_le_zero_iff.mp
  unfold Slot.atSite Slot.eval; rw [G.norm_adjoint]; apply (G.curvature_norm _).trans
  let p := (d.offset,d.plaq)
  rw [show faceValue (expandAt x (1:Config G n)) p = faceValue (1:Config G n) (wrap n d.offset+x,d.plaq) from travel_at ..,chord_suc]
private lemma atom_flat {m : ℕ} [NeZero m] (A : Atom G m) (x : Site n) (p : BudgetPoint) :
    A.placed p (1:Config G n) x = 0 := by
  unfold Atom.placed
  by_cases he : Healthy p.threshold (A.footprint x) (1:Config G n)
  · rw [masked_eq _ _ _ _ he]
    unfold Atom.unmasked Atom.poly
    apply Finset.sum_eq_zero; intro i _
    rw [Finset.prod_eq_zero (Finset.mem_univ (0:Fin m)) (by dsimp only; rw [slot_flat]; rfl),mul_zero]
  rw [masked_ne _ _ _ _ he]
private lemma base_flat (R : PathData G) (C : Clip) (p : BudgetPoint) (x : Face (Per n)) :
    R.baseTerm C p (1:Config G n) x=0 := by
  simp only [PathData.baseTerm,PathData.clipped,chord_suc,PathData.ell,PathData.ellTerms,slot_flat,smul_zero,tsum_zero,norm_zero]
  split <;> split <;> ring
theorem channels_heat (R : PathData G)(C : Clip)(P:BudgetPoint)(b:ℝ): R.inChannels C P b (1:Config G n) = 0 := by
  simp only [PathData.inChannels,pull_flat,PathData.principal,base_flat,PathData.atomSeries,atom_flat,tsum_zero,
    Finset.sum_const_zero,add_zero,mul_zero]
end YM.SectorNext.Vacuum
