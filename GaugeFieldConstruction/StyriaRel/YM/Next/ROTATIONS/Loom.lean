/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from repos YM/Climb/{Cells,Beams}.lean and YM/Spin/Sheets.lean for new register
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Yard
import GaugeFieldConstruction.StyriaRel.YM.Ward.Axis
import GaugeFieldConstruction.StyriaRel.YM.Work.A01.Conserve
noncomputable section
namespace YM.NSF
open Function Set Filter Ward Table
open scoped Topology BigOperators ContDiff ComplexOrder Matrix.Norms.Frobenius
namespace Spin
abbrev Ind := Axis × Axis
abbrev K (p : Ind) := Ortho.plane p.1 p.2

/-- Need equality for all Ω, not just generating planes. No unnoticed constants. -/
lemma spans : Submodule.span ℝ (Set.range K) = ⊤ := by
  -- express any matrix Ω as half sum over all ordered
  rw [eq_top_iff]; intro x hx; change Ortho.Skew at x
  have hb : ((2:ℝ) • x) = ∑ i : Axis, ∑ j : Axis, (x.val i j) • K (i,j) := by
    apply Subtype.ext; ext i j
    simp only [SetLike.val_smul, Submodule.coe_sum,K]
    have he : star x.val= -x.val := x.property
    have hz : x.val j i= -x.val i j := by
      have hm := congr_arg (fun z : M4 => z i j) he
      simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial, Matrix.neg_apply] using hm
    simp [Ortho.plane,Matrix.sum_apply,Matrix.single_apply,mul_sub,mul_ite, Finset.sum_sub_distrib,ite_and] -- hz
    rw [hz]
    ring
  rw [show x=(2:ℝ)⁻¹ • ∑ i : Axis, ∑ j:Axis,(x.val i j) • K (i,j) from by rw [← hb,inv_smul_smul₀ two_ne_zero]] -- dependant occurrences!
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  exact (Submodule.span ..).smul_mem _ (Submodule.subset_span (mem_range_self _))

lemma extendsE {A : Type*} [AddCommGroup A] [Module ℝ A]
    (f g : Ortho.Skew →ₗ[ℝ] A) (h : ∀ i, f (K i) = g (K i)) : f=g := by
  -- ext by spanning
  apply sub_eq_zero.mp
  suffices he : LinearMap.ker (f-g)=⊤ from LinearMap.ker_eq_top.mp he
  rw [eq_top_iff,← spans,Submodule.span_le]; rintro _ ⟨i,rfl⟩; apply LinearMap.mem_ker.mpr; simp [h i]

end Spin
namespace Climb
variable {G : Gauge} {L : Register G} {S : Table L}
abbrev Parts (S : Table L) := ∀ d, Axis → S.Field d→ₗ[ℂ] S.Field (d+1)
/-- Param pivot used BEFORE assigning any spin law. -/
structure Pre (H : S.Hierarchy) (V : DiffPlan S) (J : S.Stress) (p : Parts S) (Y : SpinRows S) : Prop where
  tensor : Conserved V H.spin J
  symmetric : RawTensor H.spin J
  raw : StressLaws S J p Y


def localTurn (p : Parts S) (T : SpinRows S) (K : Ortho.Skew) {n : ℕ} (q : Fin n → S.Tag) (x : Points n) :=
    ∑ i, (disc (update q i (turns T K (q i))) x + ∑ b : Axis, ((M4.move K.val (x i) b) •
      disc (update q i (⟨_,p _ b (q i).2⟩:S.Tag)) x))

end Climb
end YM.NSF
