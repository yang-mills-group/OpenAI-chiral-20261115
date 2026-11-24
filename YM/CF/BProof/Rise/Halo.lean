import YM.CF.BProof.Rise.Plate
set_option autoImplicit false
/-! Matrix smooth exp. independent of norm on Gauge matrix in rest. -/
noncomputable section
namespace YM.CF.BProof.Cliff
open SU
open scoped Topology ContDiff Matrix.Norms.Frobenius
lemma smoothExp(i j:SU.F): ContDiff ℝ ∞ (fun x:SU.group.Color=>SU.fund (group.lieExp x) i j):=by
 let L:group.Mat→ₗ[ℝ]ℂ:=⟨⟨fun x=> x i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩; exact L.toContinuousLinearMap.contDiff.comp (SU.group.exp_jet.of_le le_top)
end YM.CF.BProof.Cliff
