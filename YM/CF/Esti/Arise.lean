import YM.CF.Esti.Ache
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Dissent
import YM.Push.FREE_RESOLVENT.Test
set_option autoImplicit false
noncomputable section
namespace YM.CF.Esti
open Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ: Type} [Fintype ι] [Fintype τ] {C D v K d N X U s r a e:ℝ}{n:ℕ}
open Next.SectorChange (panels shots)
variable {S G:Gauge}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
open Newt Matrix
def ranQ : Matrix ι τ ℝ →L[ℝ] Fish τ →L[ℝ] Fish ι := LinearMap.toContinuousLinearMap { toFun := fun x => LinearMap.toContinuousLinearMap x.mulVecLin, map_add':=fun x y=>by ext1 i; exact add_mulVec _ _ _, map_smul':=fun x y=>by ext1 i; exact smul_mulVec _ _ _ }
lemma rad_p(A: Matrix ι τ ℝ)(z: Fish τ): ranQ A z=A *ᵥ z:=rfl
section norms
lemma linearH (A:Matrix ι τ ℝ){p:ι→Site c}{q:τ→Site c}(h:(FreeResolvent.native c).Schur p q v C A)(hv:0 ≤ v)(ht:0 ≤ C): ‖ranQ A‖ ≤ C:=by
 have hw:= h.mono hv le_rfl
 refine ContinuousLinearMap.opNorm_le_bound _ ht fun i => ?_; apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht (norm_nonneg _))).mpr
 intro j
 have hh : ∑ k, |A j k| ≤ C:= by simpa using hw.rows.bound j
 rw [rad_p]; change |∑ k, A j k*i k|≤ _
 apply (Finset.abs_sum_le_sum_abs ..).trans; apply le_trans (Finset.sum_le_sum (g:=fun k=>|A j k| * ‖i‖) fun k _=>?_)
 · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
 rw [abs_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm i _) (abs_nonneg _)
lemma radon (H:Directions G c)(A:PriceCoords G c→ Matrix ι τ ℝ){p:ι→Site c}{q:τ→Site c}(hp:Polar (reader G c H) p q A n v C)(hC:0≤C)(hv:0<v):Allows n (fun y=>ranQ ((A ∘ reader G c) y)) H (activation G n 0 v*C):=by
 have hy: Next.SectorChange.tape (reader G c H)=H:= Next.SectorChange.gaugeCount.apply_symm_apply H
 have he:= Polar.weighted 0 hp hv hC
 let G':= fun y=>ranQ ((A∘reader G c) y); have h : ContDiffAt ℝ n (cart A) H:= by rw [← hy]; exact he.smooth
 have hh : ContDiffAt ℝ n G' H:= by change ContDiffAt ℝ (↑n:WithTop ℕ∞) ((ranQ (τ:=τ)) ∘ cart A) H; exact ((ranQ (τ:=τ)).contDiff.contDiffAt.comp _ h)
 have hm :0 ≤ activation G n 0 v*C:=mul_nonneg (zero_le_one.trans (activation_one G n 0 hv)) hC
 refine ⟨hh,fun j hj=> Planned.AtomRegular.op_le_of_unit hm fun y hy'=>?_⟩
 change ‖iteratedFDeriv ℝ j (ranQ ∘ cart A) _ _‖≤ _
 erw [ranQ.iteratedFDeriv_comp_left h (Nat.cast_le.mpr hj)]; let t:=List.ofFn y
 have hw:Afford 1 0 (0:Site c) t:= by unfold t Afford; rw [List.forall_mem_ofFn_iff]; intro i k; simp [FreeResolvent.Mark.hill]; exact (norm_le_pi_norm ..).trans (hy' _)
 have hX:=he.each 0 zero_le_one t (List.length_ofFn.trans_le hj) hw
 rw [hy] at hX; unfold t at hX; rw [FreeResolvent.Stars.list_result] at hX; let T:=iteratedFDeriv ℝ j (cart A) H y
 change ‖ranQ T‖≤_
 apply linearH T (p:=p) (q:=q) (v:=v) _ hv.le hm; constructor
 · refine ⟨fun i=>?_⟩; have ht:= hX.row.rows i; simpa only [one_pow,mul_one,FreeResolvent.Mark.payment,FreeResolvent.Mark.hill, pow_zero,inv_one,one_mul,id_comp] using ht
 refine ⟨fun i=>?_⟩; have ht:= hX.col.rows i; simpa only [one_pow,mul_one,FreeResolvent.Mark.payment,FreeResolvent.Mark.hill,pow_zero,inv_one,one_mul,id_comp] using ht
end norms
end YM.CF.Esti
