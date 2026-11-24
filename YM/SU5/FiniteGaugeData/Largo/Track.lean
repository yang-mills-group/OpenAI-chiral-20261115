import YM.SU5.FiniteGaugeData.Largo.Rook
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {a:Type*}[Fintype a][DecidableEq a] (N:Side) {H:Momentum→Op SpinIdx} {σ C:ℝ}
private lemma freight (k:Cover)(f:Cover→Op a): ‖wagon N f k‖ ≤ ‖f k‖:=by refine jump_bound _ _ (norm_nonneg _) (fun _=>?_); rw [norm_smul]; unfold wind; rw [fee_norm,one_mul]
abbrev E₁ (b:Momentum→Op SpinIdx) (N:Side):= Rush.plates N b
def plateH (H: Momentum→Op SpinIdx) (N:Side)(d:ℕ) : Op (Site N × SpinIdx):= ∑ i∈Lattice.box d, wagon N (tub H) i
-- variant size.Exp.Laurent and bool.Tail need only halo sop.
namespace Ream
variable (h: Ream H σ C)(p:0 ≤ σ)
local notation "V"=> wagon N (tub H)
include p h
lemma wagonS: Summable (fun i=> ‖wagon N (tub H) i‖):=Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=> freight N _ _) (h.reserve.unweighted p).2.1
lemma wagonA: E₁ H N= ∑' i, wagon N (tub H) i:=by
 rw [show E₁ H N= _ from (cart_traded h.foe N).symm]; ext i j; unfold cart;
 let u: Op (Site N× SpinIdx) →L[ℂ] ℂ:= LinearMap.toContinuousLinearMap ({ toFun:= fun f=>f i j,map_smul':= by intros; rfl,map_add':=by intros; rfl}: Op (Site N× SpinIdx) →ₗ[ℂ] ℂ); exact (u.map_tsum (h.wagonS N p).of_norm).symm
lemma cartLimit: ‖E₁ H N‖ ≤ C:= h.wagonA N p ▸ (norm_tsum_le_tsum_norm (h.wagonS N p)).trans (((h.wagonS N p).tsum_le_tsum (fun i=> freight N ..) ((h.reserve.unweighted p).2.1)).trans (h.reserve.unweighted p).2.2)
omit h p in
private lemma size_pin (j:Cover)(b:ℕ)(e:j∉Lattice.box b): b ≤ Laurent.size j:=le_of_not_gt fun h=>e (Lattice.box_test.mpr (have he a := lt_of_le_of_lt (Finset.single_le_sum (f:=fun k:Axis=>(j k).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ a)) h; ⟨fun a=>by specialize he a; omega,fun a=>by specialize he a; omega⟩)) -- syntax
lemma tollT (b:ℕ): ‖E₁ H N - plateH H N b‖ ≤ Real.exp (-σ*b)* C := by
 let F:=tub H; let S:= Lattice.box b; let A(i:Cover):= Real.exp (σ*Laurent.size i)*‖F i‖; let K:= Real.exp (-σ*b); have hv:0≤ K:= (Real.exp_pos _).le; rw [wagonA N h p]; change ‖(∑' i,V i)-∑ i∈ S,V i‖≤_; let T:={i:Cover// i∉ S}
 have hx:(∑' i:T,V i.val)+∑ i∈ S,V i=∑' i,V i:= by rw [add_comm]; exact Summable.sum_add_tsum_subtype_compl (h.wagonS N p).of_norm _
 have hp(i:T): ‖V i.val‖ ≤ K*A i.val:=by
    unfold A; rw [←mul_assoc]; apply (freight N _ _).trans; apply le_mul_of_one_le_left (norm_nonneg _); unfold K; rw [←Real.exp_add]; apply Real.one_le_exp; nlinarith only [mul_le_mul_of_nonneg_left (show (b:ℝ) ≤ Laurent.size i.val from Nat.cast_le.mpr (size_pin i.val b i.property)) p]
 have hQ: Summable A:=h.reserve.2.1; have ht:= (h.wagonS N p).subtype (fun i=>i∉S)
 change ‖(∑' i,V i)-_‖ ≤ _; rw [←hx,add_sub_cancel_right]; have hk: (∑' i:T,A i.val) ≤ ∑' i:Cover,A i:= Summable.tsum_subtype_le A _ (fun i=> h.reserve.1 _) hQ; exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hp ((hQ.subtype _).mul_left K)).trans (by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hk.trans h.reserve.2.2) hv))
end Ream
-- halo.B namespace.W
end YM.CF.Window.Largo
