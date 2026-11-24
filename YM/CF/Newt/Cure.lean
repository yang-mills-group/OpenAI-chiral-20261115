import YM.CF.Newt.Plum
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Dissent
import YM.Push.FREE_RESOLVENT.Test
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ: Type} [Fintype ι] [Fintype τ] {C D v K d N X U s r a e:ℝ}{n:ℕ}
open Next.SectorChange (panels shots)
variable {S G:Gauge}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
-- colors
abbrev Mast(G:Gauge)(c:Side):= Fish (Push.Uniform.Primary c G)
def hull(G:Gauge)(c:Side):Mast G c→L[ℝ] Directions G c:= LinearMap.toContinuousLinearMap { toFun := fun z=> collect G ((Push.Uniform.tint G _) z), map_add':=fun _ _=>rfl, map_smul':=fun _ _=>rfl }
lemma hull_n : ‖hull G c‖ ≤ Uniform.shade G:=by
 refine ContinuousLinearMap.opNorm_le_bound _ (Uniform.shade_pos _).le fun i=>?_
 apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Uniform.shade_pos _).le (norm_nonneg _))).mpr
 exact fun j=> (norm_le_pi_norm (Uniform.tint G _ i) (j.1,coord j.2)).trans (Uniform.tint_le i)
lemma hull_h(u:Mast G c): ‖reader G c (hull G c u)‖≤‖u‖:=by
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr; exact fun j=> norm_le_pi_norm u ((j.1.1,coord j.1.2),j.2)
section panes
variable (F:Forest T.ratio) (x:ℝ)
def pageX : (Key F G)≃Next.SectorChange.Rows.In x (bareStores T) F (G:=G):=Assembly.opened G T x (bareStores T) F (Assembly.bare_is_Clear T x F)
def visitX : Fish (Next.SectorChange.Rows.In x (bareStores T) F (G:=G))→L[ℝ] Fish (Key F G):=LinearMap.toContinuousLinearMap { toFun:=fun f=> f ∘ (pageX (G:=G) F x), map_add':=fun _ _=> rfl,map_smul':=fun _ _=> rfl}
def leaveX : Fish (Key F G) →L[ℝ] Fish (Next.SectorChange.Rows.In x (bareStores T) F (G:=G)):=LinearMap.toContinuousLinearMap { toFun:=fun f=> f ∘ (pageX (G:=G) F x).symm, map_add':=fun _ _=> rfl,map_smul':=fun _ _=> rfl}
lemma visit_n : ‖visitX (G:=G) F x‖≤1:=by refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>?_ ; rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> norm_le_pi_norm i _
lemma leave_n : ‖leaveX (G:=G) F x‖≤1:=by refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>?_ ; rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> norm_le_pi_norm i _
lemma visit_left(i: Fish (Key F G)):visitX F x (leaveX F x i)=i:=funext fun j=>congrArg i ((pageX F x).symm_apply_apply _)
lemma visit_right(i: Fish (Next.SectorChange.Rows.In x (bareStores T) F (G:=G))):leaveX F x (visitX F x i)=i:=funext fun j=>congrArg i ((pageX F x).apply_symm_apply _)
lemma tableVisit (A:Matrix (Next.SectorChange.Rows.In x (bareStores T) F (G:=G)) (Next.SectorChange.Rows.In x (bareStores T) F (G:=G)) ℝ): paintO (A.submatrix (pageX F x) (pageX F x))= (visitX F x).comp ((paintO A).comp (leaveX F x)):=by
 ext i j; let e:=pageX F x (G:=G)
 change ∑ y, A _ (e y)*i y=∑ y,A _ y*i (e.symm y); rw [← e.sum_comp]; simp
end panes
section norms
lemma mtr_op (A:Matrix ι ι ℝ){p:ι→Site c}(h:(FreeResolvent.native c).Schur p p v C A)(hv:0 ≤ v)(ht:0 ≤ C): ‖paintO A‖ ≤ C:=by
 have hw:= h.mono hv le_rfl
 refine ContinuousLinearMap.opNorm_le_bound _ ht fun i => ?_; apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht (norm_nonneg _))).mpr
 intro j
 have hh : ∑ k, |A j k| ≤ C:= by simpa using hw.rows.bound j
 rw [paintO_p]; change |∑ k, A j k*i k|≤ _
 apply (Finset.abs_sum_le_sum_abs ..).trans; apply le_trans (Finset.sum_le_sum (g:=fun k=>|A j k| * ‖i‖) fun k _=>?_)
 · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
 rw [abs_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm i _) (abs_nonneg _)
lemma polar_cash (H:Directions G c)(A:PriceCoords G c→ Matrix ι ι ℝ){p:ι→Site c}(hp:Polar (reader G c H) p p A n v C)(hC:0≤C)(hv:0<v):Allows n (fun y=>paintO ((A ∘ reader G c) y)) H (activation G n 0 v*C):=by
 have hy: Next.SectorChange.tape (reader G c H)=H:= Next.SectorChange.gaugeCount.apply_symm_apply H
 have he:= Polar.weighted 0 hp hv hC
 let G':= fun y=>paintO ((A∘reader G c) y); have h : ContDiffAt ℝ n (cart A) H:= by rw [← hy]; exact he.smooth
 have hh : ContDiffAt ℝ n G' H:= by change ContDiffAt ℝ (↑n:WithTop ℕ∞) ((paintO (τ:=ι)) ∘ cart A) H; exact ((paintO (τ:=ι)).contDiff.contDiffAt.comp _ h)
 have hm :0 ≤ activation G n 0 v*C:=mul_nonneg (zero_le_one.trans (activation_one G n 0 hv)) hC
 refine ⟨hh,fun j hj=> Planned.AtomRegular.op_le_of_unit hm fun y hy'=>?_⟩
 change ‖iteratedFDeriv ℝ j (paintO ∘ cart A) _ _‖≤ _
 erw [paintO.iteratedFDeriv_comp_left h (Nat.cast_le.mpr hj)]; let t:=List.ofFn y
 have hw:Afford 1 0 (0:Site c) t:= by unfold t Afford; rw [List.forall_mem_ofFn_iff]; intro i k; simp [FreeResolvent.Mark.hill]; exact (norm_le_pi_norm ..).trans (hy' _)
 have hX:=he.each 0 zero_le_one t (List.length_ofFn.trans_le hj) hw
 rw [hy] at hX; unfold t at hX; rw [FreeResolvent.Stars.list_result] at hX; let T:=iteratedFDeriv ℝ j (cart A) H y
 change ‖paintO T‖≤_
 apply mtr_op T (p:=p) (v:=v) _ hv.le hm; constructor
 · refine ⟨fun i=>?_⟩; have ht:= hX.row.rows i; simpa only [one_pow,mul_one,FreeResolvent.Mark.payment,FreeResolvent.Mark.hill, pow_zero,inv_one,one_mul,id_comp] using ht
 refine ⟨fun i=>?_⟩; have ht:= hX.col.rows i; simpa only [one_pow,mul_one,FreeResolvent.Mark.payment,FreeResolvent.Mark.hill,pow_zero,inv_one,one_mul,id_comp] using ht
end norms
end YM.CF.Newt
