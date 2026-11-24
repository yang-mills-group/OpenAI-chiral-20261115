import YM.SU5.Thin.Press.Fiord
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Sleigh
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory SectorNext.Vacuum
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations Metric
variable {G:Gauge}{A:ChartRatio G}(H:LocalRatio A){ε r κ:ℝ}
lemma rail_out (G:Gauge){B:Set G.El}(hp:MeasurableSet B)(v:0<κ)(u:0<ε)(H:∀ x∈B,ε≤ G.price x): Paddled (-1) (fun x:ℝ=> x^dim G*(∫ y in B,mouth G (κ*x^2) y ∂G.probHaar)):=by
 let F(t):=∫ y in B,mouth G (κ*t^2) y ∂G.probHaar; let a:=κ*ε; have ha:0<a:=mul_pos v u
 obtain ⟨C,c,hc⟩:= snow_max (dim G+1) ha; refine ⟨C,c,?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ)] with x t
 let V:=Real.exp (-a*x^2); have hc': V>0:= Real.exp_pos _; have H'x:0 ≤ F x:=setIntegral_nonneg hp (fun i _=>(mouth_pos _ _ _).le); have hk:F x≤V:=by
    apply le_trans (setIntegral_mono_on (f:=fun i=>mouth _ _ i) (mouth_int _ _).integrableOn (g:=fun _=>V) integrableOn_const hp (fun i g=>?_))
    · rw [setIntegral_const,smul_eq_mul]; exact mul_le_of_le_one_left hc'.le measureReal_le_one -- arg explicit?
    apply Real.exp_monotone; unfold a; nlinarith only [mul_le_mul_of_nonneg_left (H i g) (show 0≤κ*x^2 by positivity)]
 rw [Real.rpow_neg_one, ← div_eq_mul_inv,le_div_iff₀ t]; change |x^dim G*F x| *x ≤ C; rw [abs_of_nonneg (by positivity : 0≤ x^dim G*F x)]; have he: x^(dim G+1)*V ≤ _:=hc x t.le; rw [pow_succ] at he; nlinarith only [he,mul_le_mul_of_nonneg_left hk (show 0 ≤ x^dim G*x by positivity)]
include H
lemma singleWater(v:0<κ):Paddled (-1) (fun x:ℝ=> x^dim G *linkZ G (κ*x^2)-narrow A κ):=by
 obtain ⟨r,ε,D,r0,R,p,h,Y,U⟩:= kernel_ball A H
 let B:= G.lieExp '' closedBall 0 r; have hp:MeasurableSet B:= ((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet
 refine ((fiord_earned H r0 R h v Y).add (rail_out G hp.compl v p (fun y u=>U y u))).agree (Eventually.of_forall fun x=>?_)
 dsimp only; unfold linkZ; let t(y:G.El):=mouth G (κ*x^2) y; rw [sub_add_eq_add_sub, ← mul_add,show G.lieExp '' _= B from rfl, integral_add_compl hp (mouth_int G (κ*x^2))]
lemma singleLog(v:0<κ):Paddled (-1) (fun x:ℝ=> Real.log (x^dim G*linkZ G (κ*x^2))-Real.log (narrow A κ)):=by
 let t:=narrow A κ; have hp:0<t:=narrow_pos A H κ v; let F(x:ℝ):=x^dim G*linkZ G (κ*x^2); let z:=t/2; have h:0<z:=half_pos hp; let G(x:ℝ):= F x-t; have hx:=singleWater H v
 apply (hx.scale z⁻¹).caps; filter_upwards [(first_asymptotic A H κ v).eventually (le_mem_nhds (show z<t from half_lt_self hp))] with x h'
 let f:= F x; have he:z≤f:=h'; apply (log_swing h he (half_le_self hp.le)).trans; rw [abs_mul,abs_of_pos (inv_pos.mpr h)] -- `goal ≤` use exact le_rfl
end YM.Sleigh
