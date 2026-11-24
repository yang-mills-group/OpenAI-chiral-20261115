import YM.SU5.FiniteGaugeData.Celeritas.Dynamo
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
open scoped Classical
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(v:Cross a)(u:ℝ≥0)(z:ℂ)(w x:H)(t:ℝ)(P:Cinema S)(Q:‖v‖≤1)
local notation "W" => wheelB S v u
local notation "Z"=> lanes (u:ℝ)
local notation "T" t:max => S.U (t • v)*S.E u
-- left ray bundle; returns (Test_i, applied operator).L
abbrev paceB(z:ℂ)(x y:H):ℂ:= (W z (x+y)- W z (x-y)- Complex.I * W z (x+ I • y)+ Complex.I*W z (x-I • y))/4
local notation "Θ"=> paceB S v u
include P Q
lemma pace_paid_real (x y:H): paceB S v u (t:ℂ) x y=inner ℂ x ((T t) y):=by
 let A:=T t; unfold paceB; simp_rw [wheel_r S v t u _ P Q]; let q(x y:H):= inner ℂ x (A y); change (q ..-q ..-I * q .. + I*q ..)/_ = _; -- placeholders tune. expand
 unfold q; simp only [map_add,map_sub, inner_add_left,inner_add_right, map_smul,inner_smul_left,inner_smul_right,Complex.conj_I,inner_sub_left,inner_sub_right]; ring_nf; simp; change _=inner ℂ x (A y); ring -- wrong sign? wheel x+I*y diag = i Bxy -i Byx. diff combination -i adds Bxy
lemma pace_hol(x y:H) : AnalyticOnNhd ℂ (fun z=>paceB S v u z x y) Z:=by
 intro z h; let Ta(w:H):=lap_hol S v u w P Q z h; unfold paceB; -- t1-t2-...; infer 
 exact ((((Ta _).sub (Ta _)).sub (analyticAt_const.mul (Ta _))).add (analyticAt_const.mul (Ta _))).div analyticAt_const (by norm_num)
-- energy.Hstar
variable (l:z∈lanes (u:ℝ))
include l
lemma pace_sum (x y w:H): paceB S v u z x (y+w)= paceB S v u z x y+paceB S v u z x w:=
 settleA (u:ℝ) z l (pace_hol S v u P Q x (y+w)) ((pace_hol S v u P Q x y).add (pace_hol S v u P Q x w)) (fun t=>by simp only [Pi.add_apply]; rw [pace_paid_real S v u t P Q,pace_paid_real S v u t P Q,pace_paid_real S v u t P Q,map_add,inner_add_right]) -- args
lemma pace_cap (x y:H)(c:ℂ): paceB S v u z x (c • y)= c * paceB S v u z x y:=
 settleA (u:ℝ) z l (pace_hol S v u P Q x (c • y)) (AnalyticOnNhd.mul (analyticOnNhd_const (v:=c)) (pace_hol S v u P Q x y)) (fun t=>by simp only [pace_paid_real S v u _ P Q,map_smul,inner_smul_right]) -- tune
lemma pace_plus (x y w:H): Θ z (x+y) w= Θ z x w+Θ z y w:= by
 apply settleA (u:ℝ) z l (pace_hol S v u P Q _ _) (AnalyticOnNhd.add (pace_hol S v u P Q x w) (pace_hol S v u P Q y w)); intro p; simp only [Pi.add_apply,pace_paid_real S v u p P Q,map_add,inner_add_left]
lemma pace_warm (c:ℂ)(x y:H): Θ z (c • x) y = (starRingEnd ℂ c) * Θ z x y := by
 apply settleA (u:ℝ) z l (pace_hol S v u P Q _ _) (AnalyticOnNhd.mul analyticOnNhd_const (pace_hol S v u P Q x y)); intro p; simp only [pace_paid_real S v u p P Q,inner_smul_left]
-- build sesqui B z then continuous
lemma pace_4 (x y:H)(p:‖x‖≤1)(q:‖y‖≤1): ‖paceB S v u z x y‖ ≤ 4 := by
 let A:= W z; have hp(x:H)(p:‖x‖ ≤ 2): ‖A x‖ ≤ 4:=(wheel_bound S v u x P Q z l).trans (by nlinarith only [p,norm_nonneg x]); -- order z
 unfold paceB; rw [norm_div]; let X:=x+I • y; let Y:=x-I • y; let a:=A (x+y); let b:=A (x-y); let U:=I*A X; let V:=I*A Y; change ‖a-b-U+V‖ /_≤ _; have hx:‖(4:ℂ)‖=(4:ℝ):=by norm_num
 have hb:‖U‖=‖A X‖:=by unfold U; simp; -- caret
 have hc:‖V‖=‖A Y‖:=by unfold V; simp
 have hw:‖I • y‖=‖y‖:=by simp [norm_smul]
 rw [hx]; apply (div_le_iff₀ (by norm_num : 0<(4:ℝ))).2; linarith only [norm_sub_le (a-b) U, norm_add_le (a-b-U) V,hb,hc,norm_sub_le a b,hp X ((norm_add_le ..).trans (by rw [hw]; linarith)),hp Y ((norm_sub_le ..).trans (by rw [hw]; linarith)),hp (x+y) ((norm_add_le ..).trans (by linarith)),hp (x-y) ((norm_sub_le ..).trans (by linarith))]
lemma pace_l (x y:H): ‖paceB S v u z x y‖ ≤ 4*‖x‖*‖y‖ :=by
 by_cases p:x=0; · subst x; have he:=pace_warm S v u z P Q l 0 (0:H) y; rw [zero_smul,map_zero, zero_mul] at he; rw [he,norm_zero]; positivity
 by_cases t:y=0; · subst y; have he:=pace_cap S v u z P Q l x (0:H) 0; rw [zero_smul, zero_mul] at he; rw [he,norm_zero]; positivity
 let X:=‖x‖; let Y:= ‖y‖; have h:0<X:= norm_pos_iff.mpr p; have h':0<Y:=norm_pos_iff.mpr t; let σ(r:ℝ):ℂ:= ↑(r⁻¹); have hv(r:ℝ)(p:0<r):‖σ r‖=r⁻¹:= Complex.norm_real (r⁻¹) |>.trans (Real.norm_of_nonneg (inv_nonneg.mpr p.le));
 let x':=σ X • x; let y':=σ Y • y; have hx:‖x'‖=1:=by rw [show x'=σ X • x from rfl,norm_smul,hv _ h]; exact inv_mul_cancel₀ h.ne'
 have hz:‖y'‖=1:=by rw [show y'=σ Y • y from rfl,norm_smul,hv _ h']; exact inv_mul_cancel₀ h'.ne'
 have hk:=pace_4 S v u z P Q l x' y' hx.le hz.le; unfold x' y' at hk; rw [pace_warm S v u z P Q l,pace_cap S v u z P Q l, show starRingEnd _ (σ X)=σ X from conj_ofReal _, norm_mul,norm_mul,hv X h,hv Y h'] at hk; rw [inv_mul_le_iff₀ h,inv_mul_le_iff₀ h'] at hk; change _≤4 * X * Y; nlinarith only [hk]
-- B as H→L*[ℂ] H→L cc.
def cupQ(l:z∈ Z):H.Op:=
 let E:H.space→ₗ⋆[ℂ] H.space→ₗ[ℂ]ℂ:={
        toFun x:={ toFun:=paceB S v u z x,map_add' y w:= pace_sum S v u z P Q l x y w,map_smul' b y:=pace_cap S v u z P Q l x y b}
        map_add' x y:=LinearMap.ext fun w=>pace_plus S v u z P Q l x y w
        map_smul' b y:=LinearMap.ext fun w=>pace_warm S v u z P Q l b y w }
 (InnerProductSpace.continuousLinearMapOfBilin (E.mkContinuous₂ 4 (pace_l S v u z P Q l))).adjoint
def cup (v:Cross a)(Q:‖v‖≤1)(z:ℂ): H.Op:= if l:z∈lanes (u:ℝ) then cupQ S v u z P Q l else 0
lemma credit_c (x y:H) : inner ℂ x (cup S u P v Q z y) = paceB S v u z x y:=by
 rw [cup,dif_pos l]; unfold cupQ; rw [ContinuousLinearMap.adjoint_inner_right]; exact InnerProductSpace.continuousLinearMapOfBilin_apply .. -- tune args
#print axioms pace_l
local notation "B"=> cup S u P v Q
omit l P Q in
private lemma op_compare (E:H.Op)(c:ℝ)(p:0≤c)(g:∀ x y:H,‖x‖=1→ ‖y‖=1→ ‖inner ℂ y (E x)‖ ≤ c):‖E‖≤c:=ContinuousLinearMap.opNorm_le_of_re_inner_le p fun x y u v=> Complex.re_le_norm ..|>.trans ((show ‖inner ℂ (E x) y‖=‖inner ℂ y (E x)‖ from (by rw [← inner_conj_symm y (E x)]; simp only [Complex.norm_conj])).trans_le (g x y u v)) -- omit l etc
lemma cupH : ‖cup S u P v Q z‖ ≤ 4:= op_compare _ _ (by norm_num) (fun x y px py=>by rw [credit_c S v u z P Q l]; exact pace_4 S v u z P Q l _ _ py.le px.le)
omit l in
lemma credit_h (e:0 < u): cup S u P v Q (↑t)= S.U (t • v)*S.E u:=by ext1 x; apply ext_inner_left ℂ; intro y; rw [credit_c S v u t P Q (lanes_r t u e) y x]; exact pace_paid_real S v u t P Q y x -- signature
omit l
set_option maxRecDepth 4000 in
lemma cup_l : ContinuousOn (cup S u P v Q) (lanes u):= by
 intro p q; obtain ⟨r,hp,h⟩:= nhds_basis_closedBall.mem_iff.mp ((lanes_open _).mem_nhds q); let s:=r/2; have hs:0<s:=half_pos hp; let U:= closedBall p s; let V:=closedBall p r; have hh(x)(b:x∈ U): closedBall x s ⊆ V:= by
    exact fun z e=> (show dist z p ≤ r from (dist_triangle z x p).trans ((add_le_add (Metric.mem_closedBall.mp e) (Metric.mem_closedBall.mp b)).trans_eq (add_halves _))) -- invalid x arg.
 have hV:U⊆lanes u:= (closedBall_subset_closedBall (half_le_self hp.le)).trans h
 let c:ℝ:=4/s; have hc:0<c:=div_pos (by norm_num) hs; have he(x y:H)(hx:‖x‖=1)(hv:‖y‖=1)(z:ℂ)(L:z∈ U): ‖paceB S v u p y x- paceB S v u z y x‖≤ c*dist z p:=by
   let Tℓ (z):=paceB S v u z y x; have hk(z)(L:z∈ Z): DifferentiableAt ℂ Tℓ z:= (pace_hol S v u P Q y x z L).differentiableAt
   apply le_trans (Convex.norm_image_sub_le_of_norm_deriv_le (C:=c) (fun x t=>hk x (hV t)) ?_ (convex_closedBall ..) L (Metric.mem_closedBall_self hs.le)) ?_
   · intro z L; have hr:closedBall z s⊆lanes _:= (hh z L).trans h; apply norm_deriv_le_of_forall_mem_sphere_norm_le hs ((show DifferentiableOn ℂ Tℓ (closedBall z s) from fun x t=> (hk x (hr t)).differentiableWithinAt ).diffContOnCl_ball subset_rfl); intro w t; exact pace_4 S v u w P Q (hr (sphere_subset_closedBall t)) y x hv.le hx.le
   rw [←dist_eq_norm,dist_comm]
 refine ContinuousAt.continuousWithinAt (Metric.tendsto_nhds.mpr fun ε e=> ?_); filter_upwards [Metric.ball_mem_nhds p hs,Metric.ball_mem_nhds p (div_pos e hc)] with z L E
 rw [dist_comm,dist_eq_norm]; refine lt_of_le_of_lt (op_compare _ (c*dist z p) (by positivity) (fun x y a b=> ?_)) ?_
 · rw [_root_.sub_apply,inner_sub_right,credit_c S v _ p P Q q, credit_c S v _ z P Q (hV (ball_subset_closedBall L))]; exact he x y a b z (ball_subset_closedBall L)
 exact mul_comm c _ ▸ (lt_div_iff₀ hc).1 E
lemma cup_A : AnalyticOnNhd ℂ (cup S u P v Q) Z:= by
 let e(x y:H):= (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ H.space x); let L:=(Set.range (fun p:H.space× H.space=>e p.1 p.2)); apply YM.Analysis.lift_weak L _ (lanes_open _) (cup_l S v u P Q); swap
 · rintro x y g; apply ContinuousLinearMap.ext; intro w; exact ext_inner_left ℂ (fun u:H.space=>g (e w u) ⟨(w,u),rfl⟩)
 rintro f ⟨⟨x,y⟩,rfl⟩; apply DifferentiableOn.congr (pace_hol S v u P Q y x).differentiableOn; intro i x'; exact credit_c S v u i P Q x' y x -- include implicit.Proof
#print axioms cup_A
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
