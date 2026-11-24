import YM.SU5.FiniteGaugeData.ArchiveK.Mogul
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
variable (G:E4≃ₗᵢ[ℝ] E4)(p:Space3) (y:E4)(n:ℕ)
set_option quotPrecheck false
local notation "ℙ"=> E4≃ₗᵢ[ℝ] E4
open Submodule
-- economical spatial exponents
lemma visitQ(v:E4)(t:‖v‖=1):∃ G:ℙ, sailX G=v:=by
 let u:=sailX (LinearIsometryEquiv.refl ℝ E4); exact ⟨reflection (ℝ ∙ (u-v))ᗮ, reflection_sub ((sail_size _).trans t.symm)⟩
lemma ocean_f(x:E4) : ∃ G:ℙ,depthG G x= ‖x‖:=by
 by_cases h:x=0; · subst x; exact ⟨LinearIsometryEquiv.refl ℝ _,by simp [depthG]⟩
 let t:= ‖x‖⁻¹; let v:=t • x; have he:0<‖x‖:=norm_pos_iff.mpr h
 obtain ⟨G',p⟩:=visitQ v (by unfold v; rw [norm_smul]; simp [t, Real.norm_of_nonneg (inv_nonneg.mpr he.le),h]); refine ⟨G',?_⟩; unfold depthG; rw [p]; unfold v; rw [real_inner_smul_left,real_inner_self_eq_norm_sq]; unfold t; field_simp
#check summable_nat_add_iff
section price
open NormedSpace
variable {r:ℝ} (u:0<r)(t:r≤1)(z:ℂ)
include u t
lemma murmurE : ‖Complex.exp z-say n z‖ ≤ r^n * Real.exp (‖z‖/r):=by
 apply (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z n).trans; let x(y:ℝ)(n:ℕ):= y^n/(n.factorial:ℝ); let V:= ‖z‖; let B:= V/r; let S :=Finset.range n; let T:={i:ℕ//i∉ S}; have he(x:ℝ): (NormedSpace.exp x) = Real.exp x:=by rw [Real.exp_eq_exp_ℝ]; -- preced
 have hk(y:ℝ): HasSum (x y) (Real.exp y):= (he y) ▸ expSeries_div_hasSum_exp y; have hv(i:T): x V i.val ≤ r^n * x B i.val:= by
    have hb:n≤ i.val:= by simpa [S] using i.property
    have hm:0≤B:=by unfold B; positivity;
    have hq:0≤x B i.val:= by unfold x; positivity
    let a:=i.val; apply le_trans (le_of_eq (b:=r^a*x B i.val) ?_) (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one u.le t hb) hq); -- tune preced let
    unfold x; nth_rw 1 [show V=r*B from (by unfold B; field_simp)]; rw [mul_pow]; ring
 change Real.exp V - _ ≤ r^n * Real.exp B; rw [← (hk V).tsum_eq, ← (hk B).tsum_eq,←(hk V).summable.sum_add_tsum_subtype_compl S]; rw [add_comm]; rw [show ∑ i∈S,x V i = ∑ i∈ Finset.range n, ‖z‖^i/(i.factorial:ℝ) from rfl, add_sub_cancel_right]; let HB:= hk B
 apply le_trans (Summable.tsum_le_tsum hv ((hk V).summable.subtype _) ((HB.summable.subtype _).mul_left (r^n))); rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (Summable.tsum_subtype_le (x B) _ (by intro a; unfold x B; positivity) HB.summable) (pow_nonneg u.le _)
end price
-- ξ price estimates.
def salt (G:ℙ)(p:Space3)(x:E4)(i:Axis):= flute G p i * rise (pulseG G p) x
local notation "E"=> ‖p‖
local notation "Σ"=> pulseG G p
lemma saltB (i:Axis)(x:E4) (a:ℝ) (t:a ≤ depthG G x-20): ‖salt G p x i‖ ≤ 2*τ *Real.exp (-‖p‖*a):=by
 unfold salt; rw [norm_mul,loftB]; apply (mul_le_mul_of_nonneg_right (flute_pay ..) (Real.exp_pos _).le).trans; rw [mul_assoc,←Real.exp_add]; gcongr; nlinarith only [mul_le_mul_of_nonneg_left t (norm_nonneg p)]
@[fun_prop] lemma salt_m(x:E4)(i:Axis): Measurable (fun p=> salt G p x i):=(flute_m G i).mul ((show Continuous (fun p=> rise (pulseG G p) x) from (rise_safe.comp ((pulse_cont G).prodMk (continuous_const (y:=x))))).measurable)
lemma remotePt (n:ℕ)(x:E4)(a:Axis){r:ℝ}(t:0<r)(g:r≤1)(v: 100 < depthG G x)(u:32*‖y‖≤ r *depthG G x):
 ‖salt G p x a * (rise (pulseG G p) y - say n (murmur y (pulseG G p)))‖ ≤ (r^n)*(2*τ*Real.exp (-1*‖p‖)):=by
 let z:=murmur y (Σ); let H:=depthG G x; have hr:0<H:=lt_trans (by norm_num) v; rw [norm_mul]; have he: ‖rise (pulseG G p) y - say n z‖ ≤ r^n*Real.exp ((H/2)*E):= by
    have hm: ‖z‖/r ≤ H/2*E:=by rw [div_le_iff₀ t]; apply (mur_fee ..).trans; nlinarith only [mul_le_mul_of_nonneg_right u (norm_nonneg p), mul_nonneg (norm_nonneg p) (mul_nonneg t.le hr.le)]
    exact (murmurE n t g z).trans (by gcongr)
 apply le_trans (mul_le_mul (saltB G p a x (H-20) le_rfl) he (norm_nonneg _) (by unfold τ; positivity));
 let L:=(2*τ); rw [show _*_*(r^n*Real.exp _)= r^n*(L *(Real.exp (-‖p‖*(H-20))*Real.exp (H/2*‖p‖))) from ?_]; rw [←Real.exp_add]; gcongr; nlinarith only [mul_le_mul_of_nonneg_right v.le (norm_nonneg p),norm_nonneg p]; -- tune
 unfold L; ring
#print axioms remotePt
-- Black rank fee. offsets at physical both. constants independent of α.
lemma kaon_fee (v : EdgeM):∃ n:ℕ,∀ p:Space3, ‖kaon v (pulseG G p)‖ ≤ 2^n*‖p‖^n:=by
 let a:=v.1.1; let b:=v.1.2.1; let c:=v.1.2.2; let d:ℕ:= if v.2 then 1 else 0; let n:=a+b+c+d; refine ⟨n,fun p=> ?_⟩; obtain ⟨⟨w,l,k⟩,r⟩:=v; let x:= 2*‖p‖; unfold kaon; simp only [norm_mul,norm_pow]; rw [←mul_pow]; change ‖(pulseG G p) 0‖^a * _ * _ * ‖(pulseG G p) 3‖^d ≤ x^n; unfold n; simp only [pow_add]; apply mul_le_mul (mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (pulse_pay ..) _) (pow_le_pow_left₀ (norm_nonneg _) (pulse_pay ..) _) (by positivity) (by positivity)) (pow_le_pow_left₀ (norm_nonneg _) (pulse_pay ..) _) (by positivity) (by positivity)) (pow_le_pow_left₀ (norm_nonneg _) (pulse_pay ..) _) (by positivity) (by positivity) -- tune h
lemma kaon_I(a:Axis)(x:E4)(u:20<depthG G x)(v:EdgeM): Integrable (fun p:Space3=>salt G p x a*kaon v (pulseG G p)):=by
 obtain ⟨k,T⟩:= kaon_fee G v; let b:=depthG G x-20; apply Integrable.mono' ((exp3_poly b (sub_pos.mpr u) k).const_mul (2^k*(2*τ))) ?_ ?_
 · apply Measurable.aestronglyMeasurable; apply Measurable.mul (salt_m G x a); exact (show Continuous (fun p:Space3=>kaon v (pulseG G p)) from by unfold kaon; fun_prop).measurable
 filter_upwards with p; rw [norm_mul]; refine (mul_le_mul (saltB G p a x b le_rfl) (T p) (norm_nonneg _) (by unfold τ; positivity)).trans_eq ?_; ring_nf
-- rank factor scalar weights same coin v for ALL components.
def arcX(n:ℕ)(x:E4)(v:EdgeM):ℂ:= (crown_say x n).choose v
def marine(x:E4):ℙ:= (ocean_f x).choose
def homex(x:E4)(a:Axis)(v:EdgeM):= ∫ p:Space3,salt (marine x) p x a*kaon v (pulseG (marine x) p)
abbrev roverC:ℝ:= 2*τ* (∫ p:Space3,Real.exp (-1*‖p‖))
lemma horizonPt (x:E4)(a:Axis) {r:ℝ}(u:0<r)(t:r≤1)(Z:100<‖x‖)(U:32*‖y‖≤ r *‖x‖): ‖sax a (x+y)-∑ i∈coon n,(arcX n y i)*homex x a i‖≤ roverC*r^n:=by
 let G':= marine x; have he: depthG G' x=‖x‖:= (ocean_f x).choose_spec; have hv:20<depthG G' (x+y):=by
    have hg: depthG G' (x+y)=depthG G' x + depthG G' y:= inner_add_right ..; rw [hg,he]; have ht: -‖y‖ ≤ depthG G' y:= (abs_le.mp ((abs_real_inner_le_norm ..).trans_eq (by rw [sail_size,one_mul]))).1; nlinarith only [Z,U,ht,mul_le_mul_of_nonneg_right t (norm_nonneg x)]
 let W:=arcX n y; let H(i:EdgeM)(p:Space3):= salt G' p x a * kaon i (pulseG G' p); have ht(i:EdgeM):Integrable (H i):=kaon_I G' a x (by rw [he]; linarith [Z]) i
 let U'(p:Space3):= ∑ i∈coon n,W i * H i p; have hu'(p:Space3): U' p=salt G' p x a*say n (murmur y (pulseG G' p)):=by have he:=(crown_say y n).choose_spec _ (choir G' p); dsimp only at he; rw [he,Finset.mul_sum]; unfold U'; apply Finset.sum_congr rfl; intro i _; unfold W H arcX; ring -- prep
 have hp : ∑ i∈coon n,W i *homex x a i=∫ p,U' p:=by unfold U'; rw [integral_finsetSum _ (fun i _=>(ht i).const_mul _ )]; simp_rw [integral_const_mul]; rfl
 let u₀:20<depthG G' (x+y):=hv; change ‖_-∑ i∈coon n,W i*_‖≤_ ; rw [hp,serenade G' a (x+y) hv,← integral_sub (omega_int G' a (x+y) hv) (integrable_finsetSum _ (fun i _=>(ht i).const_mul _))]; apply le_trans (norm_integral_le_of_norm_le (g:=fun p:Space3=>r^n*(2*τ*Real.exp (-1*‖p‖))) (((exp3 1 (by norm_num)).const_mul _).const_mul _) ?_) (le_of_eq ?_) -- omega Real nope
 · filter_upwards with p; change ‖_- U' p‖≤_; rw [hu' p,rise_add,← mul_assoc,show flute G' _ _* rise (pulseG G' _) x= salt G' _ x _ from rfl, ← mul_sub]; exact remotePt G' p y n x a u t (he.symm ▸ Z) (he.symm ▸ U)
 rw [integral_const_mul,integral_const_mul]; unfold roverC; ring
-- matrix.Spin
abbrev spectx(v:EdgeM)(x:E4): Op SpinIdx:= ∑ i:Axis, (((gain⁻¹:ℝ):ℂ)*homex x i v) • drizzle i
def rover:ℝ:= ∑ i:Axis,(gain⁻¹ *roverC)*‖drizzle i‖
lemma rover_n : 0≤ rover:= Finset.sum_nonneg fun i _=> by have hv:= gain_h; have h:0≤ roverC:= mul_nonneg (mul_nonneg zero_le_two tau_pos.le) (integral_nonneg fun _=> (Real.exp_pos _).le); positivity
lemma roverPt(x:E4){r:ℝ}(u:0<r)(t:r≤1)(Z:100<‖x‖)(U:32*‖y‖≤ r*‖x‖): ‖spiral (x+y)-∑ i∈coon n,(arcX n y i) • spectx i x‖ ≤ rover*r^n:=by
 unfold spiral spectx rover; simp_rw [Finset.smul_sum,Finset.sum_mul]; rw [Finset.sum_comm (s:=coon n), ←Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=>?_ ; let q:=gain⁻¹; let z:ℂ:= q; have hv: ‖z‖=q:= Complex.norm_of_nonneg (inv_nonneg.mpr gain_h.le); let K(c:ℂ): Op SpinIdx:= z • (c • drizzle i); have hp: ∀ j:EdgeM, (arcX n y j • (z*homex x i j) • drizzle i)= K (arcX n y j*homex x i j):=by intro j; unfold K; simp_rw [smul_smul]; rw [mul_left_comm]
 let D:=drizzle i; change ‖_ - ∑ j∈_,arcX n y j • (z*homex x i j) • drizzle i‖≤_; simp_rw [hp]; unfold K; simp_rw [smul_smul]; rw [← Finset.sum_smul, ← Finset.mul_sum,←sub_smul,←mul_sub,norm_smul,norm_mul,hv]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (horizonPt y n x i u t Z U) (show 0≤q from inv_nonneg.mpr gain_h.le)) (norm_nonneg (drizzle i))).trans_eq (by unfold q; ring)
#print axioms horizonPt
end YM.CF.Window.ArchiveK
