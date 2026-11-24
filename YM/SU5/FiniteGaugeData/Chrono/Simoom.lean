import YM.SU5.FiniteGaugeData.Chrono.Palmetto
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Chrono
open Nacre Heat Charm
variable (K:Calibration) (a: Axis)(z kT:ℤ)
abbrev helve (K:Calibration) (a:Axis)(x y:W K):= fire K a 0 x*y
abbrev dialL (K:Calibration) (a:Axis)(x:W K)(z:ℕ):= helve K a (clockW K a z x) (clockW K a z x)
variable (x y:W K)
lemma helve_slide : clockW K a z (helve K a x y)=helve K a (clockW K a (-z) x) (clockW K a z y):=by simp only [helve, clock_neg, neg_neg,clock_mul]
lemma helve_neg (z:ℤ) : clockW K a (-z) (helve K a x y)=helve K a (clockW K a z x) (clockW K a (-z) y):= by simp only [helve, clock_neg,clock_mul]
lemma helve_plus (s:ℤ) (H:kT+z=s) : helve K a x (clockW K a s y)= clockW K a z (helve K a (clockW K a z x) (clockW K a kT y)):= by rw [helve_slide,clock_add,clock_add,neg_add_cancel, tic_zero,add_comm z kT,H]
lemma helve_conv (s:ℕ):
  helve K a (clockW K a s x-clockW K a ↑(s+2) x) (clockW K a s x-clockW K a ↑(s+2) x)= dialL K a x s+dialL K a x (s+2)-(clockW K a 1 (dialL K a x (s+1)) + clockW K a (-1) (dialL K a x (s+1))):= by
 let f(u:ℕ):= clockW K a (u:ℕ) x
 let T:= fire K a 0
 have h (x y: W K): T (x-y)= T x-T y:= by unfold T; nth_rw 1 [sub_eq_add_neg]; rw [ice_more, ← neg_one_smul (R:=ℂ) y,ice_paid,star_neg,star_one,neg_one_smul,sub_eq_add_neg] -- tune lemma R:=ℂ
 change T (f s - f (s+2)) * _= _
 unfold dialL; rw [helve_slide,helve_slide,neg_neg]; simp_rw [clock_add]
 rw [show (-1:ℤ)+↑(s+1)=(s:ℤ) from by omega, show (1:ℤ)+↑(s+1)=↑(s+2) from by omega,h,mul_sub,_root_.sub_mul,_root_.sub_mul]; dsimp only [f,T,helve]; abel
variable {K}
lemma helve_loc {x y:W K}{S T:Finset Cover}(q:Locator K x S)(h:Locator K y T) : Locator K (helve K a x y) (refract a 0 S∪T):= locate_join _ _ (locate_sub _ (locate_cold K _ a 0 q) subset_union_left) (locate_sub _ h subset_union_right)
lemma emir_bound (x:W K)(S:Finset Cover)(q:Locator K x S)(m:Side)(n:ℕ) (v:Fields (K.c m)): ‖(dialL K a x n).val m v‖≤ (duration S * ‖reading K S x q‖)^2:= by
 let R:= fire K a (gaugeShift K.B n) (fire K a 0 x)
 let C:= duration S * ‖reading K S x q‖
 have ht(v:Fields (K.c m)):‖x.val m v‖ ≤ C:= (congrArg (fun t:Family K=>‖t m v‖) (reading_p K S x q)).symm.le.trans (compose_price ..)
 have h(z:ℤ)(x:W K)(v:Fields (K.c m)): ‖(fire K a z x).val m v‖=‖x.val m (reflFields a z v)‖:= theta_fee ..
 refine (norm_mul_le ((fire K a 0 R).val m v) (R.val m v)).trans ?_; rw [h, sq]; unfold R; simp_rw [h]; apply mul_le_mul (ht _) (ht _) (norm_nonneg _) ((norm_nonneg _).trans (ht v))
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
set_option maxHeartbeats 360000
-- the course logarithm/convexity budget from `palmetto`
local notation "μ"=> momentm Y i s
local notation "Ω"=> hours S Kₜ (momentm Y i s)
variable (x:W (tent Y h)) -- extra K stale
variable (f:Ferry Y s i k) -- k reused :ℕ
private abbrev takeY := collector Y h i k f.depth s
-- linear in W K_t
private def heatClock : W (tent Y h) →ₗ[ℂ] ℂ where
 toFun x:= collector Y h i k f.depth s (x.val (momentm Y i s))
 map_add' x y := (boxprice Y h i k f.depth s f.fire f.enters).sum _ _ ((well_for Kₜ x).1.paid.choose_spec.support _).env ((well_for Kₜ y).1.paid.choose_spec.support _).env
 map_smul' _ _:= (boxprice Y h i k f.depth s f.fire f.enters).mult ..

local notation "Γ"=> heatClock Y h s i k f
variable (q:Locator (tent Y h) x S) (p:Ahead a 0 (reserve Λ l) S)
-- indicate name Fin
abbrev ember (n:ℕ) : ℂ := (heatClock Y h s i k f) (dialL (tent Y h) a x n)
include p q
private lemma color_sum (b:wall S+ (tent Y h).ℓ ≤ ((tent Y h).c (momentm Y i s)).val) {n:ℕ}(u:n≤hours S (tent Y h) (momentm Y i s)):AtSupport false (band ((Kₜ).c (momentm Y i s)) a 0 (tent Y h).ℓ) ((clockW Kₜ a n x).val μ):= ((loc_tic Kₜ S a n q)|>.support _).mono (hours_band S Kₜ μ a b u p) -- K_t.c syntax better parenthesize
local notation "η"=> reserve Λ l
local notation "N"=> ((tent Y h).c (momentm Y i s))
local notation "A"=> AtSupport false (band ((tent Y h).c (momentm Y i s)) a 0 (reserve Λ l))
omit p q
private lemma sum_ge (x:W (tent Y h))(p:A (x.val (momentm Y i s))): 0 ≤ (heatClock Y h s i k f) (helve Kₜ a x x):=by
 have he: gaugeShift (Kₜ).B 0=0:=by unfold gaugeShift; rw [mul_zero]
 have hx: AtSupport false (band (N) a (gaugeShift (Kₜ).B 0) η) (x.val μ):= he.symm ▸ p
 change 0 ≤ takeY Y h s i k f _; unfold takeY; have ht:=(boxprice Y h i k f.depth s f.fire f.enters).fund a 0 _ hx; rw [he] at ht; exact ht
include q p
local notation "O" n:max=> ember a Y h s i k x f n -- order inspect
lemma convex_step (b:wall S+η≤(N).val) {n:ℕ}(u:n+2≤hours S Kₜ μ): (O (n+1)).re+(O (n+1)).re ≤ (O n).re+(O (n+2)).re:= by
 have he(n:ℕ)(t:n≤hours S Kₜ μ): A ((clockW Kₜ a n x).val μ):= color_sum a Y h S s i x q p b t
 let y:= clockW Kₜ a n x; let z:= clockW Kₜ a (n+2:ℕ) x
 have hz:A ((y-z).val μ):= by rw [sub_eq_add_neg,←neg_one_smul (R:=ℂ) z]; exact (he n (by omega)).addM ((he _ u).smulM (-1))
 have ht:= sum_ge a Y h s i k f _ hz; unfold y z at ht; rw [helve_conv,map_sub,map_add,map_add,show heatClock Y h s i k f (clockW Kₜ a 1 _) = _ from collector_tick Y h s i k a 1 f (dialL Kₜ a x (n+1)),show heatClock Y h s i k f (clockW Kₜ a (-1) _) = _ from collector_tick Y h s i k a (-1) f (dialL Kₜ a x (n+1))] at ht
 exact sub_nonneg.mp (show 0 ≤ (O n).re+ (O (n+2)).re - ((O (n+1)).re+(O (n+1)).re) from (Complex.le_def.mp ht).1)
lemma ember_nn (b:wall S+η≤(N).val){n:ℕ}(u:n≤hours S Kₜ μ): 0 ≤ (O n).re:= (Complex.le_def.mp (sum_ge a Y h s i k f _ (color_sum a Y h S s i x q p b u))).1
-- a PERIOD-VARYING room exactly 
abbrev cargoC := Real.exp (duetCharge Y s * ((2*(2*(fareWidth S Kₜ)+addgap Kₜ):ℕ):ℝ)^4) *(duration S * ‖reading Kₜ S x q‖)^2
-- `p` in type? drop
lemma career (b:wall S+η ≤ (N).val)(d:2*fareWidth S Kₜ+addgap Kₜ≤ (N).val) : ‖O Ω‖≤ cargoC Y h S s x q:= by
 let P:= boxprice Y h i k f.depth s f.fire f.enters
 let T:= loc_tic Kₜ S a Ω q
 let Z:= duration S * ‖reading Kₜ S x q‖
 have he: cash (deltaL Y h i s) ((dialL Kₜ a x Ω).val μ)≤ (Z:ℝ)^2:=by
    unfold cash; refine (integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _)) (integrable_const («μ»:=city _) (Z^2)) (Eventually.of_forall (fun x' => emir_bound a x S q μ _ _))).trans_eq ?_; simp
 refine (P.homestead (cost_tic S Kₜ μ a b) d ((helve_loc a T T : Locator Kₜ (dialL Kₜ a x Ω) _).support μ)).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
lemma slope (b:wall S+η≤ (N).val) {n:ℕ}(r:n≤hours S Kₜ μ) : (n:ℝ)*((O 1).re-(O 0).re)≤(O n).re:=by
 have he(n:ℕ)(t:n+1≤hours S Kₜ μ): (O 1).re - (O 0).re ≤ (O (n+1)).re - (O n).re:= by
    induction n with
    | zero=> rfl
    | succ n ih=> have h:= ih (by omega); have v:=convex_step a Y _ S s i k x f q p b t; linarith
 induction n with
 | zero=> rw [Nat.cast_zero,zero_mul]; exact ember_nn a Y h S s i k x f q p b r
 | succ n ih=> have h:= ih (by omega); have t:= he n r; rw [Nat.cast_succ]; linarith
#print axioms career
omit q p
-- UV then IR, inequality linear paid at endpoint before passing UV.
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable (R:Universal Y h u v I E)
include R p q
lemma fixed_slope (b:wall S+η≤ (N).val)(d:2*fareWidth S Kₜ+addgap Kₜ≤ (N).val) : (Ω:ℝ) * ((I s (dialL Kₜ a x 1).val i).re - (I s (dialL Kₜ a x 0).val i).re) ≤ cargoC Y h S s x q:=by
 let F(n:ℕ):= dialL Kₜ a x n|>.val
 have he(n:ℕ): Tendsto (fun k=> (hot Y h s i (v k) (F n)).re) atTop (𝓝 ((I s (F n) i).re)):=by rw [← internal_eq Y h s i R (F n) (well_for Kₜ (dialL Kₜ a x n)).1]; exact Complex.continuous_re.continuousAt.tendsto.comp ((R.pick.booked Y h s (well_for Kₜ (dialL Kₜ a x n)).1).1.inner i)
 apply le_of_tendsto (Filter.Tendsto.const_mul (Ω:ℝ) (Filter.Tendsto.sub (he 1) (he 0))); filter_upwards [R.pick.pass Y h s i] with k f
 change _*( (hot Y h s i (v k) (F 1)).re - (hot Y h s i (v k) (F 0)).re) ≤ _; unfold hot; rw [dif_pos f.depth,dif_pos f.depth]
 apply le_trans (slope a Y h S s i (v k) x f q p b (show Ω ≤ Ω from le_rfl))
 exact (Complex.re_le_norm _).trans (career a Y h S s i (v k) x f q p b d)
theorem contraction  : (E s (helve Kₜ a (clockW Kₜ a 1 x) (clockW Kₜ a 1 x)).val).re ≤ (E s (helve Kₜ a x x).val).re := by
 let F(n:ℕ):= dialL Kₜ a x n|>.val
 suffices V:(E s (F 1)).re-(E s (F 0)).re≤0 by
    dsimp only [F,dialL] at V; rw [Nat.cast_zero,Nat.cast_one,tic_zero] at V; exact sub_nonpos.mp V
 by_contra! hx
 let t:=(E s (F 1)).re-(E s (F 0)).re
 let Q:= cargoC Y h S s x q
 let X(i:ℕ):=hours S Kₜ (momentm Y (u i) s)
 let G(n i:ℕ):=(I s (F n) (u i)).re
 have hX:Tendsto (fun i=>(X i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp ((hours_grow S Kₜ).comp ((momentum Y s).comp R.pick.grow_i.tendsto_atTop))
 have he(n): Tendsto (G n) atTop (𝓝 ((E s (F n)).re)):= Complex.continuous_re.continuousAt.tendsto.comp ((R.together s _ (well_for Kₜ (dialL Kₜ a x n)).1).periods)
 have hz:0<t/2:= by change 0<t at hx; positivity
 obtain ⟨m,c,v,d⟩:= ((((momentum Y s).comp R.pick.grow_i.tendsto_atTop).eventually (antipodes S Kₜ)).and (((Filter.Tendsto.sub (he 1) (he 0)).eventually (Ioi_mem_nhds (show t/2<t from by linarith))).and (hX.eventually (eventually_gt_atTop (Q/(t/2)))))).exists
 have ht:Q<(X m:ℝ)*(t/2):= (div_lt_iff₀ hz).mp d; change t/2<G 1 m-G 0 m at v
 exact not_lt_of_ge (fixed_slope a Y h S s (u m) x q p R c.1 c.2) (show Q< _ from lt_of_lt_of_le ht (mul_le_mul_of_nonneg_left (v.le) (Nat.cast_nonneg' (X m)))) -- tune
#print axioms contraction
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
