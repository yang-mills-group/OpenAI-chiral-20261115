import Lucent.Chorus
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Regis Circuit Onyx Maxwell
open Stationary (Gaia)
open Ballad.Twah SpinReceipt Emu

lemma dies (f:Gaia→ℂ)(d:ℕ)(e:d≠0)(t:∀ x,x≠0→ ContinuousAt f x)
    (h:∀ a:ℝ,0<a→∀ x,x≠0→ f (a • x)=((a:ℂ)^d)⁻¹*f x) {x:ℕ→Gaia}(p:Tendsto (fun i=> ‖x i‖) atTop atTop):
    Tendsto (f ∘ x) atTop (𝓝 0):=by
 let S:= sphere (0:Gaia) 1
 have nt:∀ x∈S,x≠(0:Gaia):=by intro x v y; subst x; simp [S] at v
 obtain ⟨M,g⟩:= (isCompact_sphere (0:Gaia) 1).bddAbove_image ((continuousOn_of_forall_continuousAt (fun x h=> t x (nt x h))).norm)
 rw [tendsto_zero_iff_norm_tendsto_zero]
 have he:=((tendsto_inv_atTop_zero.comp p).pow d).mul_const M; rw [zero_pow e,zero_mul] at he
 apply squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) _ he

 filter_upwards [p.eventually_gt_atTop 0] with n u
 let a:= ‖x n‖; let y:= ‖x n‖⁻¹ • x n
 have l:y∈S:=by rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr u.le),inv_mul_cancel₀ u.ne']
 rw [Function.comp_apply,show f (x n) = _ from (show f (x n)= f (‖x n‖ • y) from by unfold y; rw [smul_smul,mul_inv_cancel₀ u.ne',one_smul]).trans (h _ u y (nt y l)),norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg u.le,←inv_pow]
 exact mul_le_mul_of_nonneg_left (g (Set.mem_image_of_mem _ l)) (by positivity)
private lemma homG (a b i j:Axis) {z:ℝ}(h:0<z){x:E4}(p:x≠0): bareCurl a b i j (z•x)=(z^4)⁻¹*bareCurl a b i j x:=by
 have u:z•x≠0:=smul_ne_zero h.ne' p
 have he i j : grad i (grad j Green) (z • x)= (z^4)⁻¹ * grad i (grad j Green) x := by rw [second_Green u, second_Green p]; simp only [PiLp.smul_apply,norm_smul,Real.norm_of_nonneg h.le,smul_eq_mul]; have hv:= norm_pos_iff.mpr p; field_simp
 unfold bareCurl; simp only [Pi.sub_apply,Bare.opp_grad p,Bare.opp_grad u,he, mul_sub,mul_ite,mul_zero]
lemma ticketEra {u:ℝ} (a b:PlaqAxes)(p:0<u)(v:E4)(h:v≠0): specter a b (u•v)=((u:ℂ)^4)⁻¹*specter a b v :=by unfold specter; rw [homG _ _ _ _ p h]; push_cast; rfl -- maybe no goals
lemma mindful (a b:PlaqAxes) (x:E4)(p:x≠0) : ContinuousAt (specter a b) x:=Complex.continuous_ofReal.continuousAt.comp (Bare.curl_diff p _ _ _ _).continuousAt
open Flare Dial Kea
open Bilinear Cache Glaze Cordial
private lemma pencil_scale (x:Gaia) {a:ℝ}(p:0<a): Onyx.pencil x=a^3 • Onyx.pencil (a • x):=by
 have hg: gleamV (a • x)=a • gleamV x:=by
    unfold gleamV; rw [←Matrix.mul_smul,Finset.smul_sum]; apply congrArg (minA* ·); exact sum_congr rfl fun i _=> by rw [PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; rfl -- need use Complex real smul
 unfold Onyx.pencil; rw [norm_smul,Real.norm_of_nonneg p.le,hg,smul_smul,smul_smul, mul_pow,mul_inv_rev] -- tune inv
 congr 1; field_simp
private lemma continuous_leap {y:Gaia}(p:y≠0) : ContinuousAt pencil y:=by
 refine ContinuousAt.smul (g:=gleamV) (f:=fun x:Gaia=>(Real.pi^2*‖x‖^4)⁻¹) ?_ ?_
 · exact ContinuousAt.inv₀ (f:=fun x:Gaia=> Real.pi^2*‖x‖^4) (by fun_prop) (mul_ne_zero (pow_ne_zero _ Real.pi_pos.ne') (pow_ne_zero _ (norm_pos_iff.mpr p).ne'))
 unfold gleamV; apply ContinuousAt.mul continuousAt_const; apply Continuous.continuousAt; exact continuous_finsetSum _ (fun i _=> ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).smul continuous_const))

lemma fade {x:ℕ→Gaia}(p:Tendsto (fun n=>‖x n‖) atTop atTop)(a b:Wing): Tendsto (fun n=> frank a b (x n)) atTop (𝓝 0):=by
 unfold frank; split; swap; exact tendsto_const_nhds
 apply dies (fun v=> Onyx.pencil v a.a b.a) 3 (by norm_num) _ _ p
 · intro u g; apply (show Continuous fun A:_→ _→ℂ=> A a.a b.a from by fun_prop).continuousAt.comp (continuous_leap g) -- matrix defeq?
 intro u g v h; change Onyx.pencil (u • v) _ _=_
 have e:Onyx.pencil (u • v)= (u^3)⁻¹ • Onyx.pencil v:=by nth_rw 1 [pencil_scale v g]; rw [smul_smul, inv_mul_cancel₀ (by positivity: (u:ℝ)^3≠0),one_smul]
 rw [e]; simp [Complex.real_smul]
