import ForceSatin.Aureole
import YM.SU5.Circuit.Regale
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
local notation "π" => Real.pi
open YM.Stationary (Gaia exileE cartWeight cart_weight_pos orbit_at)
open MeasureTheory
open scoped SchwartzMap FourierTransform
open Complex (ofReal)

-- rapid price
lemma tribune (y:ℝ)(u:0<y)(p:ℕ):∃ C:ℝ,0<C ∧ ∀ x:ℝ,0≤x→(1+x)^p * Real.exp (-y*x^2) ≤ C :=by
 let f(x:ℝ):=Real.exp (-y*x^2); obtain ⟨s,H⟩:= (eventually_atTop.1 ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).eventually (gt_mem_nhds one_pos)))
 let U:= max s (max 1 y⁻¹); have hu:1≤ U:=le_max_of_le_right (le_max_left ..)
 let W(x:ℝ):=(1+x)^p * f x
 have he:Continuous W:=by unfold W f; fun_prop
 obtain ⟨r,g⟩:= (isCompact_Icc (a:=(0:ℝ)) (b:=U)).bddAbove_image he.continuousOn
 refine ⟨max r (2^p),lt_max_of_lt_right (by positivity),fun x h=>?_⟩
 rcases le_total x U with hx|hx; · exact (g ⟨_,show x∈ Set.Icc 0 U from ⟨h,hx⟩,rfl⟩).trans (le_max_left ..)
 apply le_trans _ (le_max_right ..); have hy:x≤y*x^2:=by have he:= ((inv_le_iff_one_le_mul₀ u).mp ((le_max_of_le_right (le_max_right ..)).trans hx)); nlinarith only [he,mul_le_mul_of_nonneg_left he h]
 calc
   _≤(2*x)^p*Real.exp (-x):=by gcongr; all_goals linarith
   _≤_:=by rw [mul_pow,mul_assoc]; exact mul_le_of_le_one_right (by positivity) (H x ((le_max_left ..).trans hx)).le

lemma velvetSch : ∃ G:𝓢(Gaia,ℝ), (G:Gaia→ℝ)=tog 1:=by
 let f(x:Gaia):ℝ:= -(‖x‖^2); have hf: HasTemperateGrowth f:= Function.HasTemperateGrowth.neg (Function.hasTemperateGrowth_norm_sq Gaia) -- tune
 have he: tog 1= Real.exp ∘ f:=funext fun i=>(by simp [tog,f]); refine ⟨⟨tog 1,he ▸ Real.contDiff_exp.comp hf.1, fun k n =>?_⟩,rfl⟩
 obtain ⟨d,C,hc,h⟩:= hf.norm_iteratedFDeriv_le_uniform n; obtain ⟨W,t,w⟩:= tribune 1 one_pos (k+d*n); let A(x:Gaia):=1+‖x‖; refine ⟨n.factorial*(1+C)^n*W,fun x=>?_⟩
 have hu:0<tog 1 x:=Real.exp_pos _; let V:= (1+C)*A x^d; have hv:1≤V:= one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by unfold A; simp))
 have hh: ‖iteratedFDeriv ℝ n (tog 1) x‖≤ n.factorial*tog 1 x * V^n:= by
    rw [he]; apply norm_iteratedFDeriv_comp_le Real.contDiff_exp hf.1 (by exact_mod_cast le_top) x
    · intro i h; rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp,Real.norm_of_nonneg (Real.exp_nonneg _)]; rfl -- tune
    intro i p t; exact (h i t x).trans ((show C*(1+‖x‖)^d≤ V by unfold V A; gcongr; simp).trans (le_self_pow₀ hv (by omega)))
 apply (mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (show ‖x‖≤ 1+‖x‖ by linarith) _) hh (norm_nonneg _) (by positivity)).trans; refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left (w ‖x‖ (norm_nonneg _)) (show 0 ≤ (n.factorial:ℝ)*(1+C)^n by positivity)); unfold tog V A; rw [pow_add,pow_mul,mul_pow]; ring
-- inverse lift away from 0 via collateral monotone true sizes
lemma Assets {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→ℝ}(h:HasTemperateGrowth f){η:ℝ}(hp:0<η)(v:∀ x,η<f x): HasTemperateGrowth fun x=> (f x)⁻¹:=by
 let I:= Set.Ioi η
 have hV(x:ℝ)(u:x∈I):ContDiffAt ℝ ∞ (Inv.inv (α:=ℝ)) x:= contDiffAt_id.inv (show x≠0 from (hp.trans u).ne'); -- tune syntax
 apply HasTemperateGrowth.comp' (t:=I) (g:=(Inv.inv (α:=ℝ))) (f:=f) (Set.range_subset_iff.mpr v) isOpen_Ioi.uniqueDiffOn (fun x hx=>(hV x hx).contDiffWithinAt) _ h
 intro n; let T(i:ℕ):= (i.factorial:ℝ)*(η^(-1-i:ℤ))
 refine ⟨0,∑ i∈range (n+1),T i, Finset.sum_nonneg fun i _=> by unfold T; positivity, fun i l x u=>?_⟩
 have he:η < x:=u; have h0:=hp.trans he
 rw [pow_zero,mul_one,iteratedFDerivWithin_of_isOpen _ isOpen_Ioi u,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,iter_deriv_inv,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Real.norm_natCast, Real.norm_of_nonneg (show 0≤ x^(-1-i:ℤ) by positivity)]
 apply le_trans _ (single_le_sum (f:=T) (fun i _=>by unfold T; positivity) (mem_range.mpr (Nat.lt_succ_of_le l))); unfold T; gcongr <;> first| positivity | (rw [show (-1-(i:ℤ))= -(↑(1+i):ℤ) from (by omega),zpow_neg,zpow_neg,zpow_natCast,zpow_natCast]; gcongr)

abbrev gloom: Gaia ≃L[ℝ] Bin := PiLp.continuousLinearEquiv 2 ℝ _ -- tune
abbrev glad(x:Gaia):= tmap (gloom x)
lemma glacial(x:Gaia): Fain (glad x)= (‖x‖:ℂ)^2:=by rw [Fain,prodM_self _ (tmap_physical _),←Complex.ofReal_pow, ←Stationary.geode_sum]; rfl
lemma gathering(x:Gaia): Vaunt (glad x)= (tog 1 x:ℂ):=by unfold Vaunt; rw [glacial]; simp [tog]
def springerse(p:Gaia):= ‖p‖^2+ puff (gloom p)
abbrev blazing(x:Gaia):= fog (gloom x)
lemma kernel_piece :HasTemperateGrowth (fun p:Gaia=> (1-blazing p)* (‖p‖^2)⁻¹):=by
 have he:HasTemperateGrowth blazing:= (fog.hasCompactSupport.hasTemperateGrowth fog_c).comp gloom.hasTemperateGrowth
 have hg: HasTemperateGrowth springerse:= (Function.hasTemperateGrowth_norm_sq Gaia).add ((puff.hasCompactSupport.hasTemperateGrowth puff.contDiff).comp gloom.hasTemperateGrowth)
 let V:=min ((π/64)^2/2) (1/2); have hm:=Real.pi_pos; have ht:0<V:=lt_min (by positivity) one_half_pos
 have hx(x:Gaia): ‖gloom x‖≤‖x‖:= orbit_at (gloom x)
 have hf: HasTemperateGrowth fun x:Gaia=> (springerse x)⁻¹:= Assets hg ht fun x=> by
    by_cases e:‖gloom x‖≤ π/64
    · unfold springerse; rw [puff.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr e)]; exact (min_le_right ..).trans_lt (by linarith [sq_nonneg ‖x‖])
    have hh: π/64<‖x‖:=lt_of_lt_of_le (lt_of_not_ge e) (hx x); unfold springerse; apply lt_of_le_of_lt (min_le_left ..); exact lt_of_lt_of_le (by nlinarith) (le_add_of_nonneg_right (b:=_) puff.nonneg)
 convert (show HasTemperateGrowth fun p:Gaia=> (1-blazing p)*(springerse p)⁻¹ from ((HasTemperateGrowth.const (1:ℝ)).sub he).mul hf) using 1
 ext p; by_cases e:‖gloom p‖≤π/4
 · simp [blazing, fog_s _ e]
 have hx: π/32≤‖gloom p‖ := by linarith
 unfold springerse; rw [puff.zero_of_le_dist (show _ from dist_zero_right (gloom p) ▸ hx)]; simp

lemma vRock (F: Gaia→ℂ)(p: HasTemperateGrowth F) : ∃ f:𝓢(Gaia,ℂ), ⇑f= fun x=> (1-(blazing x:ℂ))*F x *(pet 1 x:ℂ):=by
 let V(p:Gaia):= (1-blazing p)*(‖p‖^2)⁻¹; obtain ⟨f,h⟩:= velvetSch; refine ⟨SchwartzMap.smulLeftCLM _ F (SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.smulLeftCLM ℝ V f)),?_⟩ -- tune E explicit arg
 funext x; rw [SchwartzMap.smulLeftCLM_apply_apply p,SchwartzMap.postcompCLM_apply,SchwartzMap.smulLeftCLM_apply_apply kernel_piece, show f x= _ from congr_fun h x]; change F x*(↑(V x*tog 1 x):ℂ)=_; unfold V pet; push_cast; ring
#print axioms Assets
-- Rapid error observable grows.Aperiod or E union
structure Swift(f : Gaia→ℂ) : Prop where
 fast (k:ℕ):∃ K:ℝ,0≤K∧∀ i:Gaia,1 ≤ ‖i‖ → ‖i‖^k * ‖f i‖ ≤ K
namespace Swift
variable {f g:Gaia→ℂ}(h:Swift f)
include h
lemma plus(k:Swift g):Swift (f+g):=by
 constructor; intro n; obtain ⟨C,c,p⟩:= h.fast n; obtain ⟨A,a,v⟩:= k.fast n; refine ⟨C+A,by positivity,fun i t=>?_⟩; change _ *‖f i+g i‖ ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)); rw [mul_add]; exact add_le_add (p i t) (v i t)
lemma cons(w:ℂ): Swift (w • f):=by
 constructor; intro k; obtain ⟨C,c,p⟩:= h.fast k; refine ⟨‖w‖*C, by positivity,fun i t=>?_⟩; rw [Pi.smul_apply,norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (p i t) (norm_nonneg _)
lemma neg : Swift (-f):=by have he:= cons h (-1); simpa using he
lemma sub(k:Swift g):Swift (f-g):=by simpa [sub_eq_add_neg] using h.plus k.neg
omit h in
lemma zero : Swift 0:=by constructor; intro k; exact ⟨0,le_rfl,fun i _=>by simp⟩
end Swift

def gorge (F: Gaia→ℂ) (x:Gaia):= (cartWeight:ℂ)* ∫ p, burn x p*F p
lemma ghoul(f:𝓢(Gaia,ℂ)): Swift (gorge f):=by
 let F:𝓢(Gaia,ℂ):= 𝓕⁻ f
 have hp:=Real.pi_pos; let z:= 2*Real.pi; have hz:0<z:= by unfold z; positivity
 have he(x:Gaia):gorge f x=(cartWeight:ℂ)*F (z⁻¹ • x):=by
    unfold gorge F; congr 1; rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']; apply integral_congr_ae; filter_upwards with i; unfold burn; congr 1; rw [real_inner_smul_right,real_inner_comm i,←mul_assoc,show 2*π*z⁻¹ =1 from mul_inv_cancel₀ hz.ne',one_mul,mul_comm Complex.I]
 constructor; intro n; use (cartWeight*z^n * SchwartzMap.seminorm ℝ n 0 F)
 apply And.intro
 · have hv:=cart_weight_pos; have he:0≤SchwartzMap.seminorm ℝ n 0 F:= (apply_nonneg (SchwartzMap.seminorm ℝ n 0) F); positivity
 intro i w
 rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg cart_weight_pos.le]
 let j:= z⁻¹ • i; have ht:‖i‖=z*‖j‖:=by unfold j; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz.le)]; field_simp
 rw [ht,mul_pow]; change _* (cartWeight * ‖F j‖)≤_; rw [show z^n* _*_ = cartWeight*z^n*(‖j‖^n*‖F j‖) by ring]; exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_pow_mul_le_seminorm ℝ F n j) (mul_nonneg cart_weight_pos.le (pow_nonneg hz.le _))
#print axioms kernel_piece
#print axioms ghoul
end YM.Regis.Circuit.SpringDay
