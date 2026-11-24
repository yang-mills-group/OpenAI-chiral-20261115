import YM.SU5.SatinWard.Resolution.IndexMag
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern.IndexMag
open YM YM.Lattice YM.CF.Fir YM.CF YM.CF.Jill Silk YM.Laurent Filter Topology MeasureTheory NormedSpace
open YM.Stationary
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Classical Topology _root_.Pointwise
open GaussianFourier
local notation "η"=> boundsEarth
local notation "pi!"=> Real.pi
local notation "Φ"=> exileE
variable {j:ℕ}{r:Male→Streams}(L:Looming j r)(H:1≤j)(M:Male)
local notation "Q"=> r M
local notation "V"=> reserveJ (r:=r) M
local notation "ψ"=> dimples (j:=j) M
abbrev nres(n:ℕ)(x:ℂ):ℂ:= ((1+x)/2)^n
abbrev winSize(n:ℕ):= Real.sqrt (↑n:ℝ)
abbrev moveJ (n:ℕ)(x:Gaia):= (winSize n)⁻¹ • x
def toEarth(f:Streams)(n:ℕ):Gaia→ℂ:= fun x=> boundsEarth.indicator (fun p=> nres n (E (dial p) (f 0)) * balljac f p) (moveJ n x)
local notation "V₄"=>toEarth Q
abbrev Brim(v:ℝ):Gaia→ℝ:= fun x=> Real.exp (-v*‖x‖^2)
local notation "κ"=> (1/4:ℝ)
private lemma toward :Tendsto (fun n=>(winSize n)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
lemma sings(x:Gaia):Tendsto (fun n=> moveJ n x) atTop (𝓝 0):=by simpa only [zero_smul] using toward.smul_const x
lemma into_earth (x: Gaia): ∀ᶠ n in atTop,moveJ n x∈ boundsEarth:= ((sings x).norm.eventually (show ∀ᶠ x in 𝓝 (‖(0:Gaia)‖), x≤1 from ge_mem_nhds (by simp))).mono fun i p=> orbs p
lemma pulse_ω(x:Gaia)(n:ℕ): ‖moveJ n x‖^2=(n:ℝ)⁻¹*‖x‖^2:=by rw [moveJ,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow, inv_pow,Real.sq_sqrt (by positivity)]
lemma Jacobian (F:Streams):Continuous (balljac F):= (E_cont _).comp cast_dial
include L H
private lemma anatomy(x:Gaia): Tendsto (fun n:ℕ=> (n:ℝ)* dimples (j:=j) M (moveJ n x)) atTop (𝓝 ((1/4:ℝ)*‖x‖^2)):=by
 obtain ⟨K,hP,E⟩:=dclose (j:=j) H; let T:=(1/4:ℝ)*‖x‖^2; rw [tendsto_iff_dist_tendsto_zero]; simp_rw [dist_eq_norm]; let H₁:= (((sings x).norm).const_mul (K*‖x‖^2)); rw [norm_zero,mul_zero] at H₁
 refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ?_ H₁
 filter_upwards [ eventually_gt_atTop 0,into_earth x] with n v h
 let i:= moveJ n x; have hn:0<(n:ℝ):=(by exact_mod_cast v); change ‖(n:ℝ)*(ψ i)-T‖ ≤ K*‖x‖^2*‖i‖; have hi:= E M i h; rw [show T=(n:ℝ)*((1/4:ℝ)*‖i‖^2) from ?_,← mul_sub,norm_mul, Real.norm_of_nonneg hn.le]; refine le_trans (mul_le_mul_of_nonneg_left hi hn.le) (le_of_eq ?_)
 · unfold i; rw [show ‖moveJ n x‖^3=‖moveJ n x‖^2*‖moveJ n x‖ from pow_succ ..,pulse_ω]; field_simp
 · unfold T i; rw [pulse_ω]; field_simp
lemma oracle_lim(x:Gaia): Tendsto (fun n=> toEarth (r M) n x) atTop (𝓝 (Brim κ x:ℂ)):=by
 let T:= fun n=> -(dimples (j:=j) M (moveJ n x)); let t:= -(1/4:ℝ)* ‖x‖^2; have hk:Tendsto (fun n:ℕ=> (n:ℝ) * T n) atTop (𝓝 t):=by simpa only [T,t,neg_mul,mul_neg,Pi.neg_apply] using (anatomy L H M x).neg
 let g:= Real.tendsto_one_add_pow_exp_of_tendsto hk; have he:Tendsto (fun n:ℕ=> nres n (reserveJ (r:=r) M (moveJ n x))) atTop (𝓝 ((Brim κ x:ℝ):ℂ)):=by
    refine (Complex.continuous_ofReal.continuousAt.tendsto.comp g).congr' ?_; filter_upwards [into_earth x] with i h; unfold nres; rw [signal_price L M h]; change _= _; simp only [Function.comp_apply]; unfold T; push_cast; ring -- pow variable
 have hf:Tendsto (fun n=>balljac (r M) (moveJ n x)) atTop (𝓝 1):=by
    have e:= (Jacobian (r M)).continuousAt (x:=0)|>.tendsto; rw [show balljac (r M) 0=1 from (by unfold balljac dial; rw [show Φ (0:Gaia)=(0:Bin) from rfl,rad_zero,L.j_origin H M])] at e; exact e.comp (sings x) -- trans'?
 have ht:=he.mul hf; rw [mul_one] at ht; exact ht.congr' ((into_earth x).mono fun i h=> (Set.indicator_of_mem h ..).symm)
#print axioms oracle_lim
private lemma manage_bound: ∃ C D:ℝ,0<C ∧ 0<D∧ ∀ n:ℕ,0<n→∀ x: Gaia, ‖V₄ n x‖≤ D * Brim C x :=by
 obtain ⟨C,u,p⟩:= lower_earth (j:=j) H; obtain ⟨D,h⟩:= isCompact_univ.exists_bound_of_continuousOn (E_cont (jac (r M))).continuousOn; have hd:0 < D:=(by have hu:= h 0 (Set.mem_univ _); rw [L.j_origin H M,norm_one] at hu; linarith); refine ⟨C,D,u,hd,fun n hn x=>?_⟩
 let z:= moveJ n x; let T:= 1- (ψ z); unfold toEarth; by_cases e:moveJ n x∈boundsEarth
 · rw [Set.indicator_of_mem e,norm_mul,show (E (dial _) ((r M) 0))= _ from signal_price L M e]
   have ht: nres n (↑(1-2*ψ z):ℂ)=( (↑(T^n):ℂ) ):=by unfold nres T; push_cast; ring
   have hw:0≤ T:=sub_nonneg.mpr (dsmile L M e); have w:(T)^n ≤ Brim C x := by
      have hr:T≤ Real.exp (-C*‖z‖^2):=by unfold T; linarith only [p M z e,Real.add_one_le_exp (-C*‖z‖^2)] -- unfold
      refine (pow_le_pow_left₀ hw hr _).trans_eq ?_; have hN: (n:ℝ) ≠0:= by exact_mod_cast ne_of_gt hn -- fix
      rw [← Real.exp_nat_mul]; unfold Brim; congr 1; unfold z; rw [pulse_ω]; field_simp
   rw [ht,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hw _)]; exact (mul_le_mul w (h _ (Set.mem_univ (dial z))) (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_comm ..)
 rw [Set.indicator_of_notMem e,norm_zero]; unfold Brim; positivity
#print axioms manage_bound
omit L H
private lemma angel (F:Streams) (n:ℕ) : AEStronglyMeasurable (toEarth F n) MeasureTheory.volume := by
 have he: Continuous (fun (p:Gaia)=> nres n (E (dial p) (F 0))*balljac F p):= ((((continuous_const.add ((E_cont _).comp cast_dial)).div_const (2:ℂ)).pow n).mul (Jacobian F))
 exact ((he.measurable.indicator earth_meas).comp (show Measurable (moveJ n) from (continuous_id.const_smul (winSize n)⁻¹).measurable)).aestronglyMeasurable
private lemma integrant (C:ℝ)(p:0<C):Integrable (Brim C):=by
 have he:Integrable (fun x:Gaia=> ((Brim C x:ℝ):ℂ)):=by simp_rw [Brim,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg]; simpa using integrable_cexp_neg_mul_sq_norm_add (b:=(C:ℂ)) p 0 (0:Gaia)
 exact (show Integrable (fun x:Gaia=>((Brim C x:ℂ)).re) from he.re)
include L H
lemma meteringJ : Tendsto (fun n:ℕ=> ∫ x:Gaia,toEarth (r M) n x) atTop (𝓝 (16*(Real.pi:ℂ)^2)):=by
 obtain ⟨C,D,u,p,e⟩:=manage_bound L H M; let X:= fun x:Gaia=> ((Brim κ x:ℝ):ℂ)
 have Xφ:=tendsto_integral_filter_of_dominated_convergence (l:=atTop) (μ:=MeasureTheory.volume) (fun x=>D*Brim C x) (Eventually.of_forall (fun n=> angel (r M) n)) ((eventually_gt_atTop 0).mono fun i u=> Eventually.of_forall (e i u)) ((integrant C u).const_mul D) (Eventually.of_forall (fun x=>oracle_lim L H M x))
 convert Xφ using 2
 unfold Brim; rw [integral_complex_ofReal,integral_rexp_neg_mul_sq_norm (by norm_num : (0:ℝ)<1/4),show Module.finrank ℝ Gaia=4 from finrank_euclideanSpace_fin]; norm_num [show (4:ℝ)/2=2 by ring]; push_cast; ring -- exponent simp
#print axioms meteringJ
end Zephyr.Chern.IndexMag
