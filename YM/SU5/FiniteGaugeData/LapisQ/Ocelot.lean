import YM.SU5.FiniteGaugeData.LapisQ.Frax
import YM.SU5.FiniteGaugeData.LapisQ.Feather
/-! # Harmon.S. Smoothing away harmonic. not full weak conv assertion. UP uniform.
-/
set_option autoImplicit false
set_option maxHeartbeats 580000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Willow
open Vulcan Nosh
variable {α:Type}[Fintype α] {β:Type}[Fintype β]
variable {n:Side} {u:Stage}{P:Bed} {ρ C Δ ε σ K:ℝ}{z:Phase4}
local notation "S"=> Site n
variable (t x:Site n)
abbrev harp (t:Site n):Phase4:= Exterior.q (mon t)
lemma harpC (i): harp t i=cell t (step i)-1:= by rw [cell_step]; rfl
lemma bendW : ‖harp (t+x)-harp t‖ ≤ ‖harp x‖:= by
 refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>?_ ; rw [Pi.sub_apply,harpC, harpC]
 rw [show cell (t+x) (step i)=cell t (step i)*cell x (step i) from (by rw [cell_duality (t+x),cell_add,cell_duality t, cell_duality x]), show cell t (step i)*cell x (step i)-1-(cell t (step i)-1) =cell t (step i)* harp x i from (by rw [harpC]; ring),norm_mul,cell_pay,one_mul]; exact norm_le_pi_norm _ _
variable {t x}
lemma windBudget {r:ℕ}(h:r+1<n.val): (∑ x:Site n,windK r x * sqLength (harp x))= 8/(r+1:ℝ):=by -- remove binder
 simp_rw [sqLength_apply,mul_sum]; rw [sum_comm]; simp_rw [harp,weft h, sum_const,card_univ, show Fintype.card Axis=4 from rfl]; rw [nsmul_eq_mul]; norm_num; ring -- tune
lemma flareA (y:Phase4): ‖y‖^2 ≤ sqLength y:=by
 refine le_trans (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (Real.sq_sqrt (sqLength_nonneg y)).le; exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i=> component_le_length _ _
variable {r:ℕ}
local notation "V"=> Phase4
noncomputable def lore (t:Site n)(r:ℕ)(f:Site n→ℂ): ℂ:= cropE r (fun x=>f (t+x))
private lemma tune_crop (h:r+1<n.val)(u:ℂ) (f:S→ℂ)(t:Site n) : lore t r f-u= ∑ x:Site n,(windK r x:ℂ)*(f (t+x)-u):= by
 simp_rw [mul_sub,sum_sub_distrib,←sum_mul,←Complex.ofReal_sum,wind_sum h,Complex.ofReal_one,one_mul]; rfl
lemma tender (h:r+1<n.val)(u:ℂ)(T b:ℝ)(f:S→ℂ)(t:Site n)(w:∀ z:Site n,‖f (t+z)-u‖≤ T+ b*sqLength (harp z)): ‖lore t r f-u‖ ≤ T+ b*(8/(r+1:ℝ)):=by
 rw [tune_crop h]; have he(x:Site n): ‖(windK r x:ℂ)*(f (t+x)-u)‖≤ windK r x*(T+b*sqLength (harp x)):=by
    rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (wind_p _)]; exact mul_le_mul_of_nonneg_left (w x) (wind_p x)
 refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=> he i)).trans_eq ?_); simp_rw [mul_add,mul_left_comm (windK r _) b,sum_add_distrib,←sum_mul,←mul_sum,wind_sum h,windBudget h,one_mul]
variable {A:Matrix (Body 2 n) (Body 2 n) ℝ}
local notation "F" x:max p:max=> facet x p f0 f0
local notation "Y" y:max=> camp y f0 f0
abbrev road (A:Matrix (Body 2 n) (Body 2 n) ℝ)(r:ℕ) (t:Site n):ℂ:= lore t r fun x=> facet A x f0 f0
lemma carriage (σ ρ K:ℝ)(p:0<ε) :∃ x:ℝ,0<x∧∀ z:Phase4,z≠0→‖z‖<x→∃ δ:ℝ,0<δ ∧ ∀ᶠ r:ℕ in atTop,∀ {n:Side}{A:Matrix (Body 2 n) (Body 2 n) ℝ}{u:Stage}{P:Bed}{C:ℝ}{t:Site n}, Gate u P ρ C σ K n A → r+1<n.val→‖harp t-z‖≤δ →‖road A r t-camp z f0 f0‖≤ε :=by
 let μ:= ε/4; have hm:0<μ:=by unfold μ; positivity
 obtain ⟨x,u,h⟩:= promise σ ρ K hm; refine ⟨x,u, fun z v w=>?_⟩
 let Q: Set V:= {y|‖y‖ < x ∧ y≠0∧ ‖camp y f0 f0-camp z f0 f0‖ < μ }
 have hQ : Q∈𝓝 z:=by
    have he: {y:Phase4|y≠0}∈𝓝 z:=compl_singleton_mem_nhds v
    filter_upwards [he,(continuous_norm.continuousAt (x:=z)).tendsto.eventually (gt_mem_nhds w), (cap_C z v f0 f0).tendsto.eventually (Metric.ball_mem_nhds _ hm)] with x t p p'; exact ⟨p,t,show _ from (by rwa [dist_eq_norm] at p')⟩
 obtain ⟨d,b,v0⟩:=Metric.mem_nhds_iff.mp hQ
 let δ:= d/4; have hd:0<δ:=by unfold δ; positivity
 let C':=(1/ρ+1)/(δ^2); have hb:Tendsto (fun r:ℕ=> C'*(8/(r+1:ℝ))) atTop (𝓝 0):=by -- simple denom tendsto
    have hp:Tendsto (fun r:ℕ=> (r:ℝ)+1) atTop atTop:= Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R:=ℝ)) tendsto_const_nhds -- name
    simpa using (tendsto_const_nhds.div_atTop hp |>.const_mul C') -- type infer
 refine ⟨δ,hd,?_⟩; filter_upwards [hb.eventually (ge_mem_nhds hm)] with r v_ n A u P C t g b0 ht -- shadow `b` from previous
 -- v0 subset function.V window; need η positive from Q. Ring.
 have hρ:0<ρ:=g.cost; have hv:0 ≤ C':=by unfold C'; positivity
 have he(y:Site n): ‖facet A (t+y) f0 f0-camp z f0 f0‖ ≤ μ*2+C' *sqLength (harp y):=by
    let u:=harp (t+y); by_cases he:‖harp y‖ ≤ δ
    · have hy:u∈Q:=by
         apply v0; rw [Metric.mem_ball,dist_eq_norm]; refine lt_of_le_of_lt ((norm_sub_le_norm_sub_add_norm_sub u (harp t) z).trans (add_le_add ((bendW t y).trans he) ht)) ?_; unfold δ; linarith only [b]
      refine (norm_sub_le_norm_sub_add_norm_sub (facet A (t+y) f0 f0) (camp u f0 f0) (camp z f0 f0)).trans (le_trans (add_le_add (h g hy.2.1 hy.1.le f0 f0) hy.2.2.le) ?_); nlinarith only [mul_nonneg hv (sqLength_nonneg (harp y))]
    apply le_trans (norm_sub_le ..)
    have hz: ‖facet A (t+y) f0 f0‖≤1/ρ:= frontier_entry g _ _ _ -- v lost binder!
    have hh: δ^2 ≤ sqLength (harp y):= (pow_le_pow_left₀ hd.le ((lt_of_not_ge he).le) 2).trans (flareA _); -- fix
    have hw:1/ρ+1≤ C'*sqLength (harp y):=((div_mul_cancel₀ ((1:ℝ)/ρ+1) (pow_pos hd 2).ne').symm).le.trans (mul_le_mul_of_nonneg_left hh hv)
    linarith only [hm, passport z ‹_› f0 f0,hz,hw]
 apply le_trans (tender b0 _ (μ*2) C' _ t he); have hp:C'* (8/(r+1:ℝ)) ≤ μ:=v_; unfold μ at *; linarith only [hp,hm]
end Willow
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Willow.carriage
