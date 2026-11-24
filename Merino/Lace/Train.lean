import Merino.Lace.Ray
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Lace
open Garter Regis.Circuit CF.Lat
open Stationary (Gaia)
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

variable (B:Z.Bounds q η C S)(P:Attached H Z)
local notation "wE"=>stamen B P n
local notation "χ"=>stdGaussian wE
local notation "J"=>Husk G n


open Ember Onyx


abbrev miles(t:ℕ):ℝ:=2*(t:ℝ)
abbrev Steam(n:Side)(t:ℕ):Prop:=(t:ℝ)^2 ≤ (n.val:ℝ)
lemma depart {u:ℕ→ℕ} (h: Tendsto u atTop atTop):
 Tendsto (fun i=>miles (u i)) atTop atTop :=
 Filter.Tendsto.const_mul_atTop (by norm_num: (0:ℝ)<2) (tendsto_natCast_atTop_atTop.comp h)
lemma spacious {u:ℕ→ℕ} (h:Tendsto u atTop atTop)(v:∀ i,0<u i)
 {N:ℕ→Side}(p:∀ i,Steam (N i) (u i))(e:∀ i,Even (N i).val):
 Yard N (miles∘u):=by
 have s (i):0<(u i:ℝ):=by exact_mod_cast v i
 refine ⟨fun i=>mul_pos (by norm_num) (s i),depart h, squeeze_zero
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (s i).le) (pinch_pos _).le) (g:=fun i=>2*Real.pi / (u i:ℝ))
    ?_ (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h)),e⟩
 intro i
 apply le_trans (b:=miles (u i)*(Real.pi/(u i:ℝ)^2)) 
 · have :=s i
   unfold miles Function.comp pinch
   gcongr;exact p _
 have :=s i
 unfold miles;field_simp; exact le_rfl


abbrev noon(t:ℕ):Cover:= (t:ℤ) • step pole
def Raill(t:ℕ)(z:Cover):Prop:=
 ∀ i:Axis,(((z-(noon t+noon t)) i:ℤ):ℝ)^2 ≤ miles t

lemma arrives {u:ℕ→ℕ} (h:Tendsto u atTop atTop)(v:∀ i,0<u i)
 {z:ℕ → Cover}(x:∀ i, Raill (u i) (z i)):
 Tendsto (fun i=>riseX (miles (u i)) (z i)) atTop (𝓝 ray):=by
 have hm(i) : 0 < miles (u i):=by have :=v i; unfold miles; positivity
 let f(i:ℕ)(j:Axis):=(((z i-(noon (u i)+noon (u i))) j:ℤ):ℝ)/miles (u i)
 have t:Tendsto f atTop (𝓝 0):=by
    apply tendsto_pi_nhds.mpr
    intro j
    apply squeeze_zero_norm
       (a:=fun i=>Real.sqrt (miles (u i))⁻¹) 
    · intro i
      have a:=hm i
      apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (inv_nonneg_of_nonneg a.le)]
      unfold f;rw [div_pow]
      exact (div_le_div_of_nonneg_right (x i j) (sq_nonneg _)).trans_eq (by field_simp)
    · have iu:= tendsto_inv_atTop_zero.comp (depart h)
      exact (show Real.sqrt 0=0 by norm_num) ▸ (Real.continuous_sqrt.tendsto 0).comp iu


 have g:Tendsto (fun i=>WithLp.toLp 2 (f i)) atTop (𝓝 0):=(PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp t
 have r:=g.add_const ray;rw [zero_add] at r
 apply r.congr
 intro i;ext j
 have ih:0<u i :=by exact v i
 change f i j+ (YM.basis pole) j=(z i j:ℝ)/miles (u i)
 by_cases e:j=pole
 · subst j
   simp [f,noon,basis,miles]
   field_simp;ring
 simp [f,noon,basis,e,step]


abbrev sunLag(a b:PlaqAxes)(H:Bed)(t:ℕ):= magnify H (miles t) (plaquette a) (plaquette b)
variable {σ ψ:ℝ}

lemma rainbow (a b:PlaqAxes)(q:Clip) (δ:ℝ)
  (s0:0 < σ) (v0:0 < v) (e:ℝ)(p:0<e):
 ∀ᶠ t in atTop, ∀ z,Raill t z → ∀ (n:Side),Steam n t → Even n.val → ∀ H:Bed,
 H.covered σ v → Floor H q n δ v→ 
  dist (sunLag a b H t z n) (specter a b ray) ≤ e:=by
 by_contra h
 push Not at h
 obtain ⟨u,r,X⟩:=extraction_of_frequently_atTop (h.and_eventually (eventually_gt_atTop 0))
 have vp(i):= (X i).2
 choose z hz N hN n₀ M mh f y using fun i=> (X i).1
 have := mercury a b (spacious r.tendsto_atTop vp hN n₀)
   (arrives r.tendsto_atTop vp hz) ray0 mh f s0 v0
 obtain ⟨i,he⟩:=(Metric.tendsto_nhds.mp this e p).exists
 exact lt_asymm he (y i)
end YM.CF.Merino.Lace
