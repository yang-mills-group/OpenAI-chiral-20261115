import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace ThinGauge
open Real Filter
open scoped Topology
-- $ constants before L.YJ Angle Ico estimates all in Real.
abbrev slope:= Real.exp (-1) /4
lemma slope_live:0<slope:=div_pos (Real.exp_pos _) (by norm_num)
abbrev Bmain:ℝ:=4/slope -- covers rescale C_j = r'/b. b≥slope/2 r *dL^4
-- choose boost factor H$ : ≥16 Bmain^p? T tolerance. Eventual UV d constraint.The worsening by logL.A ok. hCost $excess.Core pre
abbrev gain:= 64*Bmain+64
variable (g0 Δ Cℓ:ℝ)(A:ℝ) -- g0 red coeff, Δ Axon coefficient and Cℓ= duty_Q. A=target coarse price normalized per q_j
abbrev lowerCost(g0 A:ℝ):= |g0| *(Real.exp 1 + A+2)
abbrev yolk(δ Cℓ:ℝ):= |δ*Cℓ| * (Real.exp 1+2) -- need A*x eventually A+2 ≤? Q terms.W unauthorized lens $ε=d^6 etc. choose threshold forcing (A+2)*d≤2.
abbrev shell(Δ Cℓ A:ℝ):= |Δ*Cℓ| *(A+1)
abbrev spineK(g0 A:ℝ):=Bmain*lowerCost g0 A
lemma bm_pos: 0<Bmain:=by unfold Bmain; exact div_pos (by norm_num) slope_live
lemma gain_pos:0<gain:=by unfold gain; linarith only [bm_pos]
abbrev winS(r H:ℝ):= r⁻¹≥H -- unused
structure Open(g0 Δ Cℓ A:ℝ)(d:ℝ):Prop where
 hm:0<d
 tax:d≤1
 asset:1≤A
 crown: Bmain * yolk Δ Cℓ ≤ A/4
 credit:d*(A+1)≤1
 faith:d*lowerCost g0 A≤ slope/2
 peak:d*spineK g0 A≤1/8
 dut: d*(gain*(spineK g0 A*yolk Δ Cℓ + shell Δ Cℓ A))≤A/4
lemma sunL (g0 Δ Cℓ A:ℝ)(h:1≤A)(p:Bmain*yolk Δ Cℓ ≤ A/4):∀ᶠ i:ℕ in atTop, Open g0 Δ Cℓ A ((i:ℝ)⁻¹):=by
 have he:Tendsto (fun i:ℕ=>(i:ℝ)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
 have q(r v:ℝ)(p:0<v):∀ᶠ i:ℕ in atTop, ((i:ℝ)⁻¹)*r ≤ v:=by
    have hv:0*r<v:=by linarith
    exact (he.mul_const r|>.eventually (ge_mem_nhds hv))
 filter_upwards [q (A+1) 1 one_pos,q (lowerCost g0 A) (slope/2) (by apply half_pos slope_live),q (spineK g0 A) (1/8) (by norm_num),q (gain*(spineK g0 A*yolk Δ Cℓ+shell Δ Cℓ A)) (A/4) (by linarith),eventually_ge_atTop (1:ℕ)] with i v u d e hx
 refine ⟨inv_pos.mpr (Nat.cast_pos.mpr hx), inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr hx),h,p,v,u,d,e⟩
#check sunL
end ThinGauge
