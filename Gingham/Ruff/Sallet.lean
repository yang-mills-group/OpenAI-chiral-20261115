import Gingham.Ruff.Subito
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Finset
open Jet
open scoped Topology ContDiff
variable {n:ℕ}{c:ℝ}{E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {f:E→F}

/-- In actual colors, evaluated on unscaled coordinates of Gallery. -/
def quadraticChi (f:E→F)(v:E):F:=(2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) 0 v v

lemma quadraticChi_smul (f:E→F)(v:E)(t:ℝ):
 quadraticChi f (t • v)=t^2 • quadraticChi f v:=by
 simp [quadraticChi,smul_smul]; ring_nf

lemma quadraticChi_small
   (G:Gallery 2 f c)(v:E): ‖quadraticChi f v‖ ≤ c*‖v‖^2:= by
 rw [quadraticChi,norm_smul,Real.norm_of_nonneg (by norm_num)]
 have p:= (G.thread.thread 0 (by simp)).value
 refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num))
    (((_ : E→L[ℝ]F).le_opNorm _).trans ?_)
 rw [pow_two,←mul_assoc]
 exact mul_le_mul_of_nonneg_right (((_ : E→L[ℝ](E→L[ℝ]F)).le_opNorm _).trans
     (mul_le_mul_of_nonneg_right p (norm_nonneg v))) (norm_nonneg v)


lemma quadraticChi_pressure
   (G:Gallery 3 f c)(z:fderiv ℝ f 0=0)(v:E):
   Tendsto (fun t:ℝ => (t^2)⁻¹ • (f (t • v)-f 0))
     (𝓝[>] 0) (𝓝 (quadraticChi f v)):=by
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
   (tendsto_const_nhds (x:=0)) (h:=fun t=>t*(c*‖v‖^3)) ?_ ?_ ?_


 · simpa using (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[>] (0:ℝ)) (𝓝 0)).mul_const (c*‖v‖^3)
    -- 0* not defeq?
 · exact Eventually.of_forall fun t=>norm_nonneg _
 have h:∀ᶠ t:ℝ in 𝓝 0, ‖t • v‖<1:=
   ((continuous_id.smul continuous_const).norm.tendsto 0).eventually (gt_mem_nhds (by simp))
 filter_upwards [self_mem_nhdsWithin,h.filter_mono nhdsWithin_le_nhds] with t p r
 change 0<t at p
 have w := G.cubic z r
 have ci:=mul_le_mul_of_nonneg_left (a:=(t^2)⁻¹) w (by positivity)
 rw [norm_smul,Real.norm_of_nonneg p.le] at ci
 have R(t:ℝ)(k:0<t):
    quadraticChi f v=(t^2)⁻¹ • ((2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) 0 (t • v) (t • v)):=by
  change _=(t^2)⁻¹ • quadraticChi f _
  rw [quadraticChi_smul,inv_smul_smul₀ (pow_ne_zero 2 k.ne')]
 rw [R t p,←smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
 refine ci.trans_eq ?_
 have : t≠0:=p.ne'; field_simp


#print axioms quadraticChi_pressure

