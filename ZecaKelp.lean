import ZecaMantle
import ZecaFinray
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary



-- n any Gaia vector ∈ spatial unit sphere 
def current(n:Gaia)(s:ℝ)(z:ℂ)(i:Axis):ℂ:=
  if i=3 then s else (n i:ℂ)*z
def currentQ(s:ℝ)(z:ℂ):ℂ:=z^2+(s:ℂ)^2
def wake(n:Gaia)(s u:ℝ):Gaia:=
    WithLp.toLp 2 fun i:Axis=> if i=3 then s else n i * u
variable {n:Gaia}{s α:ℝ}{z:ℂ}

lemma wake_mem {s:ℝ} (p:s≠0)(x:ℝ):wake n s x≠0:=by
 intro e
 have r:=congrArg (fun y:Gaia=>y 3) e
 simp [wake,p] at r
lemma wake_sums (v:n 3=0) (y:‖n‖=1) (x:ℝ):
 ‖wake n s x‖^2=x^2+s^2:=by
 rw [EuclideanSpace.real_norm_sq_eq]
 have d(i:Axis):(wake n s x i)^2=(n i)^2*x^2+ if i=3 then s^2 else 0:=by
    by_cases a:i=3
    · simp [a,wake,v]
    · simp [wake,a,mul_pow]
 rw [Finset.sum_congr rfl (fun i _=>d i),Finset.sum_add_distrib,
    ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq]
 simp [y]

abbrev Kelper(colA:PlaqAxes→ℝ)(G:Gauge)(n:Gaia)(s:ℝ): ℂ→ℂ:=
 fun z=>satire colA G (current n s z) (currentQ s z)
lemma kelping(colA:PlaqAxes→ℝ)(G:Gauge) (v:n 3=0)(y:‖n‖=1) (p:s≠0)(x:ℝ):
 spectrumℓ colA G (wake n s x)=Kelper colA G n s x:=by
 have j:(fun i=>(↑(wake n s x i):ℂ))=current n s x:=by
    funext i; unfold wake current
    rw [WithLp.ofLp_toLp]; split<;> push_cast <;> rfl
 rw [satire_in _ _ _ (wake_mem p x),j,wake_sums v y x]
 push_cast; rfl

lemma kelp_room (sp:0≤ s) (u:0≤α)(q:α<1)(e:|z.im|≤α*s) :
 ‖z‖^2 ≤ z.re^2+s^2 ∧
    (1-α^2)*(z.re^2+s^2)≤‖currentQ s z‖:=by
 have a:=pow_le_pow_left₀ (abs_nonneg _) e 2
 rw [sq_abs,mul_pow] at a
 have b:= (pow_lt_one₀ u q (by decide: (2:ℕ)≠0)).le
 have y:=mul_le_of_le_one_left (sq_nonneg s) b
 constructor
 · rw [Complex.sq_norm]
   simp [Complex.normSq_apply]
   nlinarith only [a,y]
 refine le_trans ?_ (Complex.re_le_norm _)
 simp [currentQ,sq,Complex.mul_re]
 nlinarith only [a,mul_nonneg (sq_nonneg α) (sq_nonneg z.re)]

lemma kelp_pay (i j:Axis) (d:‖n‖=1) (sp:1≤ s)
 (u:0≤α)(q:α<1)(e:|z.im|≤α*s):
 ‖(currentQ s z)⁻¹‖ ≤ (1-α^2)⁻¹ ∧
     ‖current n s z i*current n s z j*(currentQ s z)⁻¹‖ ≤ (1-α^2)⁻¹:=by
 let X:=Real.sqrt (z.re^2+s^2)
 have a:1≤X:=by
    apply Real.le_sqrt_of_sq_le; nlinarith only [sp,sq_nonneg z.re]
 have g:X^2=z.re^2+s^2:=Real.sq_sqrt (by positivity)
 obtain ⟨A,W⟩:=kelp_room (s:=s) (by linarith) u q e
 have p:0<1-α^2:=sub_pos.mpr (pow_lt_one₀ u q (by decide))
 rw [←g] at A W
 have Q:0<‖currentQ s z‖:=lt_of_lt_of_le (by positivity) W
 have Y:(1-α^2)≤‖currentQ s z‖:=(le_mul_of_one_le_right p.le (one_le_pow₀ a)).trans W
 have price (i:Axis):‖current n s z i‖≤X:=by
    have c:‖(n i:ℂ)‖≤1:=by
       rw [Complex.norm_real]
       exact (PiLp.norm_apply_le n i).trans d.le
    unfold current; split
    · rw [Complex.norm_real,Real.norm_of_nonneg (by linarith : 0≤ s)]
      nlinarith only [g,a,sq_nonneg z.re]
    · rw [norm_mul]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg z) c) (by nlinarith only [A,a])
 constructor
 · rw [norm_inv]; exact inv_anti₀ p Y
 rw [norm_mul,norm_mul,norm_inv]
 refine le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (price i) (price j) (norm_nonneg _) (by linarith)) (inv_nonneg.mpr Q.le)) ?_
 field_simp;linarith only [W]
#print axioms kelp_pay
