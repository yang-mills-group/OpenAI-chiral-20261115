import ZecaOcean
import YM.Heat.Imaginary
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open OS Semigroup

variable {H:Hilbert}{j:Axis}(S:Semigroup H j)(X:ℝ→H)(y:Cross j)(δ:ℝ)

def oceanRun (z:ℂ):ℂ:=
 let x:=δ*z.re/2
 inner ℂ (X x) (S.U y (S.edge (-(δ*z.im)) (X x)))
lemma oceanRun_real(x:ℝ):
 oceanRun S X y δ ↑(2*x)=inner ℂ (X (δ*x)) (S.U y (X (δ*x))):=by
 -- coercions
 unfold oceanRun
 simp [S.birth]
 ring_nf

variable (xpay:∀ t u:ℝ,0<t→t≤u→ X u=S.E (u-t).toNNReal (X t))
include xpay

lemma oceanRun_hot(v:ℝ)(p:0<v)(z:ℂ)(q:v<δ*z.re/2):
 oceanRun S X y δ z=
 inner ℂ (X v) (S.U y (S.F ((δ:ℂ)*z-2*v) (X v))):=by
 let t:= (δ*z.re/2-v).toNNReal
 have ht:=Real.toNNReal_pos.mpr (sub_pos.mpr q)
 have g:=(S.E t).adjoint_inner_left
 rw [S.sym] at g
 have a:=dur.mpr ht
 dsimp only [oceanRun]; rw [xpay v _ p q.le,g,
    ← ContinuousLinearMap.comp_apply (S.E t),S.independent,
        ContinuousLinearMap.comp_apply]
 rw [←S.roots_heat ht,← ContinuousLinearMap.comp_apply (S.edge _),S.along a,
    ←ContinuousLinearMap.comp_apply (S.F (duration t)),←S.pairs a ((allow _ _).mpr a)]
 suffices duration t+(duration t+sideways (-(δ*z.im)))=((δ:ℂ)*z-2*v) by rw [this]
 apply Complex.ext
 · simp [t,duration,Real.coe_toNNReal _ (sub_pos.mpr q).le]
   ring
 simp [t,duration,sideways]

lemma oceanRun_d (p:0<δ) :DifferentiableOn ℂ (oceanRun S X y δ) Inlet:=by
  intro z hz
  change 0<z.re at hz
  let f(z:ℂ):=δ*z.re/2
  have h:0<f z:=(by unfold f;positivity)
  obtain ⟨v,pv,q⟩:=exists_between h
  let g(z:ℂ):=(δ:ℂ)*z-2*v
  have pg:g z∈inside:=by
    change 0<Complex.re _
    unfold f at q; simp [g];linarith only[q]
  have hg:DifferentiableAt ℂ g z:=by unfold g;fun_prop
  have w:=(differentiableAt_const (𝕜:=ℂ) (x:=z) (S.U y)).clm_apply
    (((S.localHeat _ pg).differentiableAt.comp z hg).clm_apply
        (differentiableAt_const (X v)))
  have a:=((innerSL ℂ (X v)).differentiableAt.comp z w)
  refine (a.congr_of_eventuallyEq ?_ :DifferentiableAt ℂ (oceanRun S X y δ) z).differentiableWithinAt
  filter_upwards [(isOpen_lt continuous_const (show Continuous f from by unfold f;fun_prop)).mem_nhds q] with z q
  exact oceanRun_hot S X y δ xpay v pv z q

#print axioms oceanRun_d
#check differentiableAt_const

omit xpay
lemma deeper {M x:ℝ} (p:0<M)(q:0<x)(d:ℕ):
    (M*spur d (x/2))^2 ≤
   (M^2*2*4^d)*spur (2*d) x:=by
 unfold spur
 have e:(1/(x/2))=2*(1/x):=by field_simp
 rw [e, mul_pow,mul_pow (2:ℝ),mul_assoc,mul_assoc,
    pow_mul' _ 2 d,show (4:ℝ)=(2:ℝ)^2 by norm_num,pow_right_comm (2:ℝ) 2 d]
 apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
 let a:=(2:ℝ)^d
 let b:=(1/x)^d
 have i:1≤a^2:=one_le_pow₀ (one_le_pow₀ (by norm_num))
 change (1+a*b)^2≤_
 nlinarith only [i,sq_nonneg (1-a*b)]
#print axioms deeper
