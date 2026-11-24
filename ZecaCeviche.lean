import ZecaMantle
import ZecaOcean
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology


open Lattice Regis.Head.Brecht Regis.Circuit Stationary MeasureTheory

def Aquavit (y:Gaia)(z:ℝ):Gaia:= WithLp.toLp 2 fun i=>
    if i=3 then z else y i
def limon (y:Gaia)(z:ℂ)(i:Axis):ℂ:= if i=3 then z else y i
def limonQ (y:Gaia)(z:ℂ):ℂ:=(↑‖y‖:ℂ)^2+z^2

lemma limon_r (y:Gaia) (h:y 3=0) (x:ℝ):
  ‖Aquavit y x‖^2= ‖y‖^2+x^2:=by
 rw [EuclideanSpace.real_norm_sq_eq]
 have d(i:Axis):(Aquavit y x i)^2=(y i)^2+ if i=3 then x^2 else 0:=by
    by_cases a:i=3
    · simp [a,Aquavit,h]
    · simp [Aquavit,a]
 rw [Finset.sum_congr rfl (fun i _=>d i),Finset.sum_add_distrib,
    ← EuclideanSpace.real_norm_sq_eq];simp

variable (z:PlaqAxes→ℝ)(G:Gauge)
def Salud(y:Gaia)(t:ℂ):ℂ:=satire z G (limon y t) (limonQ y t)
lemma sangre (y:Gaia) (h:y 3=0) {x:ℝ}(p:0<x):
 spectrumℓ z G (Aquavit y x)= Salud z G y x:=by
 have j:(fun i=>(↑(Aquavit y x i):ℂ))=limon y x:=by
    funext i; unfold Aquavit limon
    rw [WithLp.ofLp_toLp]; split<;>rfl
 have t:Aquavit y x≠0:=by
   intro e
   have v:=congrArg (fun u:Gaia=>u 3) e; simp [Aquavit,p.ne'] at v
 rw [satire_in _ _ _ t,j,limon_r y h x]
 push_cast; rfl
def Straits(y:Gaia):Set ℂ:={z|z.re ≠ 0 ∨ |z.im| < ‖y‖}

lemma limon_mem(y:Gaia)(v:ℂ)(e:v∈Straits y):
   limonQ y v≠0:=by
 intro t
 have a:=congrArg Complex.re t; have b:=congrArg Complex.im t
 simp [limonQ,sq] at a b
 rcases e with l|r
 · have :v.im=0:=by
      by_contra k
      have ha :v.re * v.im ≠ 0:=mul_ne_zero l k
      exact ha (by linarith only [b])
   rw [this] at a
   nlinarith only [a,sq_pos_of_ne_zero l,sq_nonneg ‖y‖]
 have u:=pow_lt_pow_left₀ r (abs_nonneg _) (by decide:(2:ℕ)≠0)
 rw [sq_abs] at u
 nlinarith only [a,u,sq_nonneg v.re]

lemma lima_free(y:Gaia):
 DifferentiableOn ℂ (Salud z G y) (Straits y):=by
 apply satire_d
 refine ⟨fun i=>?_,?_,limon_mem y⟩
 · unfold limon;split_ifs <;>fun_prop
 · unfold limonQ;fun_prop

lemma salud_hot(y:Gaia):
 DifferentiableOn ℂ (Salud z G y) Inlet:=
    (lima_free z G y).mono (fun _ (p:_∈Inlet)=>Or.inl (ne_of_gt p))

lemma salud_mix(y:Gaia){T:ℝ} (p:T< ‖y‖):
 Bay T (Salud z G y):=by
 apply (lima_free z G y).continuousOn.comp (tide_c.continuousOn)
 intro w e
 apply Or.inr
 simp only [tide, Complex.sub_im, Complex.ofReal_im, Complex.mul_I_im, zero_sub,Complex.ofReal_re,abs_neg]
 exact (abs_le.mpr e.2).trans_lt p

-- reversal
lemma salud_again(y:Gaia)(t:ℂ):
 Salud z G (-y) (-t)=Salud z G y t:=by
 have e(j):limon (-y) (-t) j= -limon y t j:=by
   unfold limon; split_ifs <;>simp
 unfold Salud limonQ satire stamp curlIn bill
 simp_rw [e,neg_mul_neg,neg_sq,norm_neg]
def Tow (W:ℕ→ℝ→ℂ)(k:ℕ)(t:ℝ):ℂ:=(-1:ℂ)^k* W k (-t)
lemma Temporal.tow {T:ℝ}{W:ℕ→ℝ→ℂ}
   (h:Temporal T W):Temporal T (Tow W):=by
 refine ⟨fun n t=>?_,
    fun n=>by simp [Tow,h.hi],
    fun n=>by simp [Tow,h.lo]⟩
 have u:= (h.up n ((fun x:ℝ=>-x) t)).scomp t ((hasDerivAt_id' t).neg)
 have d:=u.const_mul ((-1:ℂ)^n)
 simp only [neg_smul,one_smul, mul_neg] at d
 unfold Tow
 rw [pow_succ,mul_neg,mul_one,neg_mul]
 exact d
#check intervalIntegral.integral_comp_neg
#print axioms salud_hot

lemma salud_reverse (y:Gaia){T:ℝ}(p:0<T)(W:ℕ→ℝ→ℂ):
 shellI (Salud z G (-y)) T (Tow W 0) 0=shellI (Salud z G y) T (W 0) 0:=by
 have e:-T≤T:=by linarith
 unfold shellI; rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
         ← intervalIntegral.integral_of_le e,←intervalIntegral.integral_of_le e]
 let f(t:ℝ):= W 0 t * Salud z G y (tide 0 t)
 have q(t):tide 0 t= -tide 0 (-t):=by simp [tide]
 have w(t):Tow W 0 t * Salud z G (-y) (tide 0 t)= f (-t):=by
    rw [q,salud_again]
    simp only [Tow,pow_zero,one_mul,f]
 have h:=
   intervalIntegral.integral_comp_neg (a:= -T) (b:=T) f
 simp_rw [w];rw [h,neg_neg]
#print axioms salud_reverse
