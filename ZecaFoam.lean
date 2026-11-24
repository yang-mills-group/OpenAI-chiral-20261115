import ZecaEddy
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open MeasureTheory Complex

/-- temporal smooth test via full derivative chain flat at ±T. -/
structure Temporal (T:ℝ)(W:ℕ→ℝ→ℂ):Prop where
 up:∀ n t,HasDerivAt (W n) (W (n+1) t) t
 lo:∀ n,W n (-T)=0
 hi:∀ n,W n T=0
def tide (x t:ℝ):ℂ:=x-t*I
def shellI (A:ℂ→ℂ)(T:ℝ)(φ:ℝ→ℂ)(x:ℝ):ℂ:=
 ∫ t in Icc (-T) T,φ t*A (tide x t)

variable {T:ℝ} {W:ℕ→ℝ→ℂ} {A:ℂ→ℂ}

lemma Temporal.slow (h:Temporal T W)(n):Continuous (W n):=continuous_iff_continuousAt.mpr fun t=>(h.up n t).continuousAt

lemma tide_re(x t:ℝ):(tide x t).re=x:=by simp [tide]
lemma tide_p{r:ℝ}(p:0<r)(t:ℝ): tide r t∈Inlet:=lt_of_lt_of_eq p (tide_re ..).symm
lemma tide_c :Continuous (fun v:ℝ×ℝ=>tide v.1 v.2):= by unfold tide;fun_prop
lemma surf_c (g: ContinuousOn A Inlet) (x:ℝ) (u:0<x):
   Continuous (A ∘ tide x):=g.comp_continuous (by unfold tide;fun_prop) (tide_p u)

lemma redshift (g:DifferentiableOn ℂ A Inlet)(p:0<T)
 (h:Temporal T W) (n:ℕ) {x:ℝ} (u:0<x):
 HasDerivAt (shellI A T (W n)) (-I*shellI A T (W (n+1)) x) x:=by
 let Z:=Icc (-T) T
 let μ:=volume.restrict Z
 let J:=Icc (x/2) (x+1)
 have m0:= Icc_mem_nhds (half_lt_self u) (lt_add_one x)
 have ix:x∈J:=mem_of_mem_nhds m0
 have wp(y)(a:y∈J):0<y:= lt_of_lt_of_le (half_pos u) a.1
 have gs(w)(b:w∈Inlet):HasDerivAt A (deriv A w) w:=(g.differentiableAt (quay.mem_nhds b)).hasDerivAt

 have a':ContinuousOn (deriv A) Inlet:=((g.analyticOnNhd quay).deriv).continuousOn
 let f y t:= W n t*A (tide y t)
 let b y t:=W n t*deriv A (tide y t)
 have dc:ContinuousOn (fun v:ℝ×ℝ=>b v.1 v.2) (J×ˢZ):=
     ((h.slow n).comp continuous_snd).continuousOn.mul (a'.comp tide_c.continuousOn
            (fun v t=> tide_p (wp _ t.1) _))
 have v(y)(a:y∈J):Continuous (f y):= (h.slow _).mul (surf_c g.continuousOn y (wp _ a))
 have b0:= (h.slow n).mul (surf_c a' x u)
 have ds (t) (r) (w:r∈J): HasDerivAt (fun y=> f y t) (b r t) r:=by
    have l:HasDerivAt (fun y=> tide y t) (1:ℂ) r:=by
       unfold tide; simpa using ((hasDerivAt_id' r).ofReal_comp.sub_const ((t:ℂ)*I))
    have e:= ((gs _ (tide_p (wp _ w) t)).comp r l).const_mul (W n t)
    rw [mul_one] at e
    exact e
 have dcK:IsCompact (J×ˢ Z):=isCompact_Icc.prod isCompact_Icc
 obtain ⟨C,vC⟩:=dcK.bddAbove_image dc.norm
 have cp:Integrable (fun _:ℝ=>C) μ:=continuous_const.continuousOn.integrableOn_Icc
 let hn:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (F:=f) (F':=b) m0
        ((show ∀ᶠ y in 𝓝 x, y∈J from m0)|>.mono fun y k=>(v y k).aestronglyMeasurable)
        (v _ ix|>.continuousOn.integrableOn_Icc)
        b0.aestronglyMeasurable
        ((ae_restrict_mem (μ:=volume) (measurableSet_Icc (a:= -T) (b:=T))).mono fun t a y e=>vC
           ⟨(y,t),⟨e,a⟩,rfl⟩)
        cp (ae_of_all μ ds)
 have hj:HasDerivAt (shellI A T (W n)) (∫ t,b x t ∂μ) x:= hn.2
 have at0(t): HasDerivAt (A ∘ tide x) (deriv A (tide x t)*(-I)) t:=by
    have e:HasDerivAt (tide x) (-I) t:=by
       unfold tide
       simpa using (((hasDerivAt_id' t).ofReal_comp.mul_const I).const_sub (x:ℂ))
    exact (gs _ (tide_p u t)).comp t e
 have bv:Continuous (deriv A ∘ tide x):= surf_c a' _ u
 have bp:=intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t (_:t∈uIcc (-T) T)=>h.up n t)
    (fun t _=> at0 t)
    (h.slow (n+1)|>.intervalIntegrable ..)
    ((bv.mul continuous_const).intervalIntegrable ..)
 have e:(∫ t,W n t*(deriv A (tide x t)*(-I)) ∂μ)= - shellI A T (W (n+1)) x:=by
    have e:(-T≤T):=by linarith
    rw [h.lo,h.hi,zero_mul,zero_mul,sub_zero,zero_sub, intervalIntegral.integral_of_le e,
       intervalIntegral.integral_of_le e,← integral_Icc_eq_integral_Ioc,
       ← integral_Icc_eq_integral_Ioc] at bp
    exact bp
 simp_rw [← mul_assoc, integral_mul_const] at e
 have b': (∫ t,b x t ∂μ)= -I*shellI A T (W (n+1)) x:= by
   unfold b
   let V:=∫ t:ℝ, W n t*deriv A (tide x t)∂μ
   change V* -I= _ at e
   change V=_
   linear_combination I * e + V * Complex.I_mul_I 
        -- uses I²?
 rw [←b'];exact hj
#print axioms redshift
