import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern
open Filter Topology

abbrev Three (A:Type*) := Fin 3 → A
def splice {A:Type*} [Add A] [Mul A] (p q:Three A) : Three A :=
 ![p 0 * q 0,p 0 * q 1 + p 1 * q 0,p 0 * q 2+p 2 * q 0+p 1 * q 1]

/-- Second jets (in power coefficient convention). -/
def bud (f:ℝ→ℂ) : Three ℂ :=
 ![f 0,deriv f 0,(deriv (deriv f) 0) / 2]
def Bud (f:ℝ→ℂ) := (∀ᶠ x in 𝓝 0,DifferentiableAt ℝ f x) ∧
    DifferentiableAt ℝ (deriv f) 0
def Bloom (f:ℝ→ℂ) (c:Three ℂ) := Bud f ∧ c = bud f

variable {f g:ℝ→ℂ} {c d:Three ℂ}
lemma Bloom.bud_eq (h:Bloom f c) : bud f=c := h.2.symm
lemma Bloom.unique (h:Bloom f c) (h':Bloom f d) : c=d :=
  h.2.trans h'.bud_eq
lemma Bud.bloom (h:Bud f) : Bloom f (bud f) := ⟨h,rfl⟩
lemma Bud.ha (h:Bud f) : DifferentiableAt ℝ f 0 := h.1.self_of_nhds
lemma Bloom.of_der {a:ℝ→ℂ}
    (h : ∀ᶠ x in 𝓝 0,HasDerivAt f (a x) x)
    {b:ℂ}(k:HasDerivAt a b 0) (h0:c 0=f 0)(h1:c 1=a 0)(h2:c 2=b/2) : Bloom f c := by
  have e : deriv f =ᶠ[𝓝 0] a := h.mono fun x p=>p.deriv
  have dk := k.congr_of_eventuallyEq e
  refine ⟨⟨h.mono (fun _ p=>p.differentiableAt),dk.differentiableAt⟩,?_⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1.trans e.eq_of_nhds.symm
  · change c 2=deriv (deriv f) 0 / 2; rw [h2,dk.deriv]

lemma bud_congr (e:g =ᶠ[𝓝 0] f) : bud g = bud f := by
  rw [bud,bud,e.eq_of_nhds,e.deriv_eq,e.deriv.deriv_eq]

lemma Bloom.congr (h:Bloom f c) (e:g =ᶠ[𝓝 0] f) : Bloom g c := by
  have k := h.1.1
  refine ⟨⟨(k.and e.eventually_nhds).mono
    (fun _ hx=>hx.1.congr_of_eventuallyEq hx.2),h.1.2.congr_of_eventuallyEq e.deriv⟩,
    h.2.trans (bud_congr e).symm⟩

lemma Bloom.add (h:Bloom f c)(p:Bloom g d) : Bloom (fun x=>f x+g x) (c+d) := by
  rw [h.2,p.2]
  apply of_der ((h.1.1.and p.1.1).mono
    (fun _ e=> e.1.hasDerivAt.add e.2.hasDerivAt)) (h.1.2.hasDerivAt.add p.1.2.hasDerivAt)
    rfl rfl
  exact (add_div ..).symm

lemma Bloom.mul (h:Bloom f c)(p:Bloom g d) : Bloom (fun x=>f x*g x) (splice c d) := by
  have hf := h.1.ha
  have hg := p.1.ha
  rw [h.2,p.2]
  apply of_der ((h.1.1.and p.1.1).mono
    (fun _ e=> e.1.hasDerivAt.mul e.2.hasDerivAt))
    ((h.1.2.hasDerivAt.mul hg.hasDerivAt).add (hf.hasDerivAt.mul p.1.2.hasDerivAt)) rfl
  · exact add_comm _ _
  simp [splice,bud]
  ring

lemma Bloom.constant (u:ℂ) : Bloom (fun _=>u) ![u,0,0] :=
  Bloom.of_der (Eventually.of_forall fun x=>hasDerivAt_const x u)
    (hasDerivAt_const _ _) rfl rfl (zero_div _).symm

lemma Bloom.scale (h:Bloom f c)(u:ℂ) :
    Bloom (fun x=>u*f x) (u • c) := by
  have e:u • c= splice ![u,0,0] c:=by
    funext i; fin_cases i <;> simp [splice,Pi.smul_apply]
  rw [e]
  exact (Bloom.constant u).mul h

lemma Bloom.sum {ι:Type*}(s:Finset ι) {u:ι→ℝ→ℂ}
    {v:ι→Three ℂ}(H:∀ i∈s,Bloom (u i) (v i)) :
    Bloom (fun x=> ∑ i∈s,u i x) (∑ i∈s,v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp_rw [Finset.sum_empty,show (0:Three ℂ)=![0,0,0] from funext fun i=>by fin_cases i<;>rfl]
    exact constant 0
  | insert a s h ih =>
    simp_rw [Finset.sum_insert h]
    exact (H a (Finset.mem_insert_self ..)).add
      (ih (fun i p => H i (Finset.mem_insert_of_mem p)))

variable {F:ℂ→ℂ}
lemma Bloom.cplx (h:AnalyticAt ℂ F 0) :
    Bloom (fun t=>F t) ![F 0,deriv F 0,(deriv (deriv F) 0)/2] := by
  rw [←Complex.ofReal_zero] at *
  have e := (show Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝 0) (𝓝 0) by
      simpa using Complex.continuous_ofReal.tendsto 0).eventually
    (show ∀ᶠ z in 𝓝 0, AnalyticAt ℂ F z by rw [←Complex.ofReal_zero];exact h.eventually_analyticAt)
  exact of_der (e.mono (fun t a=>a.differentiableAt.hasDerivAt.comp_ofReal))
    h.deriv.differentiableAt.hasDerivAt.comp_ofReal rfl rfl rfl

lemma Bloom.cauchy {R w:ℝ}(hR:0<R) (rR:R≤1)
    (h:DiffContOnCl ℂ F (Metric.ball 0 R))
    (hp:∀ z∈Metric.closedBall 0 R, ‖F z‖≤w) :
    Bud (fun t=>F t) ∧ ∀ i, ‖bud (fun t=>F t) i‖ ≤ w/(R^2) := by
  have v := cplx (h.differentiableOn.analyticAt (Metric.ball_mem_nhds _ hR))
  refine ⟨v.1,?_⟩
  rw [v.bud_eq]
  have hu:= hp _ (Metric.mem_closedBall_self hR.le)
  have hw := (norm_nonneg _).trans hu
  have hm:= fun n=> Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    hR h fun z hz=> hp z (Metric.sphere_subset_closedBall hz)
  intro i;fin_cases i
  · refine hu.trans ?_
    exact le_div_self hw (pow_pos hR _) (pow_le_one₀ hR.le rR)
  · change ‖deriv F 0‖ ≤ _
    have h1:‖deriv F 0‖≤w/R:=by simpa using hm 1
    refine h1.trans (div_le_div_of_nonneg_left hw (pow_pos hR _) ?_)
    simpa only [sq] using (mul_le_of_le_one_left hR.le rR)
  · change ‖deriv (deriv F) 0 / 2‖ ≤ _
    have h2:= hm 2; rw [iteratedDeriv_succ,iteratedDeriv_one] at h2
    rw [norm_div,Complex.norm_ofNat]
    suffices (Nat.factorial 2:ℝ)*w/R^2/2 ≤ w/R^2 from
      (div_le_div_of_nonneg_right h2 (by norm_num)).trans this
    rw [show (Nat.factorial 2:ℝ)=2 from by norm_num [Nat.factorial]]
    ring_nf; exact le_rfl

def ringlet (z:ℂ) : Three ℂ := ![1,z,z*z / 2]

lemma bloom_exp (z:ℂ) : Bloom (fun t=>Complex.exp (z*t)) (ringlet z) := by
  let f:ℂ→ℂ:= fun t=>Complex.exp (z*t)
  have h t:HasDerivAt f (z*f t) t := by
    simpa only [f,mul_one,mul_comm] using ((hasDerivAt_id' t).const_mul z).cexp
  have p := Bloom.cplx ((show Differentiable ℂ f from fun _=>(h _).differentiableAt).analyticAt 0)
  suffices d:f 0=1 ∧ deriv f 0=z ∧ deriv (deriv f) 0=z*z from by rw [d.2.2,d.2.1,d.1] at p;exact p
  have e:f 0=1 := by simp [f]
  have d : deriv f = fun t=>z * f t:=funext fun t=>(h t).deriv
  rw [d, ((h _).const_mul z).deriv];simp [e]
