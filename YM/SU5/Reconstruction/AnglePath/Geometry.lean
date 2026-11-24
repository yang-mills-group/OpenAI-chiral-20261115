import YM.SU5.Reconstruction.AnglePath.Budget
import YM.SU5.Reconstruction.AnglePath.Boost
import Mathlib.Analysis.Complex.Hadamard
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

namespace Bank
open Complex
local notation "π"=> Real.pi
variable (s t u e:ℝ)
noncomputable def cs (t:ℝ):ℝ:= Real.cos (π*t/2)
noncomputable def sn(t:ℝ):ℝ:= Real.sin (π*t/2)
noncomputable def tau:ℝ:= s * cs u + t * sn u
noncomputable def xi :ℝ:=t * cs u - s * sn u
noncomputable def rod(z:ℂ):ℂ:=exp ((e:ℂ)*I*π*z/2)
noncomputable def baton(z:ℂ):ℂ:= Picket.stroke e s t * rod e z
private lemma fees {x:ℂ} : rod e x = rod e (x.re:ℝ) * ↑(lengthen e (x.im/2)) := by
    unfold lengthen rod; push_cast; rw [←exp_add]; congr 1; nth_rw 1 [← Complex.re_add_im x]; ring_nf; simp; ring -- tune nth
lemma realTurn (v:e=1∨e=-1): baton s t e (u:ℂ)=Picket.stroke e (tau s t u) (xi s t u):=by
 unfold baton Picket.stroke
 have h:rod e (u:ℂ)= (cs u:ℂ)+(↑(e*sn u):ℂ)*I:=by unfold cs sn rod; rcases v with v|v <;> rw [v] <;> apply Complex.ext <;> simp [Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,-Complex.ofReal_cos,-Complex.ofReal_sin,neg_div] -- tune real_neg_div
 rw [h]; rcases v with v|v <;> subst e <;> unfold tau xi <;> push_cast <;> ring_nf <;> simp <;> ring
lemma imaginaryTurn (u:ℝ): baton s t e ((u:ℂ)*I)=Picket.stroke e (s:ℂ) (t:ℂ) * ↑(lengthen e (u/2)):=by unfold baton; rw [fees]; simp [rod] -- tune lengthen
variable (p:0 ≤ s)(q:0≤t)
private lemma π_size {u:ℝ}(h:u∈ Icc (0:ℝ) 1): 0≤ π*u/2 ∧ π*u/2≤π/2:=⟨by have H:= h.1; positivity,by have H:=h.2; nlinarith [Real.pi_pos]⟩ -- include p q accidental with s t binder; remove
include p q
lemma ratePos {u:ℝ}(h:u∈Icc (0:ℝ) 1): 0≤ tau s t u:=by
 have v:=π_size h
 exact add_nonneg (mul_nonneg p (Real.cos_nonneg_of_mem_Icc ⟨(by linarith [Real.pi_pos,v.1]),v.2⟩)) (mul_nonneg q (Real.sin_nonneg_of_nonneg_of_le_pi v.1 (v.2.trans (by linarith [Real.pi_pos])))) -- lem names
lemma ratePlus(x:0<s+t) {u:ℝ}(h:u∈ Ioo (0:ℝ) 1):0<tau s t u:=by
 have H:= h.1; have he: π*u/2<π/2:=by have hu:=h.2; nlinarith [Real.pi_pos]
 have hc:0<cs u:= Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],he⟩
 have hb:0< sn u:= Real.sin_pos_of_pos_of_lt_pi (by positivity) (he.trans (by linarith [Real.pi_pos])); unfold tau; rcases eq_or_lt_of_le q with z|z
 · rw [←z] at x ⊢; simp only [zero_mul,add_zero] at x ⊢; positivity
 positivity
variable (v:e=1∨e=-1)
include v
lemma room(z:ℂ)(h:z∈scroll):0≤(baton s t e z).re:=by unfold baton; rw [fees,←mul_assoc]; change 0 ≤(baton s t e (z.re:ℂ)* _).re; rw [realTurn _ _ _ _ v]; simp only [mul_re,ofReal_im,mul_zero, sub_zero,ofReal_re,Picket.contour_re]; have he:= ratePos s t p q h; unfold lengthen; positivity
lemma suite(z:ℂ)(h:z∈income)(x:0 <s+t):0<(baton s t e z).re:=by unfold baton; rw [fees,←mul_assoc]; change 0 <(baton s t e (z.re:ℂ)* _).re; rw [realTurn _ _ _ _ v]; simp only [mul_re,ofReal_im,mul_zero, sub_zero,ofReal_re,Picket.contour_re]; have he:= ratePlus s t p q x h; unfold lengthen; positivity
omit p q v
open Complex.HadamardThreeLines
-- cache Hadamard.One-edge identity. Need not positive on right boundary.
theorem entangles(f:ℂ→H)(u:ℝ)(h:∀ z∈scroll,‖f z‖≤u)(P:AnalyticOnNhd ℂ f income)(q:ContinuousOn f scroll)(x:∀ i:ℝ,f ((i:ℂ)*I)=0) (z:ℂ)(y:z∈scroll): f z=0:=by
 let g:= fun z:ℂ=> ‖f z‖; have h1: closure income=scroll:= by change closure (re ⁻¹' Ioo (0:ℝ) 1)= re ⁻¹' Icc (0:ℝ) 1; rw [closure_preimage_re,closure_Ioo zero_ne_one]
 have h2: DiffContOnCl ℂ f income:=⟨fun x hx=> (P x hx).differentiableAt.differentiableWithinAt,h1.symm ▸ q⟩
 have hy : BddAbove ((norm ∘ f) '' scroll):= ⟨u, fun y ⟨z,a,p⟩=> p ▸ h z a⟩
 have h0 (z): z∈ income → g z≤0:= by
    intro o; have hv : ‖f z‖ ≤ (0:ℝ) ^(1-z.re)*u ^z.re:= by
       apply norm_le_interp_of_mem_verticalClosedStrip₀₁' f (deeply o) h2 hy
       · intro w a; have r:w=(w.im:ℂ)*I:=by change w.re=0 at a; nth_rw 1 [←w.re_add_im]; rw [a]; simp
         nth_rw 1 [r]; simp [x]
       intro w a; apply h; change w.re=1 at a; simp [scroll,a]
    unfold g; rwa [Real.zero_rpow (sub_pos.mpr o.2).ne',zero_mul] at hv
 apply norm_eq_zero.mp; exact le_antisymm (le_on_closure h0 (show ContinuousOn g (closure income) from h2.2.norm) continuousOn_const (h1.symm ▸ y)) (norm_nonneg _) -- tune args
end Bank
end YM.CrossedFrame.Cardio
