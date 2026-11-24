import YM.SU5.Reconstruction.Sleet.Prism
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
/-! # Log of quadrant budget -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter MeasureTheory Complex Sail Metric
open scoped Topology NNReal Real Classical ComplexConjugate

def optimistic : Set ℂ:= {z|0<z.re}
lemma current_open:IsOpen optimistic:= isOpen_lt continuous_const continuous_re
lemma current_conn:IsPreconnected optimistic:= (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected
lemma assigned_ground {v:ℝ}(w:0<v): (v:ℂ)∈ optimistic:= by simp [optimistic,w]
lemma assigned_ne {z:ℂ}(p:z∈ optimistic): z≠0:=fun h=>by rw [h] at p; simp [optimistic] at p

def brim:=Real.pi/2
lemma piB : 0<brim:= by unfold brim; positivity
def Towerbound (x y:ℂ):= x∈ optimistic ∧ y∈ optimistic ∧ |arg x|+|arg y|<brim
lemma bπ (x:ℂ) (p:x∈ optimistic):|arg x|<brim:= abs_arg_lt_pi_div_two_iff.mpr (Or.inl p)
private lemma fit_arg(x y:ℂ)(p:x∈optimistic)(q:y∈optimistic): arg (x*y)=arg x + arg y:= by
 obtain ⟨h,t⟩:= abs_lt.mp (bπ x p); obtain ⟨w,v⟩:= abs_lt.mp (bπ y q)
 apply arg_mul (assigned_ne p) (assigned_ne q); unfold brim at *; constructor <;>linarith
lemma deck {R:ℝ}{z:ℂ}(p: ‖z‖<R):Towerbound ((R:ℂ)+z) ((R:ℂ)-z):= by
 let x:=(R:ℂ)+z; let y:=(R:ℂ)-z
 obtain ⟨h,t⟩:= abs_lt.mp ((Complex.abs_re_le_norm z).trans_lt p)
 have u:x ∈optimistic:=by simp only [x,optimistic,mem_setOf_eq,add_re,ofReal_re]; linarith
 have v:y∈ optimistic:=by simp only [y,optimistic,mem_setOf_eq,sub_re,ofReal_re]; linarith
 have v':conj y∈ optimistic:=by simpa only [optimistic, mem_setOf_eq,conj_re] using v
 refine ⟨u,v,?_⟩; change |arg x|+|arg y|<brim
 have he : z.re^2+z.im^2<R^2:=by rw [show z.re^2+z.im^2=normSq z from by simp [normSq_apply,pow_two], normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
 have k:x*y∈ optimistic:=by simp only [optimistic,mem_setOf_eq,mul_re,x,y,add_re,sub_re,ofReal_re,add_im,sub_im,ofReal_im]; nlinarith
 have k':x*conj y∈ optimistic:=by simp only [optimistic,mem_setOf_eq,mul_re,conj_re,conj_im,x,y,add_re,sub_re,ofReal_re,add_im,sub_im,ofReal_im]; nlinarith
 have ha:arg y≠Real.pi:=by have hv:arg y<brim:= (abs_lt.mp (bπ _ v)).2; unfold brim at hv; nlinarith [Real.pi_pos]
 -- explicitly get inequalities
 have hx:|arg x+arg y|<brim:= by rw [← fit_arg _ _ u v]; exact bπ _ k
 have hy:|arg x+ -arg y|<brim:=by rw [show -arg y=arg (conj y) from (by simp [arg_conj,ha]),← fit_arg _ _ u v']; exact bπ _ k'
 obtain ⟨hx1,hx2⟩:=abs_lt.mp hx; obtain ⟨hy1,hy2⟩:=abs_lt.mp hy; rcases le_or_gt 0 (arg x) with u1|u1 <;> rcases le_or_gt 0 (arg y) with v1|v1 <;>
   (first| rw [abs_of_nonneg u1]| rw [abs_of_neg u1]) <;> (first|rw [abs_of_nonneg v1]|rw [abs_of_neg v1]) <;> linarith

structure Squall (C:ℝ)(F:ℝ→ℂ→ℂ)(G:ℂ→ℝ→ℂ): Prop where
 usable (x:ℝ) (h:0<x): AnalyticOnNhd ℂ (F x) optimistic
 guides (y:ℝ)(h:0<y): AnalyticOnNhd ℂ (fun t=>G t y) optimistic
 rent(x:ℝ)(h:0<x):∀ y:ℂ,y∈optimistic→ ‖F x y‖≤ C
 charge(y:ℝ)(h:0<y):∀ x:ℂ,x∈optimistic → ‖G x y‖≤ C
 meets(x y:ℝ)(p:0<x)(q:0<y): F x y=G x y
 comes(y:ℂ)(h:y∈ optimistic):ContinuousOn (fun x=>F x y) (Set.Ioi 0)

variable {F:ℝ→ℂ→ℂ}{G:ℂ→ℝ→ℂ}{C:ℝ}(κ:Squall C F G)

private lemma shelter (z:ℂ)(p:z∈ slit brim): Complex.exp z∈ optimistic := by simp only [optimistic,mem_setOf_eq,exp_re]; exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (show |z.im|< _ from p))) -- tune deff
private def dyed (F:ℝ→ℂ→ℂ)(x:ℝ)(y:ℂ):= F (Real.exp x) (Complex.exp y)
private def pointed (G:ℂ→ℝ→ℂ)(x:ℂ)(y:ℝ):= G (Complex.exp x) (Real.exp y)
include κ
private lemma active: Gust brim C (dyed F) (pointed G):= {
 pos:=piB
 usable := fun x z p=> (κ.usable (Real.exp x) (Real.exp_pos _) _ (shelter z p)).comp analyticAt_cexp
 guides:= fun y z p=> (κ.guides _ (Real.exp_pos y) _ (shelter z p)).comp analyticAt_cexp
 rent:= fun x z p=> κ.rent _ (Real.exp_pos x) _ (shelter z p)
 charge:= fun y z p=> κ.charge _ (Real.exp_pos y) _ (shelter z p)
 meets:= fun x y=>by simpa [dyed,pointed, ←Complex.ofReal_exp] using κ.meets _ _ (Real.exp_pos x) (Real.exp_pos y)
 comes:= fun y h=> (κ.comes (Complex.exp y) (shelter y h)).comp_continuous Real.continuous_exp (fun i=> Real.exp_pos _)
 }

def sally(F:ℝ→ℂ→ℂ)(x y:ℂ):= hatch (dyed F) (Complex.log x) (Complex.log y)
lemma rocket {x y:ℂ}(h:Towerbound x y): ‖sally F x y‖≤ C:=hatch_power (active κ) _ _ (by
  simpa only [chamber, log_im] using h.2.2)
lemma accountCurve {W:Set ℂ}(h:IsOpen W){f g:ℂ→ℂ}(p:∀ z∈W,Towerbound (f z) (g z))(a:AnalyticOnNhd ℂ f W)(b:AnalyticOnNhd ℂ g W):AnalyticOnNhd ℂ (fun z=>sally F (f z) (g z)) W := hatch_curve (active κ) h (f:=Complex.log∘ f) (g:=Complex.log∘g) (fun z Z=> by simpa only [Function.comp_apply, chamber, log_im] using (p z Z).2.2) (fun z Z=>(a z Z).clog (Or.inl (p z Z).1)) (fun z Z=> (b z Z).clog (Or.inl (p z Z).2.1))
lemma sally_land(x:ℝ)(p:0<x)(y:ℂ)(q:y∈optimistic): sally F x y= F x y:=by
 unfold sally; rw [← Complex.ofReal_log p.le, show hatch _ _ _ = dyed F (Real.log x) (Complex.log y) from hatch_top (active κ) _ (show Complex.log y∈ slit brim from by simpa only [slit,mem_setOf_eq,log_im] using bπ _ q),dyed,Real.exp_log p,Complex.exp_log (assigned_ne q)]
lemma sally_fly(x:ℂ)(p:x∈optimistic)(y:ℝ)(q:0<y): sally F x y=G x y:=by
 unfold sally; rw [← Complex.ofReal_log q.le, show hatch (dyed F) (log x) ↑(Real.log y) = pointed G (log x) (Real.log y) from (hatch_lateral (active κ) (Real.log y) (show Complex.log x∈ slit brim from by simpa only [slit,mem_setOf_eq,log_im] using bπ _ p)), pointed, Real.exp_log q, Complex.exp_log (assigned_ne p)]
end YM.ConePrice.Storm
