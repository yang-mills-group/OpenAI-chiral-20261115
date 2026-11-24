import Organdy.Shower
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset



variable {k :ℝ} (p:0<k)
private abbrev veil (k x:ℝ):= 1+x^2/k
include p
lemma veil_one(x:ℝ):1≤veil k x:=le_add_of_nonneg_right (by have :=p; positivity)
lemma veil_pay (x:ℝ): |x| ≤ (1+k)*veil k x:=by
  have t:1+x^2 ≤ (1+k)*veil k x:=by
      have f:=p
      rw [veil,mul_add,add_mul _ k (_^2/k)]
      rw [mul_comm k (_ / _),div_mul_cancel₀ (x^2) f.ne']
      linarith [div_nonneg (sq_nonneg x) p.le]
  exact (show |x| ≤ 1+x^2 by rw [abs_le];constructor <;> nlinarith [sq_nonneg (x+1),sq_nonneg (x-1)]).trans t

include p
lemma mist_fee (x y:ℝ):
 |mist k x-mist k y| ≤ (2*(1+k))*|x-y|:=by
   have u:=veil_one p x
   have v:=veil_one p y
   have h:mist k x-mist k y=(x+y)/(veil k x *veil k y) *(x-y):=by
      unfold mist Regis.Head.Brecht.viewμ
      change x^2/veil k x - y^2/veil k y=_
      have f:veil k x≠0:=by linarith
      have e:veil k y≠0:=by linarith
      field_simp
      ring
   rw [h,abs_mul]
   apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)

   have hx:0<veil k x := by linarith
   have hy:0<veil k y := by linarith
   rw [abs_div, abs_of_pos (mul_pos hx hy), div_le_iff₀ (mul_pos hx hy)]
   let d:= (1+k)*(veil k x*veil k y)
   have c: |x| ≤ d:=
      (veil_pay p x).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx.le v) (by positivity))
   have w: |y| ≤ d:=
      (veil_pay p y).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hy.le u) (by positivity))
   exact (abs_add_le ..).trans ((add_le_add c w).trans_eq (by unfold d; ring))

omit p
variable {ι:Type}[Fintype ι]
lemma palette_fee (a:ι→ℂ){c d:ℝ}(f:ι→ℂ) (h:0≤d)
 (e:∑i,‖a i‖≤c)(u:∀i,a i≠0→ ‖f i‖≤d):‖∑i,a i*f i‖≤c*d:=by
 apply le_trans _ (mul_le_mul_of_nonneg_right e h)
 rw [sum_mul]
 apply (norm_sum_le ..).trans
 apply sum_le_sum;intro i _
 rw [norm_mul]
 by_cases x:a i=0
 · simp [x]
 exact mul_le_mul_of_nonneg_left (u i x) (norm_nonneg _)

lemma palette_re {c d:ℝ}(A:Ink ι)(f:Freq ι→ℝ)(h:0≤d)
 (e:A.qty≤c)(u:∀p:Freq ι,A p.1 p.2.1≠0→ |f p|≤d):
 ‖∑i,write A i*f i‖≤c*d:=
 palette_fee _ _ h ((tally A).trans e) (fun i g=>by rw [Complex.norm_real,Real.norm_eq_abs]; exact u i (active g))

variable {A:Ink ι}{c d:ℝ}
include p
lemma air_limit (h:A.qty≤c)(x): ‖air k A x‖ ≤ c*k:=
  palette_re _ _ p.le h (fun _ _=>abs_mist p _)
lemma haze_gap (h:A.qty≤c)(hd:0≤d)
 (x y:Freq ι→ℝ)(t:∀j,A j.1 j.2.1≠0→ |x j-y j| ≤ d):
 ‖haze (write A) k x - haze (write A) k y‖ ≤ c*(2*(1+k)*d):=by
 simp_rw [haze,←sum_sub_distrib, ←mul_sub, ←Complex.ofReal_sub]
 refine palette_re _ _ (by positivity) h ?_
 exact fun i u=> (mist_fee p ..).trans (mul_le_mul_of_nonneg_left (t i u) (by positivity))

variable {M:Finset ι}
lemma air_gap (h:A.qty ≤ c)(s:A.Within M) (hd:0≤d)
 (x y:ι→ℝ)(v:∀i∈M,|x i - y i|≤d):
 ‖air k A x - air k A y‖≤c*(2*(1+k)*(2*d)):=by
 refine haze_gap p h (by positivity) (read x) _ ?_
 intro i u
 rw [read_sub]
 exact read_limit (v _ (s _ _ u).1) (v _ (s _ _ u).2)

lemma air_low (h:A.qty ≤ c)(s:A.Within M) (hd:0≤d)
 (x:ι→ℝ)(v:∀i∈M,|x i|≤d):
 ‖air k A x‖ ≤ c*(2*d)^2:=by
 refine palette_re _ _ (by positivity) h (fun i u=>?_ )
 rw [abs_of_nonneg (bud_mist p _).1]
 have t:|read x i| ≤ 2*d:= read_limit (v _ (s _ _ u).1) (v _ (s _ _ u).2)
 exact (bud_mist p _).2.2.1.trans (sq_le_sq.mpr (t.trans (le_abs_self _)))

lemma air_sheds (h:A.qty ≤ c)(s:A.Within M) (hd:0≤d)
 (x:ι→ℝ)(v:∀i∈M, |x i|≤d):
 ‖A.gilt x-air k A x‖ ≤ c*((2*d)^4/k):=by
 rw [score,air,haze,←sum_sub_distrib]
 simp_rw [←mul_sub,←Complex.ofReal_pow,←Complex.ofReal_sub]
 refine palette_re _ _ (by positivity) h (fun i u=>?_)
 rw [abs_of_nonneg (sub_nonneg.mpr (bud_mist p _).2.2.1)]
 have z:|read x i|≤ 2*d:=read_limit (v _ (s _ _ u).1) (v _ (s _ _ u).2)
 refine (bud_mist p _).2.2.2.trans (div_le_div_of_nonneg_right ?_ p.le)
 nth_rw 1 [← show (|read x i|)^4=(read x i)^4 from Even.pow_abs (by decide:Even 4) _]
 exact pow_le_pow_left₀ (abs_nonneg _) z _

omit p
open scoped ComplexConjugate
lemma shade_gap {a b x y : ℂ}{u v r s:ℝ}
 (j:‖a-x‖≤u)(l:‖b-y‖≤v)(h:‖b‖≤r)(t:‖x‖≤ s):
 |(a*conj b).re - (x*conj y).re| ≤ u*r+v*s:=by
 apply (Complex.abs_re_le_norm (a*conj b-x*conj y)).trans
 rw [show a*conj b-x*conj y=(a-x)*conj b+ conj (b-y)*x by rw [map_sub];ring]
 apply (norm_add_le ..).trans
 simp only [norm_mul,RCLike.norm_conj]
 exact add_le_add
  (mul_le_mul j h (norm_nonneg _) ((norm_nonneg _).trans j))
  (mul_le_mul l t (norm_nonneg _) ((norm_nonneg _).trans l))
