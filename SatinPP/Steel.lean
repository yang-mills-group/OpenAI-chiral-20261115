import SatinThinJetsAnalytic
import SatinPP.Pearl
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option maxRecDepth 3500
set_option quotPrecheck false
noncomputable section

namespace YM.Quays
open Function Set Filter Metric Topology MeasureTheory InnerProductSpace
open scoped Topology BigOperators InnerProductSpace ComplexOrder Classical NNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open OS Semigroup
variable {X:Hilbert}{j:Axis}{S:OS.Semigroup X j}{n:ℕ}{c:ℝ}{A:Stamp X}


section
variable (S)(A)

def paintAt (z w:ℂ)(e:ℝ):X.Op:= S.F (z-e)*A e e*S.F (w-e)
def paint (z w:ℂ):X.Op:=paintAt S A z w (min z.re w.re/2)
variable {S A} (T:Paid S n c A)
local notation "ψ" =>paint S A
variable {u v e r:ℝ}{z w:ℂ}

open Complex (ofReal_re sub_re)
lemma F_heat (S:OS.Semigroup X j) (h:0<u):S.F (u:ℂ)=S.E u.toNNReal:=SatinJets.branch_eq_heat S u h
lemma below (h:e<z.re):z-e∈inside:=by change 0<(z-(e:ℂ)).re; rw [sub_re,ofReal_re]; exact sub_pos.mpr h

include T
lemma paint_le_eq (p:0<e)(h:e≤r)(a:r<z.re)(b:r<w.re):paintAt S A z w r=paintAt S A z w e:=by
 rcases h.eq_or_lt with h|h; rw [h]
 have l:0<r-e:=sub_pos.mpr h
 have m:(↑(r-e):ℂ)∈inside:= l
 unfold paintAt; rw [T.fits p p h.le h.le]
 rw [show z-e=z-r+ ↑(r-e) by push_cast;abel,show w-e= ↑(r-e)+(w-r) by push_cast;abel,S.pairs (below a) m,S.pairs m (below b),F_heat S l]
 change (S.F _*(S.E _*_ * S.E _)* S.F _)=(S.F _ * S.E _) * _ * (S.E _*S.F _)
 simp only [mul_assoc]


lemma paint_p (p:0<e)(a:e<z.re)(b:e<w.re):ψ z w=paintAt S A z w e:=by
 let t:= min z.re w.re
 have l:0<t:=lt_min (p.trans a) (p.trans b)
 unfold paint
 rcases le_total e (t/2) with h|h
 · exact paint_le_eq T p h ((half_lt_self l).trans_le (min_le_left ..))
      ((half_lt_self l).trans_le (min_le_right ..))
 exact (paint_le_eq T (half_pos l) h a b).symm

lemma paint_real (p:0<u)(h:0<v):ψ (u:ℂ) (v:ℂ)=A u v:=by
 let t:=min u v; let e:=t/2
 have d:0<t:=lt_min p h
 have ht:0<e:=half_pos d
 have a:e<(u:ℂ).re:=(half_lt_self d).trans_le (min_le_left ..)
 have b:e<(v:ℂ).re:=(half_lt_self d).trans_le (min_le_right ..)
 rw [paint_p T ht a b]
 unfold paintAt
 rw [← Complex.ofReal_sub,← Complex.ofReal_sub,
    F_heat S (sub_pos.mpr (show e<u from a)),F_heat S (sub_pos.mpr (show e<v from b))]
 exact (T.fits ht ht a.le b.le).symm
omit T in
lemma widths_ink (a:z∈inside)(b:w∈inside):
 ∃ e:ℝ, 0<e ∧ e<z.re ∧ e<w.re:=
 let t:=lt_min (show 0<z.re from a) (show 0<w.re from b)
 ⟨_, half_pos t,(half_lt_self t).trans_le (min_le_left ..),(half_lt_self t).trans_le (min_le_right ..)⟩

variable {x:ℂ}
lemma paint_left (a:z∈inside)(b:w∈inside)(c:x∈inside):
 ψ (x+z) w=S.F x*ψ z w:=by
 obtain ⟨e,h,k,l⟩:=widths_ink a b
 have t:e<(x+z).re:=k.trans (lt_add_of_pos_left z.re (show 0<x.re from c))
 rw [paint_p T h t l,paint_p T h k l]
 unfold paintAt
 rw [add_sub_assoc,S.pairs c (below k)]
 change (S.F x * _)*_ * _=_; simp [mul_assoc]

lemma paint_right (a:z∈inside)(b:w∈inside)(c:x∈inside):
 ψ z (w+x)=ψ z w*S.F x:=by
 obtain ⟨e,h,k,l⟩:=widths_ink a b
 have t:e<(w+x).re:=l.trans (lt_add_of_pos_right w.re (show 0<x.re from c))
 rw [paint_p T h k t,paint_p T h k l]
 unfold paintAt
 rw [show w+x-(e:ℂ)=w-e+x by abel,S.pairs (below l) c]
 change _*(_*S.F x)=_; simp [mul_assoc]


lemma paint_jacket (a:z∈inside)(b:w∈inside)(p:0≤u)(h:0≤v):
 ψ (u+z) (w+v)=jacket S u v (ψ z w):=by
 have h₁:ψ (u+z) w=S.E u.toNNReal * ψ z w:=by
   rcases p.eq_or_lt with r|r
   · rw [←r,Real.toNNReal_zero,S.eZero,Complex.ofReal_zero,zero_add]; rfl
   · rw [paint_left T a b (show (u:ℂ)∈inside from r),F_heat S r]
 rcases h.eq_or_lt with r|r
 · change _=S.E _ *_ * S.E v.toNNReal
   rw [←r,Real.toNNReal_zero,S.eZero,Complex.ofReal_zero,add_zero,h₁]; rfl
 · have t:↑u+z∈inside:=add_pos_of_nonneg_of_pos p a
   rw [paint_right T t b (show (v:ℂ)∈inside from r),F_heat S r,h₁]; rfl

lemma paint_cost (p:0<e)(h:e≤1)(a:e<z.re)(b:e<w.re):
  ‖ψ z w‖≤ c/e^n:=by
 rw [paint_p T p a b]
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.norm_row (below b))).trans
    ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (S.norm_row (below a))).trans (T.le p h))))


lemma analyticAt_paint {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E] {y:E}{f g:E→ℂ}
   (a:f y∈inside)(b:g y∈inside)(h:AnalyticAt ℂ f y)(k:AnalyticAt ℂ g y):
   AnalyticAt ℂ (fun t=>ψ (f t) (g t)) y:=by
 obtain ⟨e,t,p,q⟩:=widths_ink a b
 have d: AnalyticAt ℂ (fun t=>paintAt S A (f t) (g t) e) y:=
   (((S.localHeat _ (below p)).comp (f:=fun t=>f t-(e:ℂ)) (h.sub (analyticAt_const (v:=(e:ℂ))))).mul
       (analyticAt_const (v:=A e e))).mul
    ((S.localHeat _ (below q)).comp (f:=fun t=>g t-(e:ℂ)) (k.sub (analyticAt_const (v:=(e:ℂ)))))
 refine d.congr ?_
 filter_upwards [(Complex.continuous_re.continuousAt.comp h.continuousAt).eventually (lt_mem_nhds p),
    (Complex.continuous_re.continuousAt.comp k.continuousAt).eventually (lt_mem_nhds q)] with x u v
 exact (paint_p T t u v).symm

lemma continuousAt_paint {E:Type*}[TopologicalSpace E] {y:E}{f g:E→ℂ}
   (a:f y∈inside)(b:g y∈inside)(h:ContinuousAt f y)(k:ContinuousAt g y):
   ContinuousAt (fun t=>ψ (f t) (g t)) y:=
 ((analyticAt_paint (y:=(f y,g y)) T (f:=Prod.fst) (g:=Prod.snd) a b analyticAt_fst analyticAt_snd).continuousAt).comp (f:=fun t=>(f t,g t)) (h.prodMk k)

omit T
end
variable (S)(A)
def flick (z w:ℂ):X.Op:=deriv (fun t=>paint S A (z+t) (w-t)) 0
/-- Center time derivative. -/
def flicks: Stamp X:=fun u v=>flick S A u v
variable {S A}{z w:ℂ} (T:Paid S n c A)
local notation "ψ" =>paint S A
include T
lemma hasFlick (a:z∈inside)(b:w∈inside):
  HasDerivAt (fun t=>ψ (z+t) (w-t)) (flick S A z w) 0:=
    (analyticAt_paint T (f:=fun t=>z+t) (g:=fun t=>w-t)
       ((add_zero z).symm ▸ a) ((sub_zero w).symm ▸ b)
       (analyticAt_const.add analyticAt_id) (analyticAt_const.sub analyticAt_id)).differentiableAt.hasDerivAt

lemma flicks_fit {u v s t:ℝ}(a:0<s)(b:0<t)(p:s≤u)(q:t≤v):
    flicks S A u v=jacket S (u-s) (v-t) (flicks S A s t):=by
    let K:X.Op→L[ℂ]X.Op:=(jacket S (u-s) (v-t)).mkContinuous 1 (fun A=> by rw [one_mul]; exact jacket_cost ..)
    refine (hasFlick T (show (u:ℂ)∈inside from a.trans_le p)
      (show (v:ℂ)∈inside from b.trans_le q)).unique ?_
    have e:=hasFlick T (show (s:ℂ)∈inside from a) (show (t:ℂ)∈inside from b)


    let g:=fun z:ℂ=>ψ (s+z) (↑t-z)
    have h: HasDerivAt (K ∘ g) (K _) 0:= K.hasFDerivAt.comp_hasDerivAt (f:=g) 0 e
    refine h.congr_of_eventuallyEq ?_
    have a': ↑s+(0:ℂ)∈inside:=by rw [add_zero];exact a
    have b': ↑t-(0:ℂ)∈inside:=by rw [sub_zero]; exact b
    filter_upwards [((continuous_const.add continuous_id).continuousAt.eventually
       (open_inside.mem_nhds a')),((continuous_const.sub continuous_id).continuousAt.eventually
       (open_inside.mem_nhds b'))] with x h₁ h₂
    convert paint_jacket T h₁ h₂ (sub_nonneg.mpr p) (sub_nonneg.mpr q) using 1
    simp only [Pi.add_apply,Pi.sub_apply,id_eq]
    rw [Complex.ofReal_sub,Complex.ofReal_sub,←add_assoc,sub_add_cancel,
        add_comm (↑t-x),show ((v:ℂ)-t)+(↑t-x)=v-x by abel]
    rfl


lemma flick_cost (u:ℝ)(a:0<u)(b:u≤1):
    ‖flick S A u u‖≤ c * 2^n * 4/u^(n+1):=by
 let t:=u/2
 have hi(y:ℂ)(h:y∈ closedBall (0:ℂ) (u/4)):
    t<(u+y).re ∧ t<(u-y).re := by
    have e:=abs_le.mp ((Complex.abs_re_le_norm y).trans (mem_closedBall_zero_iff.mp h))
    simp only [Complex.add_re,Complex.sub_re, Complex.ofReal_re,t]
    constructor <;> linarith
 have e:=half_pos a
 let f:=fun y:ℂ=>ψ (u+y) (u-y)
 have q: DifferentiableOn ℂ f (closedBall 0 (u/4)):= fun y h=>
    (analyticAt_paint T (f:=fun t=>u+t) (g:=fun t=>u-t)
       (e.trans (hi y h).1) (e.trans (hi y h).2)
       (analyticAt_const.add analyticAt_id) (analyticAt_const.sub analyticAt_id)).differentiableAt.differentiableWithinAt

 have r:= Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
   (C:=c/(u/2)^n) (by positivity : 0<u/4)
   (q.diffContOnCl_ball (Set.Subset.refl _))
   (fun y h=>let h':= hi y (sphere_subset_closedBall h)
             paint_cost T e ((half_lt_self a).le.trans b) h'.1 h'.2)
 refine r.trans_eq ?_
 rw [div_pow,pow_succ,div_div_eq_mul_div,div_div_eq_mul_div]
 ring


lemma paid_flick : Paid S (n+1) (c*2^n*4) (flicks S A):=by
 have h:=T.pos; exact ⟨by positivity, flicks_fit T, fun a b=>flick_cost T _ a b⟩

end YM.Quays

