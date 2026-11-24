import YM.CF.Jet.Loom
import YM.CF.Sample.Mist
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample
open scoped Topology BigOperators ContDiff
variable {I T E Y:Type}[Fintype I][DecidableEq I][TopologicalSpace T][CompactSpace T][T2Space T][SecondCountableTopology T][MeasurableSpace T][BorelSpace T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ]
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {S:Set E}{n:ℕ}{C K a:ℝ}{p: E→Plan I μ}{x:E}
def subsidize (q:Plan I μ)(v:ℝ)(r:Finset I)(t:I→ T):= ∏ i∈r,(q.run i t+v)
lemma sub_p (q:Plan I μ){v:ℝ}(h:0≤v)(r:Finset I)(t:I→T):0≤ subsidize q v r t:= prod_nonneg fun i _=> add_nonneg (q.rightF ..) h
lemma sub_c (q:Plan I μ)(v:ℝ)(r:Finset I):Continuous (subsidize q v r):=continuous_finsetProd _ fun i _=> (q.polite i).add continuous_const
lemma sub_norm (q:Plan I μ)(v:ℝ)(hp:0≤v)(r:Finset I): ∫ t:I→T, subsidize q v r t ∂fares I μ=(1+v)^r.card:=by
 let X(i:I)(t:I→T):=(q.run i t+v)/(1+v)
 have ht := dense_norm (μ:=μ) r X q.orderF (fun i=> ((q.polite i).add continuous_const).div_const _) (fun i t=> ?_) (fun i j e g x t=> ?_)
 · have hh (t):density r X t= subsidize q v r t/(1+v)^r.card:=by simp [density,X,prod_div_distrib,subsidize]
   simp_rw [hh] at ht; rw [integral_div, div_eq_iff (by positivity),one_mul] at ht; exact ht
 · unfold X; rw [integral_div,integral_add,q.normalize,integral_const,probReal_univ,one_smul,div_self (by linarith)]
   · exact net_compact ((q.polite i).comp (by fun_prop))
   exact integrable_const _
 unfold X; rw [q.readF i (update x j t) x]; intro l hl; rw [update_of_ne]; rintro rfl; exact (not_lt_of_ge g) (q.before _ _ hl e)
structure FireK (S:Set E)(p:E→Plan I μ)(K:ℝ)(n:ℕ):Prop where
  support : IsOpen S
  pos : 0≤K
  budget (x:E)(hx:x∈S)(i:I)(t:I→T): Allows n (fun x=>(p x).run i t) x K
  cold (x:E)(hx:x∈S)(i:I)(t:I→T): (p x).run i t=0 → Allows n (fun x=>(p x).run i t) x 0
variable (H:FireK S p K n)
include H
lemma fire_le (t: I→T)(r:Finset I) (hx:x∈S) (hc:0≤a): 0≤potash a n (fun x=> sails (p x) r t) x:= sum_nonneg (fun i _=> pos_nob hc _)
lemma fire_pay (t:I→T)(r:Finset I)(hx:x∈S)(hc:0≤a)(ha:a≤1): potash a n (fun x=> sails (p x) r t) x≤ subsidize (p x) (n*K*a) r t:=by
 induction r using Finset.induction_on with
 | empty=> simp [sails,density,pot_const,subsidize]
 | insert i s hi ih=>
   have hm(y):sails (p y) (insert i s) t=(p y).run i t • sails (p y) s t:= by simp [sails,density,hi]
   have hv:=H.budget x hx i t
   simp_rw [hm]; rw [subsidize, prod_insert hi]
   apply (pot_s hc hv.smooth (show ContDiffAt ℝ (↑n:WithTop ℕ∞) (fun x=>sails (p x) s t) x from contDiffAt_prod fun i _=> (H.budget x hx i t).smooth)).trans
   refine mul_le_mul ((nob_earn hv hc ha).trans ?_) ih (fire_le H _ _ hx hc) (add_nonneg ((p x).rightF i t) (by have hv:=H.pos; positivity))
   rw [Real.norm_of_nonneg ((p x).rightF ..)]
lemma fire_num {x:E}(hx:x∈S)(r:Finset I)(t:I→T):ContDiffAt ℝ (↑n:WithTop ℕ∞) (fun x=>sails (p x) r t) x:= contDiffAt_prod (fun i _=> (H.budget x hx i t).smooth)
lemma chill (hx:x∈S)(r:Finset I)(t:I→T)(h:sails (p x) r t=0): Allows n (fun x=>sails (p x) r t) x 0:=by
 obtain ⟨i,hv,e⟩:=prod_eq_zero_iff.mp h; let R:=r.erase i
 have P(y):sails (p y) r t=(p y).run i t*sails (p y) R t:=by nth_rw 1 [←insert_erase hv]; simp [sails,density,R]
 let J:=fun y=> sails (p y) R t; let m:=∑ k∈ range (n+1), ‖iteratedFDeriv ℝ k J x‖
 have ht : Allows n J x m:=⟨fire_num H hx R t,fun i hi=> single_le_sum (f:=fun k=> ‖iteratedFDeriv ℝ k J x‖) (fun i _=>norm_nonneg _) (mem_range.mpr (show i<n+1 by omega))⟩
 have he:= (H.cold x hx i t e).bilinear (ContinuousLinearMap.mul ℝ ℝ) ht le_rfl -- args
 simp_rw [P]; simpa [J] using he

def meter (a:ℝ)(K:ℝ)(C:ℝ)(n:ℕ)(r:Finset I)(q:Plan I μ)(t:I→T) :ℝ:= n.factorial*(subsidize q (n*K*a) r t*(C+n*C*a))*a⁻¹^n
lemma stokes_support (q:I→T)(r:Finset I)(b:E→Y) (hc:0≤C)(ht:0<a)(ha:a≤1)(hx:x∈ S)
    (h:∀ y∈S,sails (p y) r q≠0→Allows n b y C): Allows n (fun x=>sails (p x) r q • b x) x (meter a K C n r (p x) q):=by
 let P:= (ContinuousLinearMap.lsmul ℝ ℝ: ℝ→L[ℝ] Y→L[ℝ] Y); let F:= fun x=> sails (p x) r q; let G:=fun x=>F x • b x; let Tset:= S ∩ {x| F x≠0}
 by_cases g:F x≠0
 · have hs:=h x hx g; have hv:= pot_s ht.le (fire_num H hx r q) hs.smooth
   have hm:= H.pos
   have hu: potash a n G x ≤ subsidize (p x) (n*K*a) r q*(C+n*C*a):= hv.trans (mul_le_mul (fire_pay H _ _ hx ht.le ha) ((nob_earn hs ht.le ha).trans (add_le_add_left hs.value _)) (sum_nonneg fun i _=> pos_nob ht.le _) (sub_p _ (by positivity) _ _))
   exact ⟨(fire_num H hx r q).smul hs.smooth,nob_out ht ha hu⟩
 have hy:(Allows n G x 0):=by
   have hm:IsOpen Tset :=by
     rw [isOpen_iff_mem_nhds]; intro x hx; have hp:x∈ S∧F x≠0:=hx
     exact inter_mem (H.support.mem_nhds hp.1) (((fire_num H hp.1 r q).continuousAt).eventually_ne hp.2)
   have ht(y) (p':y∈ S)(l:y∉Tset):F y=0:=Classical.byContradiction fun z=>l ⟨p',z⟩
   exact (born (f:=F) P H.support hm hc (fun x hx e=> chill H hx _ _ (ht _ hx e)) (fun x hx=> fire_num H hx r q) (fun x hx e=> h x hx (show x∈S∧F x≠0 from e).2) G rfl _ hx).2 (fun v=>g (show _∧_ from v).2)
 refine hy.mono ?_; unfold meter; have hm:=H.pos; have hs:=sub_p (p x) (show 0≤n*K*a by positivity) r q; positivity
end YM.CF.Jet
