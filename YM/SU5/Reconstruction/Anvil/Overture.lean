import YM.SU5.Reconstruction.Anvil.Radial
/-! # Build contour. Each axis acquires proper paying (i.e.
 including boundary poles where two sectors may be both lit.) -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Metric Filter
open scoped Topology BigOperators
local notation "π"=> Real.pi
local notation "ℭ"=> circleMap 0 1
variable {n:ℕ}
private lemma gentle {ι:Type*} {β:Type*} [TopologicalSpace β] {x:β} {f:ι→β→ℂ}(s: Finset ι) (p:∀ i∈s,ContinuousAt (f i) x): ContinuousAt (fun z=> ∏ i∈s,f i z) x:= tendsto_finsetProd s p
namespace Score
open Finset
variable (C:Score n) (u:ℝ) (v:u∈ Set.Ico (0:ℝ) 1)
variable (A:Spin n→ℝ) (R:ℝ)
def tenor (z:ℂ) : ℂ:= ∏ i, (sail (C.post i) u z)⁻¹
def siesta (z:ℂ) : ℂ := (R:ℂ)*(∏ i,cove (C.post i) z)*(C.tenor u z)
-- A(i) center fraction = a_i/κ
local notation "Λ" i:max=> (Finset.univ.erase i).erase (shift i)
def glisten (i:Spin n)(z:ℂ) :ℂ:= (R:ℂ)*(A i:ℝ)*C.jet i z*(∏ k∈Λ i,cove (C.post k) z)*C.tenor u z
local notation "Z"=> C.siesta u R
local notation "B"=> C.glisten u A R
local notation "T"=> C.tenor u
@[simp] lemma tenor_zero : C.tenor u 0=1:=by simp [sail,tenor,draft]
@[simp] lemma siesta_zero : C.siesta u R 0=(R:ℂ):=by simp [siesta,cove,draft]
@[simp] lemma glisten_zero (i:Spin n) : B i 0=(R*(A i):ℝ):=by simp [glisten,jet,radial,cove,draft] -- tweak
variable (i j:Spin n)
include v
variable {p:ℂ}(e:p∈Pane)
include e
lemma tenor_pays : ContinuousAt T p:=by
 unfold tenor; exact gentle _ fun i h=> (sail_cont (C.post_rim i) e v).inv₀ (sail_pos (C.post_rim i) e v)
lemma tenor_h : DifferentiableAt ℂ T p:=by
 unfold tenor; exact DifferentiableAt.fun_finsetProd (fun i h=>(sail_hol (C.post_rim i) e v).inv (sail_pos (C.post_rim i) e v)) -- name
lemma siesta_cont : ContinuousAt Z p:= (continuousAt_const.mul (gentle _ fun i t=> cove_cont (C.post_rim i) e)).mul (C.tenor_pays u v e)
omit e
lemma siesta_hol (h:p∈Well):DifferentiableAt ℂ Z p:= by
 unfold siesta; exact ((differentiableAt_const _).mul (DifferentiableAt.fun_finsetProd (fun i _=> cove_hol (C.post_rim i) h))).mul (C.tenor_h u v (ball_subset_closedBall h)) -- fun Finset
include e
lemma glisten_cont : ContinuousAt (B i) p:=by unfold glisten; exact ((continuousAt_const.mul (show ContinuousAt (C.jet i) p from by unfold jet radial; fun_prop )).mul (gentle _ (fun i t=> cove_cont (C.post_rim i) e))).mul (C.tenor_pays u v e)
omit e
lemma glisten_hol (h:p∈Well):DifferentiableAt ℂ (B i) p:=by unfold glisten; exact (((differentiableAt_const _).mul (show DifferentiableAt ℂ (C.jet i) p from by unfold jet radial; fun_prop)).mul (DifferentiableAt.fun_finsetProd (fun i _=> cove_hol (C.post_rim i) h))).mul (C.tenor_h u v (ball_subset_closedBall h))
omit v
lemma siesta_repr (p:ℂ) : Z p = (R:ℂ)*mantilla C.post u p:= by
 unfold siesta mantilla winds tenor; simp only [Finset.prod_div_distrib,Finset.prod_inv_distrib]; ring -- div ring
lemma regrow {t:ℝ}(e:t∈ Set.Ioo (C.past j) (C.future j)): B i (ℭ t)= Z (ℭ t)*C.represents i (A i) (ℭ t):= by
 unfold glisten siesta represents; rw [←prod_erase_mul _ _ (Finset.mem_univ i),←prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨C.cycle_sep i,Finset.mem_univ (shift i)⟩)]
 have g (k): cove (C.post k) (ℭ t)≠0:= cove_pos (C.post_rim k) (C.not_post t e k); have e1:=g i; have e2:=g (shift i); field_simp

variable (η:ℝ)(hA:∀ i,(A i)^2*(1+Real.cos (C.span i))=η*Real.sin (C.span i))(S:∑ i, (A i)^2=1) (Tg:∀ i,0<A i)
variable (r:ℝ)(pR:0<R)
variable (g:∀ z∈Rim,(∀ i,z≠ C.post i) → 0 < (mantilla C.post u z).re)
include hA S Tg pR g
local notation "U" r:max=> Z (ℭ r)
local notation "w" t:max i:max=> B i (ℭ t)
private lemma mint (t:r∈ Set.Ioo (C.past j) (C.future j)) : 0 < (w r j).re ∧ (w r j).re^2 = (U r).re^2 + ∑ i∈ Finset.univ.erase j,(w r i).im^2:=by
 let R' i:= C.represents i (A i) (ℭ r); let x:= R' j; obtain ⟨x1,x2⟩ := C.arc_payment r (A j) t (Tg _); change 0< x.re at x1; change x.im=0 at x2; have hx: (w r j).re=(U r).re*x.re:=by rw [C.regrow u A R j j t, Complex.mul_re]; exact sub_eq_self.mpr (by unfold x R' at x2; rw [x2,mul_zero]) -- lemma sub_eq... tune
 have h0:0<(U r).re:= by rw [C.siesta_repr,Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact mul_pos pR (g _ (normP r) (C.not_post _ t))
 have f: x.re^2=C.raymark j r (A j):=by
   have h: x.re^2-x.im^2=C.raymark j r (A j):=by rw [← sqc]; unfold x R'; rw [C.raymark_open r j _ t,Complex.ofReal_re]
   simpa [x2] using h
 have he (k:Spin n)(v:k≠j) : (w r k).im=(U r).re * (R' k).im ∧ -((R' k).im^2)= C.raymark k r (A k):=by
   have E: (R' k).re=0:=C.pure_other r k (A k) t v; unfold R' at *; rw [C.regrow u A R k j t,Complex.mul_im,E,mul_zero,add_zero]; refine ⟨rfl,?_⟩; have H := congrArg Complex.re (C.raymark_open r k (A k) t); simpa only [sqc,E,zero_pow (by decide : (2:ℕ)≠0),zero_sub,Complex.ofReal_re] using H
 rw [hx]; refine ⟨mul_pos h0 x1,?_⟩
 calc
   _ = (U r).re^2 * (x.re^2) := mul_pow ..
   _ = (U r).re^2 * (1 - ∑ i∈ Finset.univ.erase j,C.raymark i r (A i)) := by
     rw [f, ← S,← C.ledger r t A η hA,← Finset.sum_erase_add _ _ (Finset.mem_univ j),add_sub_cancel_left]
   _ = _ := by
     rw [mul_sub,mul_one,Finset.mul_sum,sub_eq_add_neg, ← Finset.sum_neg_distrib]; apply congrArg; exact Finset.sum_congr rfl (fun i t=> by obtain ⟨a,b⟩:=he i (ne_of_mem_erase t); rw [←b,a,mul_neg,neg_neg,mul_pow])
include v
lemma arc_end (t:r∈ Set.Icc (C.past j) (C.future j)):0 ≤ (w r j).re ∧ (w r j).re^2=(U r).re^2 + ∑ i∈ Finset.univ.erase j,(w r i).im^2:=by
 have C1:Continuous fun t=> U t:= continuous_iff_continuousAt.mpr (fun x=> (C.siesta_cont u v R (sphere_subset_closedBall (normP x))).comp (continuous_circleMap ..).continuousAt)
 have C2(i): Continuous fun t=> w t i:= continuous_iff_continuousAt.mpr (fun x=> (C.glisten_cont u v A R i (sphere_subset_closedBall (normP x))).comp (continuous_circleMap ..).continuousAt)
 have y:r∈ closure (Set.Ioo (C.past j) (C.future j)):=by rw [closure_Ioo (C.bud_lt j).ne]; exact t
 constructor
 · exact closure_minimal (fun x hx=> (C.mint u A R j η hA S Tg x pR g hx).1.le) (isClosed_le continuous_const (Complex.continuous_re.comp (C2 j))) y -- neq .ne? want not_equal
 exact closure_minimal (fun x hx=> (C.mint u A R j η hA S Tg x pR g hx).2) (isClosed_eq ((Complex.continuous_re.comp (C2 j)).pow 2) (((Complex.continuous_re.comp C1).pow 2).add (continuous_finsetSum _ fun i _=>(Complex.continuous_im.comp (C2 i)).pow 2))) y
lemma bountiful (e1:p∈Rim): ∃ j,0 ≤ (B j p).re ∧ (B j p).re^2=(Z p).re^2+ ∑ i∈ Finset.univ.erase j,(B i p).im^2:=by
 rw [Rim,show (1:ℝ)=|(1:ℝ)| from (abs_of_nonneg zero_le_one).symm,← range_circleMap, ← (periodic_circleMap 0 1).image_Ioc Real.two_pi_pos 0, zero_add] at e1
 obtain ⟨t,q,rfl⟩:=e1; obtain ⟨j,z⟩:=C.division t (Ioc_subset_Icc_self q); exact ⟨j,C.arc_end u v A R j η hA S Tg t pR g z⟩
end Score
end YM.Anvil
