import YM.SU5.FiniteGaugeData.Seld.GaugeK
import SatinPP.Steel

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert}{j:Axis}{S: OS.Semigroup H j}
-- check import

section Ladder
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
variable (T:ℕ→ℝ→X)(N:ℕ)(x a:ℝ)


-- T 0 singular-damped, T (k+1)' = -L T k
variable (L:X→L[ℝ] X)
-- alternative: G i=L^i T (m+1-i), G i'=-G(i+1).
-- recursive telescope G k(≥0) descending indices.
def swatch(a:ℝ)(i:ℕ)(x:ℝ):=(x-a)^i/(i.factorial:ℝ)
lemma swatch_der (i:ℕ) : HasDerivAt (swatch a (i+1)) (swatch a i x) x:=by
  have d:=(((hasDerivAt_id' x).sub_const a).pow (i+1)).div_const ((i+1).factorial:ℝ)
  convert d using 1
  all_goals try rfl
  unfold swatch
  rw [Nat.factorial_succ,Nat.add_sub_cancel]
  have u:(↑(i+1):ℝ)≠0:= by positivity
  rw [Nat.cast_mul,mul_one,mul_div_mul_left _ _ u]
-- T i'=-T (i+1)
def sample (T:ℕ→ℝ→X)(a:ℝ) : ℕ→ℝ→X
| 0,x=> T 0 x
| i+1,x=>sample T a i x + swatch a (i+1) x • T (i+1) x
lemma sample_der (d:∀ i≤N, HasDerivAt (T i) (-T (i+1) x) x):
    HasDerivAt (sample T a N) (swatch a N x • -T (N+1) x) x:=by
  induction N with
  | zero=> simpa only [sample,swatch,pow_zero,Nat.factorial_zero,Nat.cast_one,
              div_one,one_smul] using d 0 le_rfl
  | succ i ih=>
    have e:=ih (fun k p=>d k (p.trans (Nat.le_succ _)))

    have f:=e.add ((swatch_der x a i).smul (d (i+1) le_rfl))
    convert f using 1
    rfl
    simp only [smul_neg]
    abel
lemma sample_here :sample T a N a=T 0 a:=by
 induction N with
 | zero=>rfl
 | succ i h=>rw [sample,h,swatch, sub_self,zero_pow (Nat.succ_ne_zero _),zero_div,zero_smul,add_zero]

lemma sample_con :Continuous (fun a=> sample T a N 1):=by
 induction N with
 | zero=> exact continuous_const
 | succ i h=> exact h.add ((((continuous_const.sub continuous_id').pow _).div_const
    (↑(i+1).factorial:ℝ)).smul continuous_const)


lemma sample_price {c:ℝ}(c0:0≤c)
   (d:∀ x:ℝ,0<x→∀ i≤N, HasDerivAt (T i) (-T (i+1) x) x)
   (p:∀ x:ℝ,0<x→x≤1→‖T (N+1) x‖ ≤ c/x^N):
   ∃ b, ∀ x:ℝ,0<x→x≤1→ ‖T 0 x‖≤b:=by
 obtain ⟨b,u⟩:=isCompact_Icc (a:=(0:ℝ)) (b:=1) |>.bddAbove_image (sample_con T N |>.norm.continuousOn)
 refine ⟨b+c,fun x x₀ x₁=>?_⟩
 have q(y:ℝ)(z:y∈Icc x 1) : ‖swatch x N y • -T (N+1) y‖≤c:=by
    have t:0<y:=x₀.trans_le z.1
    rw [norm_smul,norm_neg,Real.norm_eq_abs, abs_of_nonneg]
    · refine (mul_le_mul (show swatch x N y≤y^N from ?_) (p y t z.2) (norm_nonneg _) (pow_nonneg t.le _)).trans ?_
      · unfold swatch; rw [div_le_iff₀ (show (0:ℝ)<↑N.factorial by exact_mod_cast N.factorial_pos)]
        exact
       
         ((pow_le_pow_left₀ (sub_nonneg.mpr z.1) (sub_le_self y x₀.le) N).trans
           (le_mul_of_one_le_right (pow_nonneg t.le _) (by exact_mod_cast N.factorial_pos)))
      field_simp; exact le_rfl
    unfold swatch; have h:=sub_nonneg.mpr z.1; positivity

 have k:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
     (fun y z=>HasDerivAt.hasDerivWithinAt (sample_der T N y x (d y (x₀.trans_le (mem_Icc.mp z).1)))) q
     (convex_Icc _ _) (right_mem_Icc.mpr x₁) (left_mem_Icc.mpr x₁)
 rw [sample_here,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr x₁)] at k
 have e:‖sample T x N 1‖≤b:=u (mem_image_of_mem _ (show x∈Icc (0:ℝ) 1 from ⟨x₀.le,x₁⟩))
 linarith [norm_sub_norm_le (T 0 x) (sample T x N 1),mul_nonneg c0 x₀.le]
end Ladder

section Dampen
variable (S)
def bath : H.Op →L[ℝ] H.Op := ((ContinuousLinearMap.mul ℝ H.Op) (saucer S) +
     (ContinuousLinearMap.mul ℝ H.Op).flip (saucer S))

variable (e:ℝ) {t:ℝ}(h:e<t)
local notation "R"=>saucer S
def Sash (e t:ℝ):H.Op:=Real.exp (-t) • S.F (t-e)
lemma sash_d (h:e<t): HasDerivAt (Sash S e)
          (Real.exp (-t) • - (looper S (t-e))) t:=by
 have d: HasDerivAt (fun u:ℝ=> S.F (u-e)) (slug S (t-e)) t:=by
    let z:=((S.localHeat _ (below (z:=(t:ℂ)) h)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t ((Complex.ofRealCLM.hasFDerivAt.hasDerivAt).sub_const (e:ℂ))
    simpa [slug] using! z
 have d':HasDerivAt (fun u=>Real.exp (-u)) (-Real.exp (-t)) t:= by
    simpa using (hasDerivAt_id' t).neg.exp
 convert d'.smul d using 1 <;> try rfl
 unfold looper
 rw [neg_smul,neg_sub,smul_sub]; abel
lemma left_d (h:e<t):
   HasDerivAt (fun t=>R*Sash S e t) (-(Sash S e t)) t:=by
 have d:=(sash_d S e h).const_mul (R)
 unfold Sash
 rw [mul_smul_comm,mul_neg,dorsal _ _ (below (z:=(t:ℂ)) h),smul_neg] at d; exact d

lemma right_d (h:e<t):
   HasDerivAt (fun t=>Sash S e t*R) (-(Sash S e t)) t:=by
 have d:=(sash_d S e h).mul_const (R)
 unfold Sash
 rw [smul_mul_assoc,neg_mul,jalousie _ _ (below (z:=(t:ℂ)) h),smul_neg] at d; exact d
variable {A:Stamp H} {m:ℕ}{c:ℝ}(K:Paid S m c A)

def Damped (A:Stamp H)(t:ℝ):H.Op:=Real.exp (-t) • (Real.exp (-t) • A t t)
local notation "D"=>Damped A
include K
lemma damped_eq (p:0<e)(h:e<t): D t=Sash S e t*A e e*Sash S e t:=by
 unfold Damped
 rw [← paint_real K (p.trans h) (p.trans h),paint_p K p h h]
 unfold paintAt Sash
 rw [smul_mul_assoc,mul_smul_comm,smul_mul_assoc]

lemma bath_d (h:0<t):HasDerivAt (fun u=>R * D u * R) (-(bath S (D t))) t:=by
 let e:=t/2; let p:=half_pos h; let q:=half_lt_self h
 have d:=((left_d S e q).mul_const (A e e)).mul (right_d S e q)
 have u:=
    damped_eq S e K p q
 rw [show -(bath S (D t)) = - Sash S e t * A e e * (Sash S e t * R)
            + R * Sash S e t * A e e * -Sash S e t by
      change -(R * D t + D t * R)=_
      rw [u,neg_mul,neg_mul,mul_neg,neg_add_rev]; simp only [mul_assoc]]
 refine d.congr_of_eventuallyEq ?_


 filter_upwards [Ioi_mem_nhds q] with r a
 simp only [Pi.mul_apply,damped_eq S e K p (show e<r from a),mul_assoc]

local notation "L"=>bath S
local notation "κ"=>Cache S

def round (S:OS.Semigroup H j)(A:Stamp H)(n:ℕ)(t:ℝ):H.Op:=
     Cache S n * Damped A t * Cache S n

local notation "G"=>round S A

lemma round_d (h:0<t)(n:ℕ):HasDerivAt (G (n+1)) (-(L (G n t))) t:=by
 have d:=((bath_d S K h).const_mul (κ n)).mul_const (κ n)
 have v:(R) * κ n= κ n * R :=(Commute.refl R).pow_right n
 convert d using 1 <;> try rfl
 · funext t; unfold round
   rw [show κ (n+1)= R*κ n from pow_succ' R n]
   rw [v]; simp only [mul_assoc,v]
 · show -(R*(κ n * D t * κ n) + (κ n * D t * κ n)*R)=
         κ n*-(R*D t + D t * R)*κ n
   rw [← mul_assoc,← mul_assoc,v, mul_assoc (κ n * D t),←v,mul_neg,neg_mul,mul_add,add_mul]
   simp only [mul_assoc]
   rw [←mul_assoc R (κ n),v,mul_assoc]

def armT(m:ℕ)(A:Stamp H)(i:ℕ)(t:ℝ):=(L ^ i) (round S A (m+1-i) t)

local notation "Z"=>armT S m A

lemma arm_der (h:0<t)(i:ℕ)(p:i ≤ m):HasDerivAt (Z i) (-(Z (i+1) t)) t:=by
 let u:= m+1-(i+1)
 have d:HasDerivAt (G (m+1-i)) (-(L (G u t))) t:=by
   rw [show m+1-i=u+1 by unfold u;omega]
   exact round_d S K h u
 change HasDerivAt ((L ^ i) ∘ G (m+1-i)) (- (L^(i+1)) (G u t)) t
 simpa [map_neg,pow_succ] using
    (L^i).hasFDerivAt.comp_hasDerivAt t d
lemma priced_cache : ∃ b, ∀ t:ℝ,0<t→t≤1→ ‖G (m+1) t‖ ≤ b:=by
 let d :=‖L^(m+1)‖*c
 have a:0≤d:= mul_nonneg (norm_nonneg _) K.pos.le
 have p(t:ℝ)(v:0<t)(w:t≤1):‖D t‖≤c/t^m:=by
   unfold Damped
   have u:‖Real.exp (-t)‖≤1:= by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr v.le)

   rw [norm_smul,norm_smul]
   exact (mul_le_of_le_one_left (by positivity) u).trans
      ((mul_le_of_le_one_left (by positivity) u).trans (K.le v w))
 have q(t:ℝ)(v:0<t)(w:t≤1):‖Z (m+1) t‖≤d/t^m:=by
   unfold armT; rw [Nat.sub_self]; unfold round; unfold Cache; rw [pow_zero,one_mul,mul_one]
   dsimp only [d]; rw [mul_div_assoc]
   exact ((L^(m+1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (p _ v w) (norm_nonneg _))
 obtain ⟨b,h⟩:=sample_price (Z) m a (fun t p=>arm_der S K p) q
 refine ⟨b,fun t v w=>?_⟩
 simpa only [armT,Nat.sub_zero,pow_zero, one_apply_eq_self] using h t v w
lemma undamped_price : ∃ b, ∀ t:ℝ,0<t→t≤1→‖κ (m+1)*A t t*κ (m+1)‖≤b:=by
 obtain ⟨b,k⟩:=priced_cache S K
 refine ⟨b/(Real.exp (-1)*Real.exp (-1)),fun t v u=>?_⟩
 have d:=k t v u
 unfold round Damped at d
 rw [mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_mul_assoc,norm_smul,norm_smul,
     Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at d
 have e:=Real.exp_le_exp.mpr (neg_le_neg u)
 rw [←mul_assoc,mul_comm] at d

 rw [le_div_iff₀ (by positivity)]
 exact (mul_le_mul_of_nonneg_left (mul_le_mul e e (by positivity) (by positivity)) (norm_nonneg _)).trans d

variable (d:ℕ)

abbrev Wrap (Y:H.Op):=Cache S d * Y * Cache S d
-- B represents Cache Price
structure Role (A:Stamp H)(B:H.Op):Prop where
  wear(u v:ℝ)(p:0<u)(q:0<v): Wrap S d (A u v)=jacket S u v B


lemma role_limit (l:Filter ℕ)[l.NeBot]{r:ℕ→ℝ}
   (h:Tendsto r l (𝓝 0))(p:∀ i,0<r i)
   {B:H.Op}(e:Anvil.Limited l (fun i=>Wrap S d (A (r i) (r i))) B):
   Role S d A B:=by
 constructor; intro u v a b
 let f i:= A (u+r i) (v+r i)
 have h₁:Tendsto f l (𝓝 (A u v)):=by
    rw [← paint_real K a b]
    have ht: Tendsto (fun i=>(r i:ℂ)) l (𝓝 0):= by
        simpa! [comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp h
    let g(t:ℂ):=paint S A (u+t) (v+t)
    have cg:ContinuousAt g 0:= (analyticAt_paint K (f:=fun t:ℂ=>u+t) (g:=fun t:ℂ=>v+t)
        (by simp only [add_zero]; exact a) (by simp only [add_zero]; exact b)
        (analyticAt_const.add analyticAt_id) (analyticAt_const.add analyticAt_id)).continuousAt
    have k:=cg.tendsto.comp ht
    dsimp only [g] at k; rw [add_zero,add_zero] at k
    exact k.congr fun i=>by dsimp [f]; rw [←Complex.ofReal_add, ←Complex.ofReal_add];
                                exact paint_real K (add_pos a (p i)) (add_pos b (p i))

 have k:=jacket_Limited S u v e
 apply ContinuousLinearMap.ext; intro y; apply ext_inner_left ℂ; intro x
 have ht := (tendsto_const_nhds (x:=κ d) |>.mul h₁ |>.mul tendsto_const_nhds : Tendsto (fun i=>Wrap S d (f i)) l (𝓝 (Wrap S d (A u v))))
 refine tendsto_nhds_unique ?_ (k.confirms x y)
 refine Tendsto.congr ?_ (show Tendsto (fun i=>inner ℂ x (Wrap S d (f i) y))
     l (𝓝 (inner ℂ x (Wrap S d (A u v) y))) from
     ((innerSL ℂ x).continuous.continuousAt.tendsto.comp
        ((ContinuousLinearMap.apply ℂ H.space y).continuous.continuousAt.tendsto.comp ht)))
 intro i; have t:=r i
 suffices w: Wrap S d (A (u+r i) (v+r i))=jacket S u v (Wrap S d (A (r i) (r i))) by
   dsimp [f];rw [w]
 rw [K.fits (p i) (p i) (le_add_of_nonneg_left a.le) (le_add_of_nonneg_left b.le),
     add_sub_cancel_right,add_sub_cancel_right]
 generalize A _ _=o
 let s:=u.toNNReal; let t:=v.toNNReal
 have e₁:=((cupE S s).pow_left d).eq
 have e₂:=((cupE S t).symm.pow_right d).eq
 change κ d * (S.E s *o *S.E t)*κ d=S.E s*(κ d*o*κ d)*S.E t
 rw [←mul_assoc,←mul_assoc]
 change κ d*S.E s= _ at e₁; change S.E t*κ d=_ at e₂
 rw [e₁]
 simp only [mul_assoc,e₂]



lemma role_exists: ∃ B,Role S (m+1) A B:=by
 obtain ⟨b,v⟩:=undamped_price S K
 let f(n:ℕ):ℝ:=1/(n+1)
 have t:Tendsto f atTop (𝓝 0):= tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
 let C:=max b 1
 have p(i):0<f i:=by unfold f; positivity
 have a(i):‖Wrap S (m+1) (A (f i) (f i))‖≤C := le_max_of_le_left
   (v _ (p i) (div_le_one_of_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)) (by positivity)))
 obtain ⟨B,e⟩:=limited_final (lt_max_of_lt_right zero_lt_one) (Eventually.of_forall a)
 exact ⟨B,role_limit S K _ _ (t.mono_left final_reels) p e⟩

#print axioms role_exists
end Dampen

namespace Role
variable {A:Stamp H}{B:H.Op}{d:ℕ}(K:Role S d A B)
local notation "κ"=>Cache S
include K

lemma turn: Role S d (Turn A) (star B):=by
 constructor; intro u v p q
 rw [← jacket_star,K.wear _ _ q p|>.symm,Turn,Wrap,star_mul,star_mul,
    ((saucer_sym S).pow d).star_eq,mul_assoc]

omit K
lemma cancel_left (d:ℕ){a b:H.Op}(h:κ d * a=κ d * b):a=b:=
 ContinuousLinearMap.ext fun y=>cache_I S d (DFunLike.congr_fun h y)
lemma cancel_right (d:ℕ){a b:H.Op}(h:a * κ d=b * κ d):a=b:=by
 apply star_injective
 apply cancel_left (S:=S) d
 have h':=congrArg (star:H.Op→H.Op) h
 rwa [star_mul,star_mul,((saucer_sym S).pow d).star_eq] at h'
include K
-- power sandwich heat recovering
lemma par (u v:ℝ≥0)(p:0<u)(q:0<v): A (u:ℝ) (v:ℝ)=Par S d u * B * Par S d v:=by
 let a:= K.wear u v p q
 let b:= P_Heq S u d p
 let c:=show Par S d v *(κ d)= S.E v from
    (change_m S d _ (dur.mpr q)).trans (S.roots_heat q)
 have z: κ d*(A ↑u ↑v)*(κ d)=κ d*(Par S d u * B * Par S d v)*(κ d):= by
   conv_rhs => rw [←mul_assoc,←mul_assoc,b,mul_assoc,c]
   convert a using 1
   change _=S.E _ * _ * S.E _
   rw [Real.toNNReal_coe, Real.toNNReal_coe]
 -- injective * & adjoint or dense

 rw [mul_assoc,mul_assoc (κ d)] at z
 exact cancel_right d (cancel_left d z)

variable {m:ℕ}{c:ℝ}
lemma suited (T:Paid S m c A) (z w:ℂ)(p:z∈inside)(q:w∈inside):
    paint S A z w=parabola S d z * B * parabola S d w:=by
 obtain ⟨e,t,h,k⟩:=widths_ink p q
 have a:(↑e:ℂ)∈inside:=t
 let u:ℝ≥0:=⟨e,t.le⟩
 have y:z-e∈inside:=below h
 have l:w-e∈inside:=below k
 rw [paint_p T t h k]
 have eq:A e e=parabola S d e * B * parabola S d e:=par K u u t t
 have b:S.F (z-e)*parabola S d e=parabola S d z:=by
   apply cancel_right (S:=S) d
   rw [mul_assoc,change_m S d _ a,change_m S d _ p]
   exact Eq.trans (S.pairs y a).symm (by rw [sub_add_cancel])
 have r:parabola S d e*S.F (w-e)=parabola S d w:=by
   apply cancel_left (S:=S) d
   rw [← mul_assoc,recover S d _ a,recover S d _ q]
   exact Eq.trans (S.pairs a l).symm (by rw [add_sub_cancel])
 unfold paintAt
 rw [eq,← mul_assoc,← mul_assoc,b,mul_assoc _ (parabola S d e),r]
#print axioms suited
end Role
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

