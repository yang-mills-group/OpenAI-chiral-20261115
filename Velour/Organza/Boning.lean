import Velour.Organza.Cording
/-!
# High energy price for all caps bought (unweighted operator norm) at
no more than geometric costs on a decreasing grid
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


local notation "R" => S.gauze
local notation "E" => S.E


def Prepaid (Q:ℝ≥0→H.Op) (m:ℕ)(X:H.Op):Prop:=
 ∀ d:ℝ≥0, 0<d → R ^ m * Q d * R ^ m = E d * X * E d

def Covetails (Q:ℝ≥0→H.Op): Prop:=
 ∀ d:ℝ≥0, 0<d → ∀ e, Q (d+e) = E e * Q d * E e
/-- Exponential cost bound; clocks may fall arbitrarily fast. -/
structure Installments (Q:ℝ≥0→H.Op) (τ:ℕ→ℝ≥0) (C D : ℝ) : Prop where
 minC : 1≤C
 minD : 1≤D
 pos (k:ℕ):0<τ k
 falls (k:ℕ): (τ (k+1):ℝ)≤τ k/2
 pay (k:ℕ): ‖Q (τ k)‖≤ C*D^k
def Cashable (Q:ℝ≥0→H.Op): Prop:= S.Covetails Q ∧ ∃ τ C D, Installments Q τ C D

namespace Installments
variable {Q:ℝ≥0→H.Op}{τ:ℕ→ℝ≥0}{C D:ℝ} (p:Installments Q τ C D)
include p
lemma small (k:ℕ): τ (k+1) ≤ τ k:=
 show (τ (k+1):ℝ) ≤_ from (p.falls k).trans (half_le_self (by positivity))


lemma tiny (k:ℕ): (τ k:ℝ)≤ τ 0*((2:ℝ)⁻¹)^k:=by
 induction k with
 | zero=>simp
 | succ k ih=>rw[pow_succ, ←mul_assoc, ←div_eq_mul_inv]; exact
     (p.falls k).trans (div_le_div_of_nonneg_right ih (by norm_num))

lemma dies : Tendsto τ atTop (𝓝 0):=by
  refine NNReal.tendsto_coe.mp ?_
  rw [NNReal.coe_zero]
  exact squeeze_zero (f:=fun k=>(τ k:ℝ)) (fun _=> NNReal.coe_nonneg _)
     p.tiny (by simpa using
       (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:0≤(2:ℝ)⁻¹)
          (by norm_num)).const_mul (τ 0:ℝ))
end Installments

variable (Q:ℝ≥0→H.Op)

/-- Bounded weighted prices with dial paid. -/
def winding_pick (m:ℕ)(t:ℝ≥0):=
 S.winding m t * Q t * S.winding m t
local notation "W"=> S.winding

private lemma pick_sandwich (m:ℕ)(t u:ℝ≥0)(X:H.Op):
 W m t * (E u * X * E u) * W m t =
 E u * (W m t * X * W m t) * E u ∧
 W m t * (E u * X * E u) * W m t =
 (E u * W m t) * X * (E u * W m t):= by
   let Y:= W m t
   have g:=S.winding_symm m t u
   constructor
   · rw [←mul_assoc,←mul_assoc, mul_assoc _ (E u), g.eq, ←mul_assoc _ (W m t) (E u), ← g.eq] -- avoid g rw all
     simp only [mul_assoc]
   rw [←mul_assoc,←mul_assoc,←g.eq,mul_assoc _ (E u)]
lemma winding_map (h:S.Covetails Q){d:ℝ≥0}(p:0<d)(m:ℕ){t:ℝ≥0}(g:0<t):
 E d * S.winding_pick Q m t * E d =
    (E t * W m t) * Q d * (E t * W m t):=by
 rw [winding_pick, ← (S.pick_sandwich m t d _).1, ←h t g, add_comm, h d p]
 exact (S.pick_sandwich m t t _).2
 -- manually manipulate




private lemma firm_diff {T V:H.Op}{u v y:ℝ}
 (m:‖T‖≤u)(n:‖V‖≤u)(h:‖T-V‖≤v){X:H.Op}(p:‖X‖≤y):
 ‖T * X * T - V * X * V‖ ≤ 2 * u * y * v:=by
   have up:0≤u:=(norm_nonneg _).trans m
   have vp:0≤v:=(norm_nonneg _).trans h
   have yp:0≤y:=(norm_nonneg _).trans p
   rw [show _-_ = (T-V)*X*T + V*X*(T-V) by rw [mul_sub,sub_mul,sub_mul];abel]
   refine (norm_add_le ..).trans ((add_le_add ?_ ?_).trans_eq (show v*y*u + u*y*v= _ from by ring))
   · exact (norm_mul_le ..).trans (mul_le_mul
     ((norm_mul_le ..).trans (mul_le_mul h p (norm_nonneg _) vp)) m (norm_nonneg _) (by positivity))
   exact (norm_mul_le ..).trans (mul_le_mul
     ((norm_mul_le ..).trans (mul_le_mul n p (norm_nonneg _) up)) h (norm_nonneg _) (by positivity))


lemma winding_swing (h:S.Covetails Q)(s t:ℝ≥0)(r:0<s)(p:s≤t)(m:ℕ){y:ℝ}(v:‖Q s‖≤y):
 dist (S.winding_pick Q m t) (S.winding_pick Q m s) ≤
    2 * (m * 2^m) * y * (m * (2 * (t:ℝ))^m):= by
 rw [dist_comm,dist_eq_norm, winding_pick, winding_pick,
     show Q t=E (t-s)*Q s*E (t-s) from
        (congrArg Q (add_tsub_cancel_of_le p).symm).trans (h s r _),
     (S.pick_sandwich _ _ _ _).2]
 refine firm_diff (S.winding_bound ..) ?_ (S.winding_diff _ _ p m) v
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)).trans
    (S.winding_bound ..))

/-- Very explicit bill incl. constants, on top of price at initial dial.
This times (D/2^m)^k pays for the difference at k,k+1. -/
def wind_charge (τ:ℕ→ℝ≥0)(C D:ℝ)(m:ℕ) :=
  2 * (m * (2:ℝ)^m) * (C * D) * (m * (2 * (τ 0:ℝ))^m)

variable {Q} {τ:ℕ→ℝ≥0}{C D:ℝ}


lemma winding_geometric (h:S.Covetails Q)(p:Installments Q τ C D)(m k:ℕ):
  dist (S.winding_pick Q m (τ k)) (S.winding_pick Q m (τ (k+1))) ≤
    wind_charge τ C D m * (D / 2^m)^k:=by
 have c:0<C:=zero_lt_one.trans_le p.minC; have d:0<D:=zero_lt_one.trans_le p.minD
 refine (S.winding_swing Q h _ _ (p.pos _) (p.small k) m (p.pay (k+1))).trans ?_
 refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left (p.tiny k) (by positivity:0≤(2:ℝ))) m)
      (Nat.cast_nonneg m)) (by positivity : 0≤ 2 * (m * (2:ℝ)^m)* (C*D^(k+1)))).trans_eq ?_
 unfold wind_charge
 rw [div_eq_mul_inv, ← inv_pow, ←mul_assoc 2 (τ 0:ℝ), mul_pow ((2:ℝ)*(τ 0:ℝ)), pow_right_comm (2:ℝ)⁻¹ k m]
 ring

theorem winding_price (h:S.Covetails Q)(p:Installments Q τ C D)
    (m:ℕ)(r:D<2^m) :
 ∃X:H.Op,
     S.Prepaid Q m X ∧
     Tendsto (fun i=> S.winding_pick Q m (τ i)) atTop (𝓝 X) ∧
     ∀k:ℕ, dist (S.winding_pick Q m (τ k)) X ≤
       wind_charge τ C D m * (D/2^m)^k / (1-D/2^m) := by
 have hm:m≠0:= by rintro rfl; rw [pow_zero] at r; exact not_le.mpr r p.minD
 have g:=S.winding_geometric h p m
 have e : D/2^m<1:= div_lt_one (by positivity) |>.mpr r
 obtain ⟨X,t⟩:= cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric _ _ (f:=fun i=>S.winding_pick Q m (τ i)) e g)
 refine ⟨X, fun d u=> ?_, t,dist_le_of_le_geometric_of_tendsto _ _ e g t⟩
 have l:= S.winding_approaches p.dies hm
 exact tendsto_nhds_unique ((l.mul_const (Q d)).mul l)
    (((t.const_mul (E d)).mul_const (E d)).congr fun i=>
       S.winding_map Q h u m (p.pos i))


#print axioms winding_price


/-- Apply to the evolving election. No condition at Q 0. -/
theorem cashed (h:S.Cashable Q) : ∃ m X, S.Prepaid Q m X:= by
 rcases h with ⟨h,b,c,d,k⟩
 obtain ⟨m,r⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num:1<(2:ℝ))).eventually
    (eventually_gt_atTop d)).exists
 obtain ⟨X,p,_⟩:= S.winding_price h k m r
 exact ⟨_,_,p⟩

lemma cashable_of_tail (h:S.Covetails Q)(c:1≤C)(d:1≤D)
    (pos:∀k,0<τ k)(falls:∀k,(τ (k+1):ℝ)≤τ k/2)
    (p:∀ᶠk:ℕ in atTop,‖Q (τ k)‖≤C*D^k):
 S.Cashable Q:=by
 obtain ⟨m,j⟩:= eventually_atTop.mp p
 refine ⟨h,fun i=>τ (m+i), C*D^m,D,
    ⟨one_le_mul_of_one_le_of_one_le c (one_le_pow₀ d),d,
     fun i=>pos _, fun i=>falls (m+i),fun i=>?_⟩⟩
 rw [mul_assoc,←pow_add]
 exact j _ (Nat.le_add_right ..)
#print axioms cashed

