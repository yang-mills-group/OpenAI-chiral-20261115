import Gingham.AnalyticEdge
import Velour.Organza.Larva
/-!
# Reading and detecting the excited charge on one graph domain

The exchanged quantity tested below uses **actual** marginals. Use the order
gauge first (take the reflected adjoint at that slot) and matter second.
Two-input test, not claiming a 'decoupled state' well-defined also on joint
products, or that the two local observable algebras have trivial intersection.

Criteria before squaring ranks: a finite-sum approximation at positive price,
*not* a scattering criterion. Strictly weaker hypotheses than field equations.
We need only overlap of excited vectors in this step.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace YM.OS.Semigroup.Gingham
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal Topology InnerProductSpace ComplexOrder
open Boundary Probe
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)
local notation "U" => S.unit.translation
local notation "V" => S.U
local notation "T" => S.E
local notation "D" => S.muslin
/- ## Same reading/prediction conventions for any sectors, bounded or not
We give the bounded version using a Hilbert space; real-edge using D. -/
variable (ω : H.space)

/-- One-input actual marginal. Use on subalgebras of observations. -/
def cup (A : H.Op) : ℂ := inner ℂ ω (A ω)
def coupled (A B : H.Op) : ℂ := cup ω (A*B)
/-- Predictor from product of marginals. -/
def forecast (A B : H.Op) : ℂ := cup ω A * cup ω B
def fault (A B : H.Op) := coupled ω A B - forecast ω A B

def rcup (v : D) (A : Module.End ℂ D) : ℂ := inner ℂ v.val (A v).val
def rcoupled (v : D) (A B : Module.End ℂ D) : ℂ := rcup S v (A*B)
def rforecast (v : D) (A B : Module.End ℂ D) : ℂ :=
   rcup S v A * rcup S v B
def rfault (v : D) (A B : Module.End ℂ D) := rcoupled S v A B - rforecast S v A B

/-- Away from vacuum. -/
def shred (u : H.space) : H.space := u - inner ℂ ω u • ω

lemma shred_cont : Continuous (shred ω) := by unfold shred; fun_prop

def jut (A : H.Op) : H.space := shred ω (A ω)
def rjut (v : D) (A : Module.End ℂ D) : D :=
   A v - rcup S v A • v

lemma shred_symmetric (n : inner ℂ ω ω = 1) (u w : H.space) :
    inner ℂ (shred ω u) (shred ω w) =
    inner ℂ u w - inner ℂ u ω * inner ℂ ω w := by
  simp only [shred,inner_sub_left,inner_sub_right,inner_smul_left,
     inner_smul_right,inner_conj_symm,n]; ring

lemma shines (n : inner ℂ ω ω = 1) (A B : H.Op) :
    fault ω A B = inner ℂ (jut ω (star A)) (jut ω B) := by
  unfold jut; rw [shred_symmetric _ n]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rfl

lemma rshines {v : D} (n : inner ℂ v.val v.val = 1)
    {A A' : Module.End ℂ D} (b : S.Faces A' A) (B : Module.End ℂ D) :
    rfault S v A B = inner ℂ (rjut S v A').val (rjut S v B).val := by
  change _ = inner ℂ (shred _ _) (shred _ _)
  rw [shred_symmetric _ n,b,b]
  rfl

def Ano (v : H) : Prop := (∀ d, T d v = v) ∧ (∀ y, U y v = v)

lemma T_shred (v : H) (p : ∀ t,T t v = v) (u : H) (d) :
    T d (shred v u) = shred v (T d u) := by
  rw [shred, map_sub,map_smul,p,shred,← ContinuousLinearMap.adjoint_inner_left, S.sym,p]

lemma U_shred (v : H) (p : ∀ y,U y v = v) (u : H) (y) :
    U y (shred v u) = shred v (U y u) := by
  rw [shred,map_sub,map_smul,p,shred,← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, S.unit_star,p]

/-- Test on vacuum guard. -/
lemma real_vac (v : D) (p : ∀ t,T t v.val=v.val) {Q : ℝ≥0 → H.Op}
    {A : S.Detector} (h : S.Instates Q A) (f : Test4) {t : ℝ≥0} (u:0<t) :
    jut v.val (S.rasp (Q t) f) = T t (rjut S v (A f)).val := by
  change shred _ _ = T t (shred v.val _)
  rw [T_shred _ _ p, ← labelled_coe, h.guard _ _ u]
  have z : S.heatL t v = v := Subtype.ext (p _)
  change shred _ ((S.heatL t (A f (S.heatL t v))).val)=_
  rw [z]; rfl

lemma real_loc (v : D) (p : ∀ t,U t v.val=v.val) {Q : ℝ≥0 → H.Op}
    {A : S.Detector} (h : S.Instates Q A) (f : Test4) (y : E4) :
    (rjut S v (A (ahead y f))).val = U y (rjut S v (A f)).val := by
  change shred _ _ = U y (shred v.val _)
  rw [U_shred _ _ p]
  have z := DFunLike.congr_fun (h.translates y f) v
  change A (ahead y f) (S.liftL y v) = _ at z
  rw [show S.liftL y v=v from Subtype.ext (p _)] at z
  rw [z]; rfl

/-- `age` is an *evaluation*, not an assumption of analytic continuation;
left turn age cancel theorem. Use simultaneous firing at Mink centres -t,+t. -/
def age (d : ℝ) (u : H) := S.edge d u

lemma edge_star (t : ℝ) : (S.edge t).adjoint = S.edge (-t) := by
  have he(s:ℝ) : S.unit.translation (s • basis a) = S.edge s := by
    have ht : SEP a (s • basis a)=0 := Subtype.ext (show (s:ℝ) • basis a-_=_ by simp)
    simp [unit,ht,S.uZero]
  rw [← he, ← ContinuousLinearMap.star_eq_adjoint, S.unit_star, ← neg_smul, he]
lemma age_heat (d : ℝ) (t : ℝ≥0) (v:H) :
    S.edge d (S.E t v) = S.E t (S.edge d v) := by
  have he(s:ℝ) : S.unit.translation (s • basis a) = S.edge s := by
    have ht : SEP a (s • basis a)=0 := Subtype.ext (show (s:ℝ) • basis a-_=_ by simp)
    simp [unit,ht,S.uZero]
  rw [← he,← mul_apply_eq_comp,(unit_heat S _ _).eq];rfl

/-- Analytic real proof with offsets: can use 2 decoys, centred in
their real slots and translated then priced on the heat sleeves. If that
Gram is still nonzero, can move with *any* small prescribed error in
real pose and recover discrepancy even when removing both sleeves. -/
lemma traces_real (v : D) (g : Ano S v.val)
    (n : inner ℂ v.val v.val = 1)
    {Q₁ Q₂ : ℝ≥0 → H.Op} {A B : S.Detector}
    (h : S.Instates Q₁ A) (k : S.Instates Q₂ B)

    (f u : Test4) {A' : Module.End ℂ D} (e : S.Faces (A f) A')
    {t r : ℝ≥0} (w : 0<t) (z : 0<r) (l b : ℝ)
    (p : inner ℂ (age S l (jut v.val (S.rasp (Q₁ t) f)))
                 (age S b (jut v.val (S.rasp (Q₂ r) u))) ≠ 0)
    (ε : ℝ) (y : 0<ε) :
    ∃ s : ℝ, |s| < ε ∧ rfault S v A' (B (ahead (s • basis a) u)) ≠ 0 := by
  unfold age at p
  rw [real_vac S _ g.1 h _ w, real_vac S _ g.1 k _ z,
    ←ContinuousLinearMap.adjoint_inner_right, edge_star,
    ←ContinuousLinearMap.comp_apply (S.edge (-l)), S.send,
    ←ContinuousLinearMap.adjoint_inner_right, S.sym, ←age_heat,
    ←ContinuousLinearMap.comp_apply (S.E t), ←S.time] at p
  obtain ⟨s,js,q⟩ := paid_move_real S (add_pos w z) p (neg_lt_self y)
  exact ⟨s,abs_lt.mpr js, by
    rw [rshines S n e, real_loc S _ g.2 k]
    exact q⟩

section proxy
/-! ## Positive-price overlap proxy -/
variable {I : Type} (A : ℝ≥0 → H.Op) (J : I → ℝ≥0 → H.Op)

/-- Right charge with all heat on itself. -/
def hearsay : Set H.space :=
  {w | ∃ i d y, 0 < d ∧ w = S.U y (jut ω (J i d))}

/-- Vectors centred by actual values. Approximate even rather than in closed linear span. -/
def mistrial : Prop :=
  ∃ t > (0:ℝ≥0), ∃ b ∈ Submodule.span ℂ (hearsay S ω J),
    ‖jut ω (A t) - b‖ < ‖jut ω (A t)‖

structure Forfeit where
  member : I
  geo : Cross a
  earlier : ℝ≥0
  later : ℝ≥0
  pays : 0 < earlier
  repays : 0 < later
  engaged :
    inner ℂ (jut ω (A earlier)) (V geo (jut ω (J member later))) ≠ 0

lemma hear_nonzero (p : mistrial S ω A J) : Nonempty (Forfeit S ω A J) := by
  by_contra! nh
  obtain ⟨t,e,b,u,v⟩ := p
  let x := jut ω (A t)
  have h : Submodule.span ℂ (hearsay S ω J) ≤
      LinearMap.ker (innerSL ℂ x).toLinearMap := Submodule.span_le.mpr (by
    rintro w ⟨i,d,y,r,rfl⟩
    apply LinearMap.mem_ker.mpr
    by_contra he
    exact nh.false ⟨i,y,t,d,e,r,he⟩)
  have h0 : inner ℂ x b = 0 := (LinearMap.mem_ker.mp (h u))
  have le := norm_inner_le_norm (𝕜:=ℂ) x (x-b)
  rw [inner_sub_right,h0,sub_zero,inner_self_eq_norm_sq_to_K,
       norm_pow, RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)] at le
  · change ‖x-b‖ < ‖x‖ at v
    linarith [mul_lt_mul_of_pos_left v ((norm_nonneg _).trans_lt v)]

/-- Closure criterion (targets positive-heat Ward difference quotient). -/
lemma proxy_closure {t : ℝ≥0} (u:0<t)
    (h : jut ω (A t) ≠ 0)
    (p : jut ω (A t) ∈ closure (Submodule.span ℂ (hearsay S ω J) : Set H.space)) :
    mistrial S ω A J := by
  obtain ⟨z,w,y⟩ := Metric.mem_closure_iff.mp p _ (norm_pos_iff.mpr h)
  exact ⟨t,u,z,w,by rwa [← dist_eq_norm]⟩

end proxy
/-! ## Change durations freely (cross readings) -/
section Eu
variable (A B : ℝ≥0 → H.Op)
/-- Joint heat on right measured as adding to charge price. -/
lemma jut_later (g : Ano S ω)
    (w : S.Covetails A) (s t : ℝ≥0) (p : 0<s) (h : s ≤ t) :
    jut ω (A t) = T (t-s) (jut ω (A s)) := by
  have hx : A t = T (t-s) * A s * T (t-s) :=
    (congrArg A (add_tsub_cancel_of_le h).symm).trans (w s p _)
  rw [hx,jut,jut,mul_apply_eq_comp,g.1,mul_apply_eq_comp,T_shred S _ g.1]

lemma jut_rebalance (g : Ano S ω)
    (w : S.Covetails A) (c : S.Covetails B)
    {s t u r : ℝ≥0} (p : 0<s) (q : 0<t)
    (l : s ≤ u) (e : t ≤ r) (y : Cross a) :
    inner ℂ (jut ω (A u)) (V y (jut ω (B r))) =
    inner ℂ (jut ω (A s))
      (T ((u-s)+(r-t)) (V y (jut ω (B t)))) := by
  rw [jut_later S ω A g w _ _ p l, jut_later S ω B g c _ _ q e,
    ←ContinuousLinearMap.adjoint_inner_right,S.sym,
    S.time, ← ContinuousLinearMap.comp_apply (V y) (T (r-t)),←S.independent]
  rfl

/-- Still exposed at some strictly shorter common calendar spend (as short as
desired but fixed before any limits). No spectral assumption on spatial charge.
Helpful since we also want *spacelike* Mink readings even without cone
spectrum or covariance yet. -/
lemma downshift (g : Ano S ω)
    (w : S.Covetails A) (c : S.Covetails B)
    {s t : ℝ≥0} (p : 0<s) (q : 0<t) (y : Cross a)
    (u : inner ℂ (jut ω (A s)) (V y (jut ω (B t))) ≠ 0)
    (d : ℝ≥0) (h : 0<d) :
    ∃ r : ℝ≥0, 0<r ∧ r<d ∧ inner ℂ (jut ω (A r)) (V y (jut ω (B r))) ≠ 0 := by
  let e := min d (min s t)/2
  have pe : 0<min d (min s t) := lt_min h (lt_min p q)
  have ke : 0<e := half_pos pe
  have he : e ≤ d/2 := by
    exact div_le_div_of_nonneg_right (min_le_left ..) zero_le_two
  have le := half_lt_self pe
  have lc : e<s := le.trans_le ((min_le_right ..).trans (min_le_left ..))
  have lt : e<t := le.trans_le ((min_le_right ..).trans (min_le_right ..))
  rw [jut_rebalance S ω A B g w c ke ke lc.le lt.le y] at u
  have x : 0 < s-e+(t-e) := add_pos (tsub_pos_of_lt lc) (tsub_pos_of_lt lt)
  obtain ⟨r,l,n⟩ := paid_move_heat S x u (le_refl _) (show (0:ℝ)<d from h)
  have rl : 0 < r := l.1
  have ru : r < d := l.2

  have er : e ≤ e+r/2 := self_le_add_right ..
  refine ⟨e+r/2,ke.trans_le er,?_,?_⟩
  · refine (add_lt_add_of_le_of_lt he ((div_lt_div_iff_of_pos_right (zero_lt_two' ℝ≥0)).mpr ru)).trans_eq (add_halves _)
  rwa [jut_rebalance S ω A B g w c ke ke er er y, add_tsub_cancel_left, add_halves]
end Eu

end YM.OS.Semigroup.Gingham
