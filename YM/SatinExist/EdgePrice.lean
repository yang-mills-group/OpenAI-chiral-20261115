import YM.SatinExist.Unpad

/-! ## Angular retrieval. Extra analytic bill at stamp level.
    Each (1+E)-price bill can be consumed once in the INTERIOR. Later we'll prove
    continuity for a Mink continuation. -/

set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)(x:H)
local notation "ρ" => volume.restrict (Ioi (0:ℝ))
local notation "R" => StampPower S
local notation "F" => S.F
variable (z:ℂ) (g:z∈inside)
include g

-- generator calculus at this mark budget (bounded stamp, not assuming operator
-- holomorphy at the boundary). Sign note. Argument z positive cost;
-- Wick λ=s imag at s<0 therefore.

private lemma filling(t:ℝ) (p:0< t):
  HasDerivAt (fun v:ℝ=> S.F z (S.E v.toNNReal x)) (deriv S.F z (S.E t.toNNReal x)) t:=by
 let y:= (t:ℂ); have hv: y∈inside:=p; let K:= S.E t.toNNReal x; let f(r:ℂ):= S.F (z+r) x
 have h : HasDerivAt f (deriv S.F z K) y := by
   let Y(w:ℂ):= w-y+z
   have hp':Y y=z:=by simp [Y]
   let a:(ℂ→H):= fun z=> S.F z K
   have he: HasDerivAt a (deriv S.F z K) z:= (ContinuousLinearMap.apply ℂ H.space K).hasFDerivAt.comp_hasDerivAt z (S.localHeat _ g|>.differentiableAt.hasDerivAt)
   have heq(a:ℂ)(p:Y a∈inside): f a=S.F (Y a) K:=by
      unfold f K; rw [show z+a=Y a + y from (by unfold Y; abel), S.pairs p hv,branch_eq_heat S t (show 0< t from hv)]; rfl
   have H:HasDerivAt Y 1 y:= ((hasDerivAt_id' y).sub_const _).add_const _
   simpa only [one_smul] using (he.scomp_of_eq y H hp'.symm).congr_of_eventuallyEq (((show ContinuousAt Y y from H.continuousAt).tendsto.eventually (show inside∈𝓝 (Y y) from hp'.symm ▸ open_inside.mem_nhds g)).mono fun t u=> heq t u)
 have he:HasDerivAt (fun t:ℝ=> f ↑t) (deriv S.F z K) t:=by
    simpa [Function.comp_def] using! (show HasDerivAt _ _ t from (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (ofRealCLM.hasDerivAt (x:=t)))
 apply he.congr_of_eventuallyEq; filter_upwards [Ioi_mem_nhds p] with t ht; unfold f; rw [S.pairs g (show (t:ℂ)∈inside from ht),branch_eq_heat S t ht]; rfl

-- Money path
private abbrev α(t:ℝ):ℂ:= ↑(thermalMass n t)
private abbrev Y(t:ℝ):H:= α n t • S.E t.toNNReal x
private def J(t:ℝ): H:= (F z) (Y S n x t)
local notation "D" => deriv S.F

omit g in
private lemma Jcon : Continuous (J S n x z):=by
 let q:=F z; have h:Continuous (thermalMass n):=by unfold thermalMass; fun_prop
 exact q.continuous.comp ((continuous_ofReal.comp h).smul ((S.continuousE x).comp continuous_real_toNNReal))

omit g in
private lemma Jworth (A:H.Op): Integrable (fun t=> A (Y S n x t)) ρ:= A.integrable_comp (heft S n x)
omit g in
private lemma rvalue (A:H.Op): (∫ t,A (Y S n x t)∂ ρ)= A (StampPower S n x) := (ContinuousLinearMap.integral_comp_comm _ (heft S n x))

-- differentiate both steps
private lemma Jdiff {t:ℝ} (p:0< t){h':ℂ}(h:HasDerivAt (α n) h' t):
    HasDerivAt (J S n x z) (h' • F z (S.E t.toNNReal x) + D z (Y S n x t)) t:=by
 unfold J Y; simp_rw [map_smul]; rw [add_comm]; exact h.smul (filling S x z g t p)

omit g in
private lemma alpha_S {t:ℝ}: HasDerivAt (α (n+1)) (α n t-α (n+1) t) t:=by
 have hq: HasDerivAt (thermalMass (n+1)) (thermalMass n t-thermalMass (n+1) t) t := by
    have he:= ((((hasDerivAt_id' t).neg.exp).mul ((hasDerivAt_id' t).pow (n+1))).div_const ((↑(n+1).factorial):ℝ))
    refine he.congr_deriv ?_
    unfold thermalMass; simp only [Pi.pow_apply,Pi.neg_apply, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
 unfold α; simpa only [ofReal_sub] using hq.ofReal_comp
omit g in
private lemma α_z(t:ℝ): HasDerivAt (α 0) (- α 0 t) t:=by
 have he: HasDerivAt (thermalMass 0) (- thermalMass 0 t) t:=by
    unfold thermalMass; simpa using (hasDerivAt_id' t).neg.exp
 unfold α; simpa only [ofReal_neg] using he.ofReal_comp

lemma interest_base : deriv S.F z (StampPower S 0 x)= S.F z (StampPower S 0 x) - S.F z x:=by
 let Z:=J S 0 x z; let Z'(t):= D z (Y S 0 x t) - F z (Y S 0 x t); let u:= Jworth S 0 x (F z);
 have he(t:ℝ)(h:t∈Ioi 0):HasDerivAt Z (Z' t) t:=by
     convert Jdiff S 0 x z g h (α_z t) using 1
     unfold Z' Y; simp [sub_eq_neg_add, add_comm] -- tune
 have p:Integrable Z' ρ:= (Jworth S 0 x (D z)).sub u
 have hp:= integral_Ioi_of_hasDerivAt_of_tendsto (Jcon S 0 x z).continuousAt.continuousWithinAt he p (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi he p u)
 have hx: Z 0= F z x:=by simp [Z,J,Y,α,thermalMass,S.eZero]
 change (∫ t,Z' t∂ ρ)=0-Z 0 at hp; unfold Z' at hp
 rw [integral_sub (Jworth ..) u, rvalue, rvalue,hx, zero_sub] at hp; rw [sub_eq_iff_eq_add] at hp; rw [hp]; abel

lemma interest_higher : deriv S.F z (StampPower S (n+1) x)= S.F z (StampPower S (n+1) x) - S.F z (StampPower S n x):=by
 let N:=n+1; let u:= Jworth S n x (F z); let u':= Jworth S N x (F z)
 let Z:= J S N x z; let Z'(t):= (F z (Y S n x t)-F z (Y S N x t)) + D z (Y S N x t)
 have he(t:ℝ)(h:t∈Ioi 0):HasDerivAt Z (Z' t) t:=by
    convert Jdiff S _ x z g h (alpha_S n) using 1
    unfold Z' Y N; simp [sub_smul]
 have p:Integrable Z' ρ:= (u.sub u').add (Jworth S N x (D z))
 have hx:Z 0=0:=by simp [Z,J,Y,α,thermalMass,N]
 have hp:= integral_Ioi_of_hasDerivAt_of_tendsto (Jcon S N x z).continuousAt.continuousWithinAt he p (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi he p u')
 change (∫ t,Z' t∂ ρ)=0-Z 0 at hp; unfold Z' at hp
 rw [integral_add (f:=fun t=> (F z) (Y S n x t) - (F z) (Y S N x t)) (u.sub u') (Jworth S N x _), integral_sub u u', rvalue,rvalue,rvalue,hx, sub_zero] at hp
 exact (eq_neg_of_add_eq_zero_right hp)|>.trans (by abel) -- tune order
end YM.SatinJets
