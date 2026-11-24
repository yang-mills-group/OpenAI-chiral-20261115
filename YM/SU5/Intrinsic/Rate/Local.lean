import YM.CF.Scree.Brief
import YM.CF.Beau.Chair
import YM.Next.RANK.Scatter
/-!
# R124 calculations. Rate ledger on the **actual** support and pressure.
Part of an attempt at the intrinsic-detector estimate.
We will increase the exponential rate in the unmarked positive-exterior-degree bill
and control incidence (support membership vs anchor). `PressB` remains at the
same threshold, powers, directions, even choices of cylinder representatives.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scree
open RG Skye Finset Lattice Next.Rank.Thirst
open scoped Classical
/-- Does not change the test bill `PressB`. -/
abbrev surchargeRate (p : BudgetPoint) (a : ℝ) (ha : 0 ≤ a) : BudgetPoint :=
  {p with supportExponent := p.supportExponent + a,
          exponent_pos := add_pos_of_pos_of_nonneg p.exponent_pos ha}

/-- For fixed Large-Hub variant. -/
abbrev plusOneRate (p : BudgetPoint) := surchargeRate p 1 zero_le_one

variable {n : Side}

theorem pressure_unchanged (p : BudgetPoint) (a : ℝ) (ha : 0 ≤ a)
    (i : Hub n) (F : InkD n) (h v : ℝ) :
    PressB (surchargeRate p a ha) i F h v ↔ PressB p i F h v := by
 -- Not defeq (PressB structure head), Signs likewise.
 constructor <;> rintro ⟨u,l,q,m,b,z,y,H⟩ <;> refine ⟨u,l,q,m,b,z,fun U w j => ?_,H⟩ <;>
   obtain ⟨s,t,k⟩ := y U w j <;> exact ⟨s,t,k⟩

/-- Cost on the incidence instead of just the center. -/
structure SupportRate (p : BudgetPoint) (F : RegBudget n) (h C : ℝ) : Prop where
 supportCost : ∃ v : Hub n → ℝ, (∀ i, PressB p i (F i) h (v i)) ∧
      ∀ x : Seat n, (∑ i : Hub n, if x ∈ i.val.2 then p.mass i.val.2 (v i) else 0) ≤ C

open Cube
open Spire

/-- Separation of two seats in the support, buying incidence for just a `1/B`
loss; this is why the `wilt` price below uses `B^2`. -/
theorem seat_near {x : Seat n} {b : ℕ} (hb : 0 < b) (i : Hub n) (hx : x ∈ i.val.2) :
    (↑(separation i.val.1 x / (8 * b^2):ℕ) : ℝ) ≤ (coverNumber b i.val.2:ℝ) / b := by
  have t : (separation i.val.1 x / (8*b^2)) * b ≤ coverNumber b i.val.2 := by
    rw [show 8*b^2 = 8*b*b by ring, ← Nat.div_div_eq_div_mul]; exact
      (Nat.div_mul_le_self ..).trans (book_site b hb i.val.2 i.property hx)
  exact (le_div_iff₀ (Nat.cast_pos.mpr hb)).mpr (by exact_mod_cast t)

private theorem anchor_pos {x : Seat n} (p : BudgetPoint) (v : Hub n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (i : Hub n) :
    0 ≤ if x=i.val.1 then p.mass i.val.2 (v i) else 0 := by
  split
  · exact mul_nonneg (Real.exp_pos _).le (hv _)
  exact le_rfl

/-- Upgrade anchor sum to a true per-site incidence estimate. Applies even
without symmetry assumptions on F; uses no diameter bound on the torus. -/
theorem spend_at_incidence {h a b C : ℝ} {F : RegBudget n} (p : BudgetPoint)
    {Q : Sweep n → Prop} (hh : 0 ≤ h) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + 1/(p.B:ℝ) ≤ b)
    (cost : IncX Q F (surchargeRate p b hb) h C) :
    SupportRate (surchargeRate p a ha) F h (wilt (p.B^2) * C) := by
  obtain ⟨v,hv,w⟩ := cost.weight
  let P := surchargeRate p a ha
  let R := surchargeRate p b hb
  have hp (i : Hub n) : 0 ≤ v i := Beau.grit_p _ (hv i) hh
  refine ⟨v,fun i=> (pressure_unchanged ..).2 ((pressure_unchanged ..).1 (hv i)),?_⟩
  intro x
  let B:=p.B; have hB : 0 < B:=p.B_pos
  let g (y : Seat n) := Real.exp (- (↑(separation y x / (8 * B ^ 2):ℕ) : ℝ))
  have hC : 0 ≤ C:= (sum_nonneg (fun i _=> anchor_pos R v hp (x:=x) i)).trans (w x)
  calc
    _ ≤ ∑ i : Hub n, ∑ y : Seat n, g y * (if y=i.val.1 then R.mass i.val.2 (v i) else 0) := by
      refine sum_le_sum (fun i _=>?_)
      apply le_trans _ (single_le_sum (s:=univ) (fun y _=> mul_nonneg (show 0 ≤ g y from (Real.exp_pos _).le) (anchor_pos R v hp i)) (mem_univ i.val.1))
      rw [if_pos rfl]
      split
      next hx=>
        unfold g
        unfold BudgetPoint.mass
        rw [← mul_assoc, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_right _ (hp i); apply Real.exp_monotone
        let K : ℝ := coverNumber p.B i.val.2
        change (_ + a) * K ≤ _ + (_ + b) * K
        have hc := seat_near hB i hx
        change _ ≤ K / B at hc
        have hx' : a * K + K / p.B ≤ b * K := by
          rw [show a*K + K/p.B = (a+1/(p.B:ℝ))*K by ring]; gcongr
        linarith only [hx',hc]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hp i))
    _ ≤ ∑ y : Seat n, g y*C := by
      rw [sum_comm]; exact sum_le_sum fun i _=>by
        rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (w i) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (range_wilt x (B^2) (by positivity)) hC

/-- Upgrade at a rate near `p.supportExponent`; rather than using Hölder
we need the extra expense only on long supports arbitrarily. -/
theorem trade_rate_far {h a c C D : ℝ} {F F' : RegBudget n} {K : ℕ}
    (p : BudgetPoint) {Q Q' : Sweep n → Prop} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (u : a + c ≤ 1)
    (pfar : ∀ i : Hub n, K < coverNumber p.B i.val.2 → F i=F' i)
    (own : IncX Q F p h C) (addl : IncX Q' F' (plusOneRate p) h D) :
    IncX Q F (surchargeRate p a ha) h
      (Real.exp (a*K)*C + Real.exp (-c*K)*D) := by
  obtain ⟨v,hv,w⟩ := own.weight
  obtain ⟨v',hv',w'⟩:= addl.weight
  have hp(i : Hub n) : 0 ≤ v i := Beau.grit_p _ (hv i) hh
  have hp'(i : Hub n) : 0 ≤ v' i := Beau.grit_p _ (hv' i) hh
  let P := surchargeRate p a ha; let R:=plusOneRate p
  let σ (i : Hub n):Prop:= K < coverNumber p.B i.val.2
  let t (i : Hub n) := if (K < coverNumber p.B i.val.2) then v' i else v i
  let A := Real.exp (a*K)
  let D' := Real.exp (-c*K)
  refine ⟨⟨t, fun i=> (pressure_unchanged ..).2 ?_,?_⟩, own.face⟩
  · unfold t; split
    next hx => rw [pfar i hx]; exact (pressure_unchanged ..).1 (hv' i)
    next => exact hv i
  intro x
  calc
    _ ≤ ∑ i : Hub n, (A*(if x=i.val.1 then p.mass i.val.2 (v i) else 0) +
                     D'*(if x=i.val.1 then R.mass i.val.2 (v' i) else 0)) := by
      refine sum_le_sum fun i _ => ?_
      by_cases z : x=i.val.1; swap; · simp only [z, ↓reduceIte, mul_zero, add_zero, le_refl]
      simp only [z, ↓reduceIte]
      let B:=coverNumber p.B i.val.2
      unfold t
      split
      next H=>
        apply le_add_of_nonneg_of_le (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hp i)))
        unfold BudgetPoint.mass D'
        rw [←mul_assoc, ← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (hp' i); apply Real.exp_monotone
        change (p.supportExponent+a)*(B:ℝ) ≤ _+(p.supportExponent+1)*(B:ℝ)
        have Hb : (K:ℝ) ≤ B := Nat.cast_le.mpr H.le
        nlinarith only [mul_le_mul_of_nonneg_right u (Nat.cast_nonneg (α:=ℝ) B), mul_le_mul_of_nonneg_left Hb hc]
      next H=>
        apply le_add_of_le_of_nonneg _ (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hp' i)))
        unfold BudgetPoint.mass A
        rw [←mul_assoc, ← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (hp i); apply Real.exp_monotone
        change (p.supportExponent+a)*(B:ℝ) ≤ _+p.supportExponent*(B:ℝ)
        linarith only [mul_le_mul_of_nonneg_left (show (B:ℝ) ≤ K from Nat.cast_le.mpr (not_lt.mp H)) ha]
    _ ≤ _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]; exact add_le_add
                                                        (mul_le_mul_of_nonneg_left (w x) (Real.exp_pos _).le)
                                                        (mul_le_mul_of_nonneg_left (w' x) (Real.exp_pos _).le)

end YM.CF.Scree
#print axioms YM.CF.Scree.spend_at_incidence
#print axioms YM.CF.Scree.trade_rate_far
