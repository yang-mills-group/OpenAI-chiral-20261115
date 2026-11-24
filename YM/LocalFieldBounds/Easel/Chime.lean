import YM.LocalFieldBounds.Easel.Gallery

/-!
# Conducting

A portable recipe to print at *one* regulator height in the election.
All that remains to connect this part to the crossing prices is verifying
the calls to Eu joint and marginal prices, and the actual footprints.
-/
noncomputable section
namespace YM.LocalFieldBounds.Easel
open Function Filter Set MeasureTheory
open OS OS.Semigroup SatinRegistration SatinWFixed Carton
open GarnetAct.Cut Boundary Probe
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Classical Topology NNReal InnerProductSpace ComplexOrder

variable {H : Hilbert} {S : OS.Semigroup H timeAxis} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (B : Carton S V)

open ConePrice.Sail


variable (w : ℝ≥0)

abbrev stage (p q : Paper) : ℝ := q 3 - p 3 - 2*w

open Marble
variable (J : JMap V) (z : Remembers B J) (a b : V)

/-- Continuum reply to a joint poll. -/
abbrev spear (p q : Paper) :=
  hotPair S B.omega (stage w p q)
    (beacon B a (horizon p) w) (beacon B b (horizon q) w)

/-- Charge a point pose via finite Eu lag interpolation in this interval,
costing at moved positions inside the apertures. -/
structure Coin (p q : Paper) (r e : ℝ) extends Stamp (stage w p q) (stage w p q+r) where
  cover : toStamp.Covers (halo w p q) e
  gap : 0 ≤ stage w p q

namespace Coin
variable {w} {p q : Paper} {r e : ℝ} (t : Coin w p q r e)

/-- New second position, unchanged spatially. -/
abbrev eighth (j : t.Job) :=
  Offset q ((t.step j).val - stage w p q)

lemma always (h : 0 ≤ stage w p q) (hp : 0 < w) (he : 0 < e) (hr : 0 < r) :
    Nonempty (Coin w p q r e) :=
  let ⟨c,hc⟩ := Stamp.afforded h (lt_add_of_pos_right _ hr) _ (halo_inside w hp p q) e he
  ⟨⟨c,hc,h⟩⟩

lemma moves (j : t.Job) : dist (t.eighth j) q ≤ r :=
  length_Offset q (sub_nonneg.2 (t.step j).property.1.le) (sub_le_comm.mp
    (sub_le_iff_le_add.2 (t.step j).property.2.le))

lemma phase_time (j : t.Job) :
    stage w p (t.eighth j) = (t.step j).val := by
  unfold stage eighth
  rw [timer]
  ring

abbrev bank (g : Paper → Paper → ℂ) :=
  ∑ j, t.fee j * g p (t.eighth j)

lemma bank_const (x : ℂ) : t.bank (fun _ _ => x) = x := by
  unfold bank
  rw [← Finset.sum_mul,t.normalized,one_mul]

variable (hw : 0<w)
local notation "va" => Whorl B w (J a) (horizon p)
local notation "vb" => Whorl B w b (horizon q)

include z
lemma first :
    t.bank (spear B w a b) =
    inner ℂ va (t.expense S vb) := by
  unfold bank spear
  simp_rw [hot_pay, phase_time, eighth, still, beacon_left B J z]
  change (∑ j, t.fee j * inner ℂ va (S.E (t.step j).val.toNNReal vb)) = _
  unfold Stamp.expense
  simp_rw [sum_apply, smul_apply, inner_sum,
    inner_smul_right]

include hw
lemma err :
    ‖t.bank (spear B w a b) - couple B w J a b p q‖ ≤
       ‖B.bar w (J a) B.omega‖ * (e * ‖B.bar w b B.omega‖) := by
  rw [first B J z, couple, kite _ _ _ _ _ _ hw, ← inner_sub_right,
    ← sub_apply, ← whorl_tame B w (J a) (horizon p),
    ← whorl_tame B w b (horizon q)]
  have he := t.interpolate S t.gap _ (halo_inside w hw p q) t.cover
  exact (norm_inner_le_norm ..).trans <| mul_le_mul_of_nonneg_left
    (((t.expense S - phase S _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right he.le (norm_nonneg _)))
    (norm_nonneg _)

end Coin

abbrev dust (n : ℕ) := 1/(n+1:ℝ)

variable {F G : Curtain} {n : ℕ}
/-- Combined coupon: mending A, C offered first. -/
structure Song (A : Coat F n) (C : Coat G n) where
  coin (i : A.Job) (j : C.Job) : Coin w (A.note i) (C.note j) w (dust n)

namespace Song

lemma afforded (A : Coat F n) (C : Coat G n) (h : 0<w)
    (v : ∀ p∈F.boxS, ∀ q∈G.boxS, 2*(w:ℝ) ≤ q 3-p 3) :
    Nonempty (Song w A C) :=
  ⟨⟨fun i j => (Coin.always (sub_nonneg.mpr (v _ (A.stays i) _ (C.stays j))) h
    (by unfold dust; positivity) (by exact h)).some⟩⟩

variable {w} {A : Coat F n} {C : Coat G n} (t : Song w A C)

/-- The finite linear combination of calls inside the apertures which will
be used on Mark prices. The same transform applies to marginal-price and
product-of-marginals costs there. -/
abbrev play (g : Paper → Paper → ℂ) :=
  sampling A C (fun i j => (t.coin i j).bank g)

lemma pitch (x : ℂ) :
    sampling A C (fun _ _ => x) = x := by
  unfold sampling
  simp only [Complex.ofReal_mul, ←Finset.sum_mul, ←Finset.mul_sum,
    ←Complex.ofReal_sum,A.tender,C.tender]
  simp

lemma constant (x : ℂ) :
    t.play (fun _ _ => x) = x := by
  unfold play
  simp_rw [Coin.bank_const]
  exact pitch _

lemma sampling_bound (e : ℝ) (v g : A.Job → C.Job → ℂ)
    (p : ∀ i j, ‖v i j - g i j‖ ≤ e) :
    ‖sampling A C v - sampling A C g‖ ≤ e := by
  unfold sampling
  simp_rw [← Finset.sum_sub_distrib]
  let k (i) (j) := (A.ink i*C.ink j)
  have h (i) (j) : 0 ≤ k i j :=
    mul_nonneg (A.weight i) (C.weight j)
  refine le_trans ?_ (le_of_eq ?_: (∑ i, ∑ j, k i j*e) ≤ e)
  · refine (norm_sum_le ..).trans <| Finset.sum_le_sum fun i _ =>
      (norm_sum_le ..).trans <| Finset.sum_le_sum fun j _ => ?_
    rw [← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (h _ _)]
    exact mul_le_mul_of_nonneg_left (p ..) (h ..)
  unfold k
  simp only [←Finset.sum_mul, ←Finset.mul_sum, C.tender, A.tender, one_mul]

include z in
lemma precise (h : 0 < w) :
    ‖t.play (spear B w a b) -
        sampling A C (fun i j => couple B w J a b (A.note i) (C.note j))‖ ≤
    ‖B.bar w (J a) B.omega‖ * (dust n * ‖B.bar w b B.omega‖) :=
  sampling_bound _ _ _ fun i j => (t.coin i j).err B J z a b h


section replies
/- Let an arbitrary Eu witness be approved point by point, including the
perturbations of each gap by 0..w on the second argument.
Just requiring the eventual approximation at a common height.
-/
variable {α : ℕ → Paper → Paper → ℂ} {v : Paper → Paper → ℂ}
lemma uplift
    (h : ∀ (i : A.Job) (j : C.Job) (k : (t.coin i j).Job),
      Tendsto (fun n => α n (A.note i) ((t.coin i j).eighth k)) atTop
        (𝓝 (v (A.note i) ((t.coin i j).eighth k)))) :
    Tendsto (fun n => t.play (α n)) atTop (𝓝 (t.play v)) := by
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  let ω := t.coin i j
  exact Tendsto.const_mul _
    (tendsto_finsetSum _ (fun k _ => Tendsto.const_mul _ (h i j k)))

lemma under (v g : Paper → Paper → ℂ) : t.play v - t.play g =
    t.play (fun p q => v p q - g p q) := by
  unfold play sampling Coin.bank
  simp_rw [←Finset.sum_sub_distrib, ←mul_sub, ←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]

lemma agrees {a b : Paper → Paper → ℂ}
    (h : ∀ (i : A.Job) (j : C.Job) (k : (t.coin i j).Job),
      a (A.note i) ((t.coin i j).eighth k) = b (A.note i) ((t.coin i j).eighth k)) :
    t.play a = t.play b := by
  unfold play sampling Coin.bank
  simp_rw [h]

end replies
end Song

variable {R : InkWaves V} {W : WView V} (t : InkPort B R W)
variable (A : ∀ n, Coat F n) (C : ∀ n, Coat G n)
local notation "goal" => W.expect [(a,film F),(b,film G)]
local notation "cue" => spear B w a b

include z in
theorem pay_focus (h : 0<w) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ n in atTop, ∀ D : Song w (A n) (C n), dist (D.play cue) (focus B w J a b F G) < ε := by
  let v := ‖B.bar w (J a) B.omega‖
  let u := ‖B.bar w b B.omega‖
  have s : Tendsto (fun n => v*(dust n*u)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const u).const_mul v
  filter_upwards [s.eventually (gt_mem_nhds (half_pos he)),
    (Metric.tendsto_nhds.1 (sail B w J a b A C h) _ (half_pos he))] with n d p D
  exact lt_of_le_of_lt (dist_triangle _ _ _) (lt_of_lt_of_eq
    (add_lt_add
      ((le_trans (le_of_eq (dist_eq_norm ..)) (D.precise B J z a b h)).trans_lt d) p)
    (add_halves _))

include t z
theorem cue_goal {ε : ℝ} (he : 0<ε) :
    ∀ᶠ y in 𝓝[>] (0:ℝ≥0), ∀ᶠ n in atTop, ∀ D : Song y (A n) (C n),
      dist (D.play (spear B y a b)) goal < ε := by
  filter_upwards [self_mem_nhdsWithin (s:=Ioi 0),
    (((sea B t J a b z F G).eventually
      (Metric.ball_mem_nhds goal (half_pos he))).filter_mono nhdsWithin_le_nhds)]
      with y p v
  filter_upwards [pay_focus B y J z a b A C p (half_pos he)] with n h D
  exact lt_of_le_of_lt (dist_triangle _ _ _) ((add_lt_add (h D)
    (Metric.mem_ball.mp v)).trans_eq (add_halves _))

#print axioms cue_goal
#print axioms Song.afforded
end YM.LocalFieldBounds.Easel
