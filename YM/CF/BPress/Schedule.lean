import YM.CF.BPress.Bands
import YM.CF.BPress.Scale
/-! Numerical choices eq:B-dy. Use a Borel tail? No measurability in coupling
is needed; all measurable objects in the marks can take these parameters fixed.
`Eventually` throughout in y so privileges uniform in any true history, j, n. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Lattice Filter Pressure
open scoped Topology Classical

/-- ceil to multiple power of two, saturating below 1 -/
def ceilDyad (x : ℝ) := Nat.find (show ∃ k : ℕ, x ≤ 2^k from Exists.imp (fun _ p=>le_of_lt p) (pow_unbounded_of_one_lt x one_lt_two))
lemma ceilDyad_ge (x : ℝ) : x ≤ (2:ℝ) ^ ceilDyad x:= by unfold ceilDyad; exact Nat.find_spec (p:=fun k : ℕ => x ≤ 2^k) _
lemma ceilDyad_pos {x : ℝ} (h : 1<x) : 0 < ceilDyad x:= by by_contra! hh; have e:=ceilDyad_ge x; rw [Nat.eq_zero_of_le_zero hh,pow_zero] at e; linarith
lemma ceilDyad_lt {x : ℝ} (h : 1<x) : (2:ℝ)^ceilDyad x < 2*x:= by
 obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (ceilDyad_pos h).ne'; have hX:k<ceilDyad x:=by omega
 have hs : (2:ℝ)^k < x:= lt_of_not_ge (Nat.find_min _ hX); rw [hk,pow_succ']; gcongr

/-- fixed band parameters; w0 purchased sufficiently large earlier. -/
structure GapSize where
  blank : Side
  collar : ℕ
  grid : blank.val ∣ collar
namespace GapSize
variable (w : GapSize)
def rP (y : ℝ) := ceilDyad ((temp y)⁻¹^2 / (w.blank.val:ℝ))
def rawP (y : ℝ) : ℕ := 2^ (w.rP y) * w.blank.val
lemma extent : Tendsto (fun y : ℝ=> (temp y)⁻¹^2) atTop atTop :=
    (tendsto_pow_atTop (by omega : (2:ℕ)≠0)).comp (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨npl_temp.drop,(eventually_gt_atTop (0:ℝ)).mono fun _ p=> temp_pos p⟩))
lemma bounds : ∀ᶠ y in atTop, 1 ≤ w.rP y ∧ (temp y)⁻¹ ^2 ≤ w.rawP y ∧ (w.rawP y:ℝ)<2*(temp y)⁻¹^2 := by
 have hb : 0<(w.blank.val:ℝ):=by exact_mod_cast w.blank.property
 filter_upwards [extent.eventually_gt_atTop (w.blank.val:ℝ)] with y t
 let z:=(temp y)⁻¹^2
 have hp : 1 < z/(w.blank.val:ℝ):=(one_lt_div hb).mpr t
 have hu:=ceilDyad_ge (z/(w.blank.val:ℝ)); have he:=ceilDyad_lt hp
 refine ⟨ceilDyad_pos hp,?_ ,?_⟩ <;> unfold rawP rP <;> push_cast
 · exact (div_le_iff₀ hb).mp hu
 rw [←mul_div_assoc] at he; exact (lt_div_iff₀ hb).mp he
lemma raw_late : Tendsto (fun y=>(w.rawP y:ℝ)) atTop atTop:= tendsto_atTop_mono' _ (w.bounds.mono fun _ p=>p.2.1) extent

/-- extension at irrelevant small y by dummy width -/
def select (y : ℝ) : BandWidth where
  blank:= w.blank
  collar:= w.collar
  marked:= ⟨max (w.rawP y-2*w.collar) 1, Nat.zero_lt_one.trans_le (le_max_right ..)⟩
abbrev LQ (y : ℝ) := (w.select y).full
@[simp] lemma blank_select (y : ℝ) : (w.select y).blank=w.blank:= rfl
@[simp] lemma collar_select (y : ℝ) : (w.select y).collar=w.collar:= rfl
@[simp] lemma D_select (y : ℝ) : (w.select y).D=w.blank.val+2*w.collar:=rfl
lemma tail_P : ∀ᶠ y in atTop, (w.select y).P=w.rawP y:= by
 filter_upwards [w.raw_late.eventually_gt_atTop (↑(2*w.collar:ℕ):ℝ)] with y p; have he : 2*w.collar<w.rawP y:=Nat.cast_lt.mp p; change max (w.rawP y-2*w.collar) 1+2*w.collar=w.rawP y; omega
lemma bound_y : ∀ᶠ y in atTop, ((w.select y).P:ℝ) ≤ 2*y:=by
 filter_upwards [w.tail_P,w.bounds,eventually_gt_atTop (0:ℝ)] with y p q h
 rw [p]; refine q.2.2.le.trans (mul_le_mul_of_nonneg_left ?_ zero_le_two); rw [temp_eq,inv_pow,mul_pow,gscale h.le]
 have e:= drift_one y
 refine (inv_le_inv₀ (by positivity) (by positivity)).mpr (show _ from ?_)|>.trans_eq (inv_inv _)
 exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ e)
lemma marked_late : Tendsto (fun y => (((w.select y).marked.val):ℝ)) atTop atTop:=by
 refine (tendsto_atTop_add_const_right _ (-(2*(w.collar:ℝ))) w.raw_late).congr' (w.tail_P.mono fun y g=>?_); rw [←g, BandWidth.P,w.collar_select]; push_cast; ring
lemma LQ_late : Tendsto (fun y=>((w.LQ y).val:ℝ)) atTop atTop := tendsto_atTop_mono (fun i=>Nat.cast_le.mpr (w.select i).marked_lt.le) w.marked_late
lemma grid_P (y : ℝ) : w.blank.val∣ w.rawP y:= dvd_mul_left ..
end GapSize

def rFrame (L : ℝ) (y : ℝ) := ceilDyad (L/(Real.sqrt (temp y)))
def frameWidth (L y : ℝ) : Side := 2^(rFrame L y)
lemma frame_bounds {L : ℝ} (h : 0<L) : ∀ᶠ y in atTop, L/(Real.sqrt (temp y)) ≤ ((frameWidth L y).val:ℝ) ∧ ((frameWidth L y).val:ℝ)< 2*(L/(Real.sqrt (temp y))) := by
 have he : Tendsto (fun y=> Real.sqrt (temp y)) atTop (𝓝 0):= by simpa using npl_temp.drop.sqrt
 filter_upwards [he.eventually (gt_mem_nhds h), eventually_gt_atTop (0:ℝ)] with y p hy
 have h':= temp_pos hy; have k : 1<L/(Real.sqrt (temp y)) := (one_lt_div (Real.sqrt_pos.mpr h')).mpr p
 unfold frameWidth; push_cast; exact ⟨ceilDyad_ge _,ceilDyad_lt k⟩

/-- The dyadic conditions on the periods from eq:B-dy and eq:dyadicH. Later stages can
  impose further integer divisibility by parameters depending on the fixed y.
-/
structure Dyadic {s : Side} (w : GapSize) (L y : ℝ) (X : Bands s (w.select y)) : Prop where
   wide : 1 ≤ w.rP y
   tail : (w.select y).P=w.rawP y
   grid : 2^(w.rP y+1) ∣ X.Q.val
   tiles : 2 * (w.select y).P ∣ s.val
   frame : (frameWidth L y).val ∣ s.val
   fits : 4 * (frameWidth L y).val ≤ s.val
end YM.CF.BPress
