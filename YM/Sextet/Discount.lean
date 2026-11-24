import YM.Sextet.Mul
import YM.SU5.Cheer.Pavilion
 
/-!
# Heat and spatial multipliers for the exact signal kernel
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sextet
open Filter Function Set MeasureTheory Mink OS.Semigroup.Balloon Spectral.PVM
open scoped NNReal BigOperators InnerProductSpace

/-- Euclidean heat and plane costs, discounts at all time coordinates clamped to
nonnegative. `p` never set to zero by hand; clamp of a negative coordinate means
evaluation at **zero** time-energy there. -/
def phasor (y:Space3) (k:Space3) : ℂ :=
  Complex.exp (↑⟪k,y⟫_ℝ*Complex.I)

def shade (t:ℝ≥0) (ω:ℝ) : ℝ := Real.exp (-(↑t*max 0 ω))

def charge (t:ℝ≥0) (p:E4) : ℂ := shade t (time p)

def flightTag (y:Space3) (t:ℝ≥0) (p:E4) := phasor y (spatial p) * charge t p

def lessLight (t:ℝ≥0) : E4→ℂ := 1 - charge t

def signalTag (a:ℝ≥0) (y:Space3) (t:ℝ≥0) : E4→ℂ :=
  flightTag y t * lessLight a * lessLight a

section Properties
variable (y:Space3) (t a:ℝ≥0) (p:E4)
lemma phasor_one (k:Space3) : ‖phasor y k‖=1 := by simp [phasor,Complex.norm_exp]
lemma phasor_zero (k:Space3) : phasor y 0=1 ∧ phasor 0 k=1 := by simp [phasor]
lemma shade_lt (ω:ℝ) (h:0<ω) (u:0<t) : shade t ω < 1 := by
  rw [shade,max_eq_right h.le,Real.exp_lt_one_iff]
  exact neg_neg_of_pos (mul_pos (NNReal.coe_pos.mpr u) h)
lemma shade_pos (ω:ℝ) : 0<shade t ω := Real.exp_pos _
lemma shade_le (ω:ℝ) : shade t ω≤1 := Real.exp_le_one_iff.mpr
  (neg_nonpos.mpr (mul_nonneg t.property (le_max_left _ _)))
lemma charge_bound : ‖charge t p‖≤1 := by
  rw [charge,Complex.norm_real,Real.norm_of_nonneg (shade_pos ..).le]; exact shade_le ..
lemma flight_zero : flightTag 0 t=charge t := funext fun p=>by
  rw [flightTag,(phasor_zero 0 _).2,one_mul]
lemma flight_bound : ‖flightTag y t p‖≤1 := by
  unfold flightTag; rw [norm_mul,phasor_one,one_mul]; exact charge_bound ..
lemma less_eq_real : lessLight t p=↑(1-shade t (time p)) := by simp [lessLight,charge]
lemma less_zero (h:time p≤0) : lessLight t p=0 := by simp [less_eq_real,shade,max_eq_left h]
lemma less_ne_zero (h:0<time p) (u:0<t) : lessLight t p≠0 := by
  rw [less_eq_real]; exact_mod_cast sub_ne_zero.mpr (shade_lt t _ h u).ne'
lemma less_bound : ‖lessLight t p‖≤1 := by
  rw [less_eq_real,Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (shade_le ..))]
  exact sub_le_self _ (shade_pos ..).le
lemma signal_bound : ‖signalTag a y t p‖≤1 := by
  simp only [signalTag, Pi.mul_apply, norm_mul]
  exact mul_le_one₀ (mul_le_one₀ (flight_bound ..) (norm_nonneg _) (less_bound ..))
    (norm_nonneg _) (less_bound ..)

-- `[fun_prop]` general all-continuity arguments.
variable {α:Type*} [TopologicalSpace α] (f:α→Space3) (g:α→ℝ≥0) (q:α→E4)
@[fun_prop] lemma phasor_cont (k:α→Space3) (h:Continuous f) (t:Continuous k) :
    Continuous (fun x=>phasor (f x) (k x)) := by unfold phasor; fun_prop
@[fun_prop] lemma shade_cont (w:α→ℝ) (h:Continuous g)(t:Continuous w) :
    Continuous (fun x=> shade (g x) (w x)) := by unfold shade; fun_prop
@[fun_prop] lemma charge_cont (h:Continuous g) (t:Continuous q) :
    Continuous (fun x=>charge (g x) (q x)) := by
  have : Continuous (fun x=>time (q x)):=clock_cont.comp t
  unfold charge; fun_prop
@[fun_prop] lemma flight_cont (h:Continuous f) (t:Continuous g) (e:Continuous q) :
    Continuous (fun x=>flightTag (f x) (g x) (q x)) := by
  have : Continuous (fun x=>spatial (q x)):=rest_cont.comp e
  unfold flightTag; fun_prop
@[fun_prop] lemma less_cont (t:Continuous g) (e:Continuous q) :
    Continuous (fun x=>lessLight (g x) (q x)) := by simp only [lessLight,Pi.sub_apply,Pi.one_apply]; fun_prop
@[fun_prop] lemma signal_cont (a:α→ℝ≥0) (h:Continuous f) (t:Continuous g) (e:Continuous q)
    (u:Continuous a) :
    Continuous (fun x=>signalTag (a x) (f x) (g x) (q x)) := by
  simp only [signalTag,Pi.mul_apply]; fun_prop
lemma charge_cost : Cost (charge t) :=
  ⟨(by fun_prop),1,zero_le_one,charge_bound t⟩
lemma less_cost : Cost (lessLight t) := Cost.one.sub (charge_cost t)
lemma flight_cost : Cost (flightTag y t) :=
  ⟨(by fun_prop),1,zero_le_one,flight_bound y t⟩
lemma signal_cost : Cost (signalTag a y t) := ((flight_cost y t).mul (less_cost a)).mul (less_cost a)

lemma phasor_shore : phasor y (spatial p) = Boundary.Probe.plane p (Cheer.shore y:E4) := by
  simp [phasor,Boundary.Probe.plane,Cheer.shore, pairing]
lemma charge_bright (g:0 ≤ time p) : charge t p=(tinct timeAxis t p:ℂ) := by
  unfold charge shade tinct; rw [max_eq_right g]; rfl
end Properties

/-- Nonpositive time energies (on PVM support the zero face). -/
def darkSet : Set E4 := {p | time p ≤ 0}
lemma dark_set : MeasurableSet darkSet := (isClosed_le clock_cont continuous_const).measurableSet

variable {H:Hilbert} (S:OS.Semigroup H timeAxis) (a t:ℝ≥0) (y:Space3)
local notation "Q"=> S.ℚmeasure
lemma valued_flight : (Q).Valued (flightTag y t) ((S.U (Cheer.shore y)).comp (S.E t)) := by
  intro v
  refine (during S t (Cheer.shore y) v).trans (integral_congr_ae ?_)
  filter_upwards [S.bright v] with p hp
  show _ = phasor y (spatial p)*charge t p
  rw [charge_bright _ _ hp, phasor_shore]
lemma flight_op : (Q).price (flightTag y t)=(S.U (Cheer.shore y)).comp (S.E t) :=
  ((Q).price_spec (flight_cost ..)).unique (valued_flight S t y)
lemma shore_zero : Cheer.shore 0=0 := by
  exact Subtype.ext (show position 0 0=(0:E4) from by
    apply PiLp.ext; intro i; refine Fin.lastCases ?_ (fun j=>?_) i
    · exact time_position ..
    simp [position])
lemma charge_op : (Q).price (charge t)=S.E t := by
  rw [←flight_zero,flight_op,shore_zero,S.uZero]; rfl
lemma less_op : (Q).price (lessLight t)= ContinuousLinearMap.id ℂ (H.space) - S.E t := by
  rw [lessLight,(Q).price_sub Cost.one (charge_cost t),(Q).price_one,charge_op]
lemma price_dark {f:E4→ℂ} (hf:Cost f) (v:H) :
    (Q).region darkSet ((Q).price (f*lessLight t) v)=0 := by
  rw [←ContinuousLinearMap.comp_apply,
    ←(Q).price_restrict (hf.mul (less_cost _)) dark_set]
  have k: darkSet.indicator (f*lessLight t)=fun _=>0 := by
    funext p; by_cases h:p∈darkSet
    · rw [indicator_of_mem h, Pi.mul_apply, less_zero _ _ h, mul_zero]
    exact indicator_of_notMem h _
  rw [k,(Q).price_const, zero_smul,zero_apply]
lemma less_dark (v:H) : (Q).region darkSet (v-S.E t v)=0 := by
  have h:=price_dark S t Cost.one v
  rw [one_mul,less_op] at h; exact h

/-- Paired kernel spectral formula. -/
lemma signal_formula (v w:H) :
    inner ℂ (v-S.E a v) (S.U (Cheer.shore y) (S.E t (w-S.E a w)))=
      (Q).crossIntegral v w (signalTag a y t) := by
  let L := (Q).price (lessLight a)
  let F := (Q).price (flightTag y t)
  have hL: (fun x=>star (lessLight a x))= lessLight a := by funext p; simp [less_eq_real]
  have l:L.adjoint=L := by unfold L;rw [←(Q).price_conj (less_cost _), hL]
  have c:L.comp F=F.comp L:=(Q).price_commutes (less_cost _) (flight_cost ..)
  suffices h : inner ℂ (L v) (F (L w))= _ by
    unfold L F at h
    rw [less_op,flight_op] at h; exact h
  calc _ = inner ℂ v (L (F (L w))) := by nth_rw 1 [←l]; rw [ContinuousLinearMap.adjoint_inner_left]
       _ = _ := by
         rw [(Q).crossIntegral_spec v w (signal_cost ..),signalTag,
           (Q).price_mul ((flight_cost ..).mul (less_cost _)) (less_cost _),
           (Q).price_mul (flight_cost ..) (less_cost _),←ContinuousLinearMap.comp_apply L F, c]
         rfl
end YM.Sextet
