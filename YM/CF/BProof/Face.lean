import YM.CF.BProof.MagnetBounds
import YM.CF.BProof.Strip

/-! Borel angular face rules on horizontal link data (all tangential torus).
Leads chosen measurably. Use separately the nearest-to-identity label adjustment
(for the **after** gauge-fixing core count). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Face
open Function SU Cube Pressure Lattice Wilson Mag Filter Metric Set MeasureTheory
open scoped Matrix.Norms.Frobenius Topology NNReal ENNReal BigOperators Classical
local notation "G" => SU.group

abbrev Sheet (s : Side) := Space s × TAxis → E
abbrev Frame (s : Side) := Space s → E

variable {s : Side}

def react (q : Frame s) (U : Sheet s) : Sheet s := fun i=>q i.1 * U i * (q (i.1+tstep i.2))⁻¹

def read (U : Sheet s) (p : Space s) (i : Fin 3) := let a:=f₁ i; let b:=f₂ i; curl (U (p,a)) (U (p+tstep a,b)) (U (p+tstep b,a)) (U (p,b))
lemma read_eq (U : Sheet s) (p : Space s) (i : Fin 3) (q : Frame s) :
    read (react q U) p i=q p* read U p i * (q p)⁻¹:= by unfold read react curl; dsimp only; rw [add_right_comm p (tstep (f₂ i))]; group
@[fun_prop] lemma read_c (p : Space s) (i : Fin 3) : Continuous (fun U : Sheet s=>read U p i) := by unfold read curl; fun_prop

/-- For reading outside the chart use an extended logG. Off chart tests always fail. -/
def slog (K : Chart G) := (SU.group.shell K.radius).indicator (logG G)
lemma slog_m (K : Chart G) : Measurable (slog K) := by
 apply Measurable.dite (continuousOn_iff_continuous_restrict.mp K.visible |>.measurable) measurable_const (group.shell_meas K.radius) -- tune
lemma slog_leg (K : Chart G) (u : E) (h : group.chord u ≤ K.radius) : slog K u=logG G u := indicator_of_mem (show u∈ group.shell _ from h) _

variable (K : Chart G) (y : ℝ) (U : Sheet s)
def tilt (p : Space s) : Triple := WithLp.toLp 2 (fun i=> (mA y)⁻¹ • slog K (read U p i))
def inChart (p : Space s) := ∀ i, group.chord (read U p i) < K.radius

lemma tilt_conj (p : Space s) (h : inChart K U p) (q : Frame s) : tilt K y (react q U) p=Mag.turn (q p) (tilt K y U p):=by
 refine PiLp.ext fun i=>?_
 change (mA y)⁻¹ • _=group.adjoint (q p) ((mA y)⁻¹ • slog K (read U p i))
 rw [slog_leg _ _ (by rw [read_eq,Gauge.chord_conj]; exact (h i).le), slog_leg _ _ (h i).le,read_eq,K.conjugate _ _ (h i).le, map_smul]

/-- condition eq:B-mood for a given h. The norm is the triple Lie norm. -/
def Mood (p : Space s) (u : E) := inChart K U p ∧ fits (tilt K y U p) u ∧ ‖tilt K y U p-orbit u‖ ≤ allowance y
lemma Mood.alter (p : Space s) (u : E) (q : Frame s) : Mood K y U p u ↔ Mood K y (react q U) p (u*(q p)⁻¹):= by
 unfold Mood; rw [show inChart K (react q U) p=inChart K U p from by unfold inChart; simp only [read_eq,Gauge.chord_conj]]
 apply and_congr_right; intro h; rw [tilt_conj _ _ _ p h,← orbit_move, fits_turn _ _ (q p), ← Mag.turn_sub,turn_norm]

def Follow (u v A : E) := cd G v (u*A) ≤ allowance y
lemma follow_chord (u v A : E) : Follow y u v A ↔ group.chord (u*A*v⁻¹)≤allowance y:=by unfold Follow; rw [←cd_mul_right G v⁻¹, mul_inv_cancel, cd_one]
lemma follow_center (u v A : E) (i : Fin 5) : Follow y (center i*u) (center i*v) A ↔ Follow y u v A := by unfold Follow; rw [_root_.mul_assoc,cd_mul_left]
lemma follow_move (a b u v A : E) : Follow y (u*a⁻¹) (v*b⁻¹) (a*A*b⁻¹) ↔ Follow y u v A := by unfold Follow; rw [show u*a⁻¹*(a*A*b⁻¹)=u*A*b⁻¹ by group,cd_mul_right]

def Lift (h : Frame s) := (∀ p,Mood K y U p (h p)) ∧ ∀ p i, Follow y (h p) (h (p+tstep i)) (U (p,i))
lemma Lift.change (h q : Frame s) : Lift K y U h ↔ Lift K y (react q U) (h*q⁻¹):=by
 unfold Lift; simp_rw [Pi.mul_apply,Pi.inv_apply,←Mood.alter K y U,react,follow_move]

def label (p : Space s) (i : Fin 5) : E := center i * lead (tilt K y U p)
def labels (F : Space s → Fin 5) (p : Space s) := label K y U p (F p)

lemma label_inj (p : Space s) : Injective (label K y U p) := fun _ _ h => center_inj (mul_right_cancel h)
lemma aisle (p : Space s) (i : Fin 5) : orbit (label K y U p i)=orbit (lead (tilt K y U p)):= orbit_center ..
lemma uniforms : ∀ᶠ y:ℝ in atTop,∀ (s:Side)(U:Sheet s) (p : Space s) (u:E), Mood K y U p u → orbit u=orbit (lead (tilt K y U p)) := by
 obtain ⟨c,hc,H⟩:= orbit_unique; filter_upwards [(coin_purchases (a:=0) (b:= -1/8) (c:=0) (by norm_num)).eventually (ge_mem_nhds hc)] with y hy
 intro s U p u h; exact H u _ _ (h.2.2.trans hy) h.2.1 (lead_spec.2 _)
lemma enumeration : ∀ᶠ y:ℝ in atTop,∀ (s:Side)(U:Sheet s) (h:Frame s), Lift K y U h → ∃ F,labels K y U F=h := by
 filter_upwards [uniforms K] with y hy
 intro s U h ht; choose i hi using fun p=> (fiber _ _).mp (hy s U p _ (ht.1 p)).symm
 exact ⟨i,funext fun x=> (hi x).symm⟩

/- meas -/
lemma tilt_c (p : Space s) : Measurable (fun U : Sheet s=> tilt K y U p) := by
 apply (PiLp.continuous_toLp 2 _).measurable.comp -- instances?
 exact measurable_pi_lambda _ fun i=> (measurable_const (a:=(mA y)⁻¹)).smul ((slog_m K).comp (read_c p i).measurable)
lemma mood_c (p : Space s) : MeasurableSet {x : Sheet s × E | Mood K y x.1 p x.2} := by
 let f (x : Sheet s × E) := tilt K y x.1 p; have hf: Measurable f := (tilt_c ..).comp measurable_fst
 unfold Mood; simp only [inChart,setOf_and,setOf_forall]; exact MeasurableSet.inter (.iInter fun i=>(isOpen_lt ((group.continuous_chord.comp (read_c p i)).comp continuous_fst) continuous_const).measurableSet) (.inter ((hf.prodMk measurable_snd) fits_graph.measurableSet) (measurableSet_le (hf.sub (orbit_cont.measurable.comp measurable_snd)).norm measurable_const))
lemma lift_c : MeasurableSet {x : Sheet s × Frame s | Lift K y x.1 x.2} := by
 unfold Lift; simp only [setOf_and,setOf_forall]; refine MeasurableSet.inter (.iInter fun i=> (measurable_fst.prodMk ((measurable_pi_apply (X:=fun _ : Space s=>E) i).comp measurable_snd)) (mood_c K y i)) (.iInter fun p=> .iInter fun i=>?_)
 exact (isClosed_le (f:=fun x : Sheet s × Frame s=> cd G (x.2 (p+tstep i)) (x.2 p*x.1 (p,i))) (by unfold cd; fun_prop) continuous_const).measurableSet
lemma label_c (p : Space s) (i : Fin 5) : Measurable (fun U : Sheet s=>label K y U p i):= measurable_const.mul (lead_spec.1.comp (tilt_c K y p))
lemma labels_c (F : Space s → Fin 5) : Measurable (fun U : Sheet s => labels K y U F) := measurable_pi_lambda _ fun i=> label_c ..

include K -- remove
end YM.CF.BProof.Face
