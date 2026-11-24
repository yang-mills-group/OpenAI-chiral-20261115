import YM.SU5.Reconstruction.FirstWindows.Frame
/-!
# Covariance of all resolution tests for reconstruction: the ACTUAL dense grid

True Euclidean motion on fixed supports. Via the single-representation test space
we move also polynomials finished at finer resolutions for displacement not visible
on their participating levels. No claim of moving arbitrary *contacts* among separately
refined marks. Spectator axes same displacement ruler as supplied clocks (and commute).
Reflection conjugates, including the Cartan part, scoped separately.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open SlabMark MeshClock
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G
local notation "L₀" => Λ.R.L.val
local notation "Γ" => timeMesh Λ

/-- `placement` in physical units (level-zero matter spacing), *grid*, not yet full group -/
def coordinates (Λ : Preparation) : placement Λ →+ RSpace where
  toFun p := fun k=> (p k).val
  map_add' _ _ := rfl
  map_zero' := rfl

def stamps (Λ : Preparation) (s : ℕ) : Cover →+ placement Λ where
  toFun z := fun k=> notch (timeMesh Λ) s (z k)
  map_add' x y := funext (fun k=> notch_add _ s (x k) (y k))
  map_zero' := funext fun _ => notch_zero (timeMesh Λ) s

local notation "ξ" => coordinates Λ
@[simp] lemma coord_at (p : placement Λ) (i : Axis) : coordinates Λ p i = p i := rfl
@[simp] lemma stamps_at (s : ℕ) (x : Cover) (i : Axis) : stamps Λ s x i = notch (timeMesh Λ) s (x i) := rfl

lemma coordinate_injective (Λ : Preparation) : Injective (coordinates Λ) := by
  intro f g h; ext1 i; exact Subtype.ext (congrFun h i)
lemma stamp_injective (Λ : Preparation) (s : ℕ) : Injective (stamps Λ s) := fun _ _ h=>
  funext fun i => notch_tight (timeMesh Λ) s (congrFun h i)

def rescaleGrid (Λ : Preparation) (s t : ℕ) (x : Cover) : Cover := fun i=> castor (timeMesh Λ) s t (x i)
theorem rescale_stamp {s t : ℕ} (p : s ≤ t) (x : Cover) : stamps Λ t (rescaleGrid Λ s t x) = stamps Λ s x :=
  funext fun _ => notch_up (timeMesh Λ) s t p _

theorem stamps_eventually (x : placement Λ) : ∀ᶠ n in atTop, ∃ v, stamps Λ n v=x := by
  obtain ⟨t,-,v,h⟩ := Selected.necklace 0 x
  have hx : stamps Λ t v=x := funext h
  exact (eventually_ge_atTop t).mono fun n e => ⟨rescaleGrid Λ t n v, (rescale_stamp e v).trans hx⟩

theorem coord_dense (Λ : Preparation) : DenseRange (coordinates Λ) := by
  apply DenseRange.piMap (X:=fun i:Axis => (marks (timeMesh Λ))) (fun _ => (daylight (timeMesh Λ)).denseRange_val)

lemma living_scale (s : ℕ) (x : ℤ) : bell (timeMesh Λ) s x =
    ((ruler Λ.block:ℤ):ℝ)*(x:ℝ)*gaugeMesh Λ s := by
  have he := Selected.double_clock_calibration Λ s 1
  unfold bell; simp only [whenly,Nat.cast_one,one_mul,mul_one] at he
  change (x:ℝ) * ((mill Γ s:ℝ≥0):ℝ)=_
  rw [he]; ring

-- Use directly Skew price to move the SAME S: proving this for all x∈streetBox,
-- so can use for unwrapped checking, not recomputing new support of moved mark.
theorem shows_ruler (s : ℕ) (S : Finset Cover) (x : Cover) (y : Cover) (h : y ∈ streetBox (tent Y H) x S) :
    ∃ z ∈ S, gaugePosition Λ s y = gaugePosition Λ s z + coordinates Λ (stamps Λ s x) := by
  obtain ⟨z,u,h⟩ := Selected.drives_shifted Y H x Vacancy.ordinate Vacancy.ordinate_one y h
  refine ⟨z,u,funext fun i=>?_⟩
  unfold gaugePosition; rw [h i,if_pos (Vacancy.ordinates i),Pi.add_apply]; change _= _ + bell (timeMesh Λ) s (x i)
  rw [living_scale]; push_cast; ring

def slides (y : RSpace) (A : Set RSpace) : Set RSpace := (fun x : RSpace => x+y) '' A

@[simp] theorem slides_zero : slides 0 U=U := by ext x; simp [slides]
theorem slides_comp (x y : RSpace) : slides x (slides y U) = slides (x+y) U := by
  unfold slides; rw [Set.image_image]; congr 1; funext i; abel_nf

theorem slides_univ (x : RSpace) : slides x univ=univ := Set.image_univ_of_surjective (add_right_surjective x)

theorem slides_cov (s : ℕ) (S : Finset Cover) (x : Cover) (u : PhaseChoice.SupportedPhysically Λ l s S U) :
    PhaseChoice.SupportedPhysically Λ l s (streetBox (tent Y H) x S) (slides (coordinates Λ (stamps Λ s x)) U) := by
  let B : RSpace := coordinates Λ (stamps Λ s x)
  apply (supported_iff ..).2
  rintro p h; obtain ⟨y,h,v⟩ := Set.mem_iUnion₂.mp h
  obtain ⟨z,b,hz⟩ := shows_ruler Y H s S x y h
  have hw : (p-B) ∈ toMatterUnits '' Tapestry.shield Λ l s z := by
    rw [shield_region_exact] at v ⊢; intro i _; obtain ⟨a,b⟩ := v i (Set.mem_univ i)
    change gaugePosition Λ s z i - _ ≤ p i-B i ∧ p i-B i ≤ gaugePosition Λ s z i + _
    change gaugePosition Λ s y = _+B at hz
    rw [hz,Pi.add_apply] at a b; constructor <;> linarith
  exact ⟨_,(supported_iff ..).1 u (Set.mem_iUnion₂.mpr ⟨z,b,hw⟩), sub_add_cancel _ _⟩

section level

-- `chart` full displacement on ONE level; can compute after streaming entire
-- polynomials upward to a common level, thus all real-grid moves, available
-- because streams commute with this action.
noncomputable def reposition (J : Calibration) (z : Cover) : Dome J →ₗ[ℂ] Dome J where
  toFun x := ⟨Vacancy.chart J z x.val,cad_paid J ordinate ((marque ..).1 x.property) z⟩
  map_add' x y := Subtype.ext (cad_part J z ordinate x.val y.val)
  map_smul' c x := Subtype.ext (cad_scale J z ordinate x.val c)

@[simp] theorem reposition_val (z : Cover) (x : Dome J) :
    (reposition J z x).val=Vacancy.chart J z x.val := rfl

theorem reposition_unit (J : Calibration) (z : Cover) : reposition J z 1=1 := Subtype.ext (cad_unit J z _)

theorem reposition_prod (z : Cover) (x y : Dome J) : reposition J z (x*y)=reposition J z x * reposition J z y :=
  Subtype.ext (cad_prod J _ _)

@[simp] theorem reposition_zero (x : Dome J) : reposition J 0 x=x := Subtype.ext <| cad_zero J ordinate ((marque J).1 x.property)

@[simp] theorem reposition_sum (x : Dome J) (v w : Cover) : reposition J v (reposition J w x) = reposition J (v+w) x :=
  Subtype.ext (cad_plus J _ ((marque J).1 x.property) v w)

lemma here_cov (q : Bool) (U : Set RSpace) (s : ℕ) (z : Cover)
    (f : Dome (tent Y H)) (p : f ∈ insideAt Λ l K q U s) :
    reposition (tent Y H) z f ∈ insideAt Λ l K q (slides (coordinates Λ (stamps Λ s z)) U) s := by
  obtain ⟨⟨S,p,h⟩,t⟩ := (mem_insideAt f s).1 p
  refine (mem_insideAt _ _).2 ⟨⟨_,cad_test z ordinate p, slides_cov Y H s S z h⟩,fun r=>?_⟩
  -- use the formula on strict marks, never repaint against another copy
  let x : Marks (tent Y H) true := ⟨f.val, f.property, fun _ => t r⟩
  rw [reposition_val, show Vacancy.chart K z f.val=(relocateWorld Y H true z x).val from (world_val Y H true z x).symm]
  exact ((marksSpec true _).2 rfl)

include V in
theorem vertical_covariance {s t : ℕ} (_p : s ≤ t) (x : Dome (tent Y H)) (z : Cover) :
    spreadTo Y H G s t (reposition K z x) = reposition K (rescaleGrid Λ s t z) (spreadTo Y H G s t x) := by
  apply Subtype.ext
  simp only [spreadTo_val,reposition_val]
  unfold Vacancy.chart
  suffices h : ∀ I : List Axis,∀ f:Dome (tent Y H), stream Y H G.refine s (t-s) (cad K I z f.val) = cad K I (rescaleGrid Λ s t z) (stream Y H G.refine s (t-s) f.val) by exact h _ x
  intro a f; have ht := ((marque K).1 f.property)
  induction a with
  | nil => rfl
  | cons i a ih =>
    rw [cad_step,cad_step]; unfold relocate gaugeT
    rw [show (K).B=Λ.block from rfl,Tower.chime_X Y H V s i (2*z i) G.history.circuit (cad_paid K a ht z), ih]
    have he : (L₀:ℤ)^(t-s)*(2*z i)= 2*(rescaleGrid Λ s t z i) := by
      change (L₀:ℤ)^(t-s)*_ = 2*((L₀:ℤ)^(t-s)*_); ring
    rw [he]

end level

noncomputable def chooseStamp (p : placement Λ) (s : ℕ) : Cover :=
  if t:∃ v, stamps Λ s v=p then Classical.choose t else 0

@[simp] theorem chooseStamp_eq {s : ℕ} {p} {v : Cover} (h : stamps Λ s v=p) : chooseStamp p s=v := by
  unfold chooseStamp; rw [dif_pos ⟨v,h⟩]; apply stamp_injective (Λ:=Λ); rw [h]; exact Classical.choose_spec (p:=fun v=>stamps Λ s v=p) (by exact ⟨v,h⟩)

/-- Ambient map. Its symmetry law on the net (and even its group law here)
requires ANY common stamps t with p given at t. -/
noncomputable def move (J : Calibration) (p : placement Λ) : Sky J →ₗ[ℂ] Sky J :=
  skySemilinear (fun s => reposition J (chooseStamp p s))

@[simp] theorem move_coe (J : Calibration) (p : placement Λ) (x : ℕ→Dome J) : move J p (↑x)= ↑(fun i=> reposition J (chooseStamp p i) (x i)) := rfl

include V in
lemma move_at (p : placement Λ) (s : ℕ) (f : Dome (tent Y H)) (z : Cover)
    (h : stamps Λ s z = p) :
    move K p (ticket Y H G s f) = ticket Y H G s (reposition K z f) := by
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_ge_atTop s] with t v
  have ht := chooseStamp_eq ((rescale_stamp v z).trans h)
  change reposition K (chooseStamp p t) (spreadTo Y H G s t f)= _
  rw [ht]; exact (vertical_covariance Y H V G v f z).symm

@[simp] theorem move_sum (p q : placement Λ) (x : Sky J) :
    move J p (move J q x) = move J (p+q) x := by
  induction x using Filter.Germ.inductionOn with | _ x => ?_
  rw [move_coe, move_coe, move_coe]; apply Filter.Germ.coe_eq.mpr
  filter_upwards [stamps_eventually p, stamps_eventually q] with i ⟨v,a⟩ ⟨w,b⟩
  have hh : stamps Λ i (v+w)=p+q := by rw [map_add,a,b]
  rw [chooseStamp_eq a,chooseStamp_eq b,chooseStamp_eq hh, reposition_sum]

theorem move_unit (p : placement Λ) : move J p 1 = 1 :=
  Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun _ => reposition_unit J _

@[simp] theorem move_by_zero (Λ : Preparation) (J : Calibration) (x : Sky J) : move J (0:placement Λ) x=x := by
  induction x using Filter.Germ.inductionOn with | _ x => ?_
  rw [move_coe]; apply Filter.Germ.coe_eq.mpr
  apply Eventually.of_forall; intro i; change reposition J (chooseStamp _ i) (x i)=_; rw [chooseStamp_eq (map_zero (stamps Λ i)),reposition_zero]

theorem move_prod (p : placement Λ) (x y : Sky J) : move J p (x*y) = move J p x * move J p y :=
  sky_change_mul (fun s=> reposition J (chooseStamp p s)) (Eventually.of_forall fun _ _ _=>reposition_prod ..) x y

include V in
theorem moving (p : placement Λ) (f : Sky K) (h : f ∈ D q U) :
    move K p f ∈ D q (slides (coordinates Λ p) U) := by
  obtain ⟨s,⟨a,v⟩,x,hx,rfl⟩ := ((stamps_eventually p).and ((domain_eventually Y H G).1 h)).exists
  rw [move_at Y H V G p s x a v,←v]; exact ticket_mem Y H G (here_cov Y H q U s a x hx)

variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Ψ" => osValue Y H V G j C χ

theorem moving_value (p : placement Λ) {f : Sky (tent Y H)} (h : f ∈ D false univ)
    (v : move K p f ∈ D false univ) :
    osValue Y H V G j C χ ⟨move K p f,v⟩ = Ψ ⟨f,h⟩ := by
  obtain ⟨s,⟨a,vz⟩,x,t,rfl⟩ := ((stamps_eventually p).and ((domain_eventually Y H G).1 h)).exists
  rw [show (⟨move K p _,v⟩ : D false Set.univ) = ⟨ticket Y H G s (reposition K a x), ticket_loose ..⟩ from Subtype.ext (move_at Y H V G p s x a vz),os_ticket_val,os_ticket_val,oneAt_reads,oneAt_reads]
  rw [show asLoose K (reposition K a x)= relocateWorld Y H false a (asLoose K x) from Subtype.ext (world_val Y H false a (asLoose K x)).symm,
    world_still]

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
