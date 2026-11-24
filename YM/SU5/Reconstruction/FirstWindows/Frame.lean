import YM.SU5.Reconstruction.FirstWindows.Polynomial
import YM.SU5.Reconstruction.FirstWindows.Compact
/-!
# Actual gauge action on the SINGLE level-to-level test presentation

Check on the physical support in R4, under gauge choices supported ANYWHERE,
no requirement of periodic or finite support. At thinner scales this is the
SAME gauge at that vertex of RSpace now. Check using the same Exhibition and
identity of the workers. No gauge field operators on a Hilbert space implied. -/
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
open Tapestry.Altitude Tapestry.Exhibition
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G

section actions

/-- Useful for all later displacements. `skyChange` is ambient and stays away
from the representative problem. But separately prove the system stays in the right
net region and implements the desired physical operation. -/
noncomputable def skyChange (F : ℕ → Dome J → Dome J) (p : Sky J) : Sky J :=
  Filter.Germ.map' (fun f i=> F i (f i)) (fun _ _ h => h.mono fun i v => congrArg (F i) v) p

@[simp] theorem skyChange_coe (F : ℕ → Dome J → Dome J) (p : ℕ → Dome J) :
    skyChange F (p : Sky J) = ↑(fun i=> F i (p i)) := rfl

theorem sky_change_mul (F : ℕ → Dome J → Dome J)
    (hf : ∀ᶠ i in atTop, ∀ x y, F i (x*y)=F i x*F i y) (p u : Sky J) :
    skyChange F (p*u)=skyChange F p * skyChange F u := by
  induction p using Filter.Germ.inductionOn with | _ p => ?_
  induction u using Filter.Germ.inductionOn with | _ u => ?_
  exact Filter.Germ.coe_eq.mpr <| hf.mono fun i h => h _ _

variable {τ : ℂ →+* ℂ}

noncomputable def skySemilinear (F : ℕ → Dome J →ₛₗ[τ] Dome J) :
    Sky J →ₛₗ[τ] Sky J where
  toFun := skyChange (fun i => F i)
  map_add' p u := by
    induction p using Filter.Germ.inductionOn with | _ p => ?_
    induction u using Filter.Germ.inductionOn with | _ u => ?_
    exact Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun i => map_add (F i) _ _
  map_smul' a x := by
    induction x using Filter.Germ.inductionOn with | _ x => ?_
    exact Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun i => LinearMap.map_smulₛₗ (F i) a _

@[simp] theorem skySemilinear_coe (F : ℕ → Dome J →ₛₗ[τ] Dome J) (p : ℕ → Dome J) :
    skySemilinear F (p : Sky J) = ↑(fun i=> F i (p i)) := rfl
end actions

section gauge

variable (g g' : RSpace → SU.E)

noncomputable def onFrame (Λ : Preparation) (J : Calibration) :
    Sky J →ₗ[ℂ] Sky J := skySemilinear fun s => (pennant J (g ∘ gaugePosition Λ s)).toLinearMap

local notation "P₀" g:max s:max => pennant J (g ∘ gaugePosition Λ s)

@[simp] theorem onFrame_coe (Λ : Preparation) (J : Calibration) (f : ℕ → Dome J) :
    onFrame g Λ J (↑f) = ↑(fun i => pennant J (g ∘ gaugePosition Λ i) (f i)) := rfl

theorem onFrame_mul (Λ : Preparation) (J : Calibration) (x y : Sky J) :
    onFrame g Λ J (x*y) = onFrame g Λ J x * onFrame g Λ J y :=
  sky_change_mul (fun i => pennant J (g ∘ gaugePosition Λ i))
    (Eventually.of_forall fun _ _ _ => map_mul ..) x y

@[simp] theorem unit_onFrame (Λ : Preparation) (J : Calibration) : onFrame g Λ J 1=1 :=
  Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun i => map_one (pennant J (g ∘ gaugePosition Λ i))

@[simp] theorem onFrame_one (Λ : Preparation) (J : Calibration) (x : Sky J) : onFrame 1 Λ J x=x := by
  induction x using Filter.Germ.inductionOn with | _ x => ?_
  exact Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun i => pennantId J (x i)

@[simp] theorem onFrame_turn (Λ : Preparation) (J : Calibration) (x : Sky J) :
    onFrame g Λ J (onFrame g' Λ J x)=onFrame (g'*g) Λ J x := by
  induction x using Filter.Germ.inductionOn with | _ x => ?_
  exact Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun i =>
    pennantCompose J (g' ∘ gaugePosition Λ i) (g ∘ gaugePosition Λ i) (x i)

variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)

theorem frame_positions (Λ : Preparation) (s : ℕ) : g ∘ gaugePosition Λ s = restrictG Λ s (g ∘ toMatterUnits) :=
  funext fun i => congrArg g (location_eq Λ s i).symm

include V G Z
-- use onMove from same Exhibition and ground; do not base gauge equivalence on
-- fixing the options of a reconstruction/extraction.
theorem frame_one_step (s : ℕ) (f : Dome K) : spreadTo Y H G s (s+1) (pennant K (g ∘ gaugePosition Λ s) f) =
    pennant K (g ∘ gaugePosition Λ (s+1)) (spreadTo Y H G s (s+1) f) := by
  have h(f : Dome K) : spreadTo Y H G s (s+1) f = Exhibition.liftD Y H s Z f := by
    apply Subtype.ext; rw [PhaseChoice.lifts_here Y H V G,spreadTo_val, show s+1-s=1 by omega]; rfl
  rw [h,h,frame_positions,frame_positions,gaugeHarmony Λ s (g ∘ toMatterUnits)]
  exact pennantNatural ..

theorem frame_later {s t : ℕ} (p : s ≤ t) (f : Dome K) : spreadTo Y H G s t (pennant K (g ∘ gaugePosition Λ s) f) =
    pennant K (g ∘ gaugePosition Λ t) (spreadTo Y H G s t f) := by
  induction t,p using Nat.le_induction with
  | base => simp
  | succ t e ih =>
    rw [←spreadTo_trans Y H G e (show t ≤ t+1 by omega), ←spreadTo_trans Y H G e (show t ≤ t+1 by omega) f, ih, frame_one_step Y H V G g Z]

theorem frame_now (s : ℕ) (f : Dome K) :
    onFrame g Λ K (ticket Y H G s f) = ticket Y H G s (pennant K (g ∘ gaugePosition Λ s) f) :=
  Filter.Germ.coe_eq.mpr ((eventually_ge_atTop s).mono fun _ e => (frame_later Y H V G g Z e f).symm)

theorem onFrame_support (f : Sky K) (p : f ∈ D false U) : onFrame g Λ K f ∈ D false U := by
  obtain ⟨s,f,q,rfl⟩ := p
  obtain ⟨⟨S,h,g'⟩,-⟩ := (mem_insideAt _ _).1 q
  rw [frame_now Y H V G g Z]
  have h' : f ∈ bay K S true := h
  exact ticket_mem Y H G ((mem_insideAt _ _).2 ⟨⟨S,pennantLocal K S _ h',g'⟩,nofun⟩)

theorem physical_invariant (f : Sky K) (p : f ∈ D true U) : onFrame g Λ K f=f := by
  obtain ⟨s,f,q,rfl⟩ := p
  rw [frame_now Y H V G g Z _ _, (colorFixed K).1 ((q : _∧_).2)]

variable (j : Axis) (R : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
  (c : displayAlgebra Y H V G.history G.clipped j false (R j) →⋆ₐ[ℂ] ℂ)
local notation "ℒ" => Domain Y H G false Set.univ

omit Z in
lemma onFrame_step_value (s : ℕ) (x : Dome K) :
    oneAt Y H V G j (R j) c s (pennant K (g ∘ gaugePosition Λ s) x) = oneAt Y H V G j (R j) c s x :=
  gauge_one ..

theorem onFrame_value (x : Sky (tent Y H)) (p : x ∈ ℒ) (u : onFrame g Λ K x ∈ ℒ) :
    osValue Y H V G j (R j) c ⟨onFrame g Λ K x,u⟩ = osValue Y H V G j (R j) c ⟨x,p⟩ := by
  rcases p with ⟨s,f,h,rfl⟩
  have t := frame_now Y H V G g Z s f
  have e : (⟨onFrame g Λ K (ticket Y H G s f),u⟩ : ℒ) = ⟨_,ticket_loose Y H G s (pennant K (g ∘ gaugePosition Λ s) f)⟩ := Subtype.ext t
  rw [e,os_ticket_val,os_ticket_val,gauge_one ..]

end gauge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
