import YM.SU5.Reconstruction.FirstWindows.Grid
/-!
# Coordinate reflective part of the Euclidean geometry

On exactly the same functional and test spaces. Composition also gives a DISCRETE
set of proper rotations (coordinate half-turns), not asserting connected joint covariance.
Combines with dense translations defined on these same regions. -/
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
open SlabMark
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G

variable (j : Axis)
noncomputable def flipMark (J : Calibration) : Sky J →ₗ⋆[ℂ] Sky J := skySemilinear fun _ => aureole J j 0

@[simp] theorem flipMark_coe (f : ℕ → Dome J) : flipMark j J (↑f) = ↑(fun i=> aureole J j 0 (f i)) := rfl

lemma flipMark_unit : flipMark j J 1=1 := Filter.Germ.coe_eq.mpr (Eventually.of_forall fun _ => aureoleUnit J j 0)

lemma flipMark_mul (f g : Sky J) : flipMark j J (f*g)=flipMark j J f * flipMark j J g :=
  sky_change_mul (fun _ => aureole J j 0) (Eventually.of_forall fun _ _ _=>aureoleProduct ..) f g

lemma flipMark_ticket (s : ℕ) (x : Dome (tent Y H)) :
    flipMark j K (ticket Y H G s x)=ticket Y H G s (aureole K j 0 x) := by
  refine Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun t => ?_
  apply Subtype.ext
  change mirror K j 0 _= stream Y H G.refine s (t-s) (mirror K j 0 x.val)
  rw [stream_flipped Y H G.history.circuit s (t-s) j 0 ((marque ..).1 x.property), mul_zero]; rfl

lemma flipMark_marks (f : Dome K) (z : ℤ) : (aureole (tent Y H) j z f).val=mirror (tent Y H) j z f.val := rfl

@[simp] lemma mirror_units (x : RSpace) : toMatterUnits (mirrorE j 0 x)=mirrorE j 0 (toMatterUnits x) := by
  funext i; by_cases h:i=j <;> simp [toMatterUnits, mirrorE,h]; ring


lemma mirror_inside (f : Dome K) (s : ℕ) (h : f ∈ insideAt Λ l K q U s) :
    aureole K j 0 f ∈ insideAt Λ l K q (mirrorE j 0 '' U) s := by
  obtain ⟨⟨S,t,p⟩,h⟩ := (mem_insideAt _ _).1 h
  refine (mem_insideAt _ _).2 ⟨⟨_, axial K j 0 t, ?_⟩, fun t' => (enclave_spec K).1
    (aureoleEnclave K j 0 ((enclave_spec K).2 (h t')))⟩
  have hp := reversed Λ l (s:=s) (α:=j) (z:=0) (V:=PhaseChoice.handstamp U) p
  rw [show markZ Λ s (0:ℤ)=0 by simp [markZ]] at hp
  intro x hx a v; change toMatterUnits a ∈ (mirrorE j 0 '' U)
  obtain ⟨b,h,rfl⟩ := hp x hx v
  exact ⟨toMatterUnits b,h,(mirror_units j b).symm⟩

lemma mirror_support (f : Sky K) (h : f ∈ D q U) :
    flipMark j K f ∈ D q (mirrorE j 0 '' U) := by
  obtain ⟨s,z,hz,rfl⟩ := h
  rw [flipMark_ticket]
  exact ticket_mem Y H G (mirror_inside Y H j z s hz)

@[simp] theorem mirror_twice (f : Sky J) : flipMark j J (flipMark j J f)=f := by
  induction f using Filter.Germ.inductionOn with | _ f=> ?_
  exact Filter.Germ.coe_eq.mpr (Eventually.of_forall fun i=> aureoleTwice J j 0 (f i))

lemma mirror_commuting (i : Axis) (x : Sky (tent Y H)) :
    flipMark j K (flipMark i K x)=flipMark i K (flipMark j K x) := by
  induction x using Filter.Germ.inductionOn with | _ x=> ?_
  refine Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun k : ℕ=> ?_
  exact Subtype.ext <| PhaseChoice.mirror_switch j i K ((marque ..).mp (x k).property)

-- Semidirect part.
def reverseOne {A : Type*} [Neg A] (j : Axis) (p : Axis → A) : Axis → A :=
  fun i=> if i=j then -p i else p i

lemma reverse_stamp (z : Cover) (s : ℕ) :
    stamps Λ s (reverseOne j z) = reverseOne j (stamps Λ s z) := by
  ext1 i
  by_cases h : i=j
  · rw [stamps_at, reverseOne,reverseOne, if_pos h, if_pos h, stamps_at]
    apply Subtype.ext
    change MeshClock.bell (timeMesh Λ) s (-z i)= -(MeshClock.bell (timeMesh Λ) s (z i))
    simp [MeshClock.bell]
  simp only [stamps_at,reverseOne, if_neg h]

lemma reverse_at (p : placement Λ) : mirrorE j 0 (coordinates Λ p) = coordinates Λ (reverseOne j p) := by
  funext i; by_cases h:i=j <;> simp [mirrorE, h, reverseOne]

lemma flipped_positions (v : Cover) (f : Dome J) :
    reposition J (reverseOne j v) (aureole J j 0 f)=aureole J j 0 (reposition J v f) := by
  have h := ((marque ..).mp f.property)
  apply Subtype.ext
  change cad J ordinate (reverseOne j v) (mirror J j 0 f.val)= mirror J j 0 (cad J ordinate v f.val)
  generalize Vacancy.ordinate = a
  induction a with
  | nil => rfl
  | cons i t ih =>
    simp only [cad_step, ih, reverseOne]
    by_cases k:i=j
    · subst i; rw [if_pos rfl]; exact (mirror_relocate J j _ _ (cad_paid J t h v)).symm
    rw [if_neg k]; exact Tower.straddle i j k _ _ ((cad_paid J t h v).paid.choose_spec)

lemma flipped_moves (p : placement Λ) (x : Sky (tent Y H)) :
    flipMark j K (move K p x) = move K (reverseOne j p) (flipMark j K x) := by
  induction x using Filter.Germ.inductionOn with | _ x=> ?_
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [stamps_eventually p] with i ⟨q,h⟩
  change aureole K j 0 (reposition K (chooseStamp p i) _)=reposition K (chooseStamp (reverseOne j p) i) (aureole K j 0 _)
  rw [chooseStamp_eq h,chooseStamp_eq ((reverse_stamp j q i).trans (congrArg (reverseOne j) h)),flipped_positions]

variable (iA : Axis) (C : Arena Y H G.history.circuit iA 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped iA false C →⋆ₐ[ℂ] ℂ)

lemma reflected_read {f : Sky (tent Y H)} (h : f ∈ D false Set.univ)
    (g : flipMark j K f ∈ D false Set.univ) :
    osValue Y H V G iA C χ ⟨flipMark j K f,g⟩ = star (osValue Y H V G iA C χ ⟨f,h⟩) := by
  rcases h with ⟨s,f,h,rfl⟩ -- shadow
  rw [show (⟨flipMark j K _,g⟩ : D false Set.univ) = ⟨ticket Y H G s (aureole K j 0 f), ticket_loose ..⟩ from Subtype.ext (flipMark_ticket Y H G j s f),os_ticket_val,os_ticket_val]
  exact all_mirror Y H V s G.history G.clipped iA false C χ (asLoose K f) j

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
