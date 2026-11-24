import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.TestField
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H

open _root_.YM.CF.Pannier.Chancel

section formula
variable {J : Calibration} {S : Finset Cover}

lemma chart_narrow (t : List Axis) (r : Cover) {F : Family J} (h : InTest J false S false F) :
    InTest J false (Selected.drivePlot r J t S) false (cad J t r F) := by
  induction t with
  | nil => exact h
  | cons a l ih => exact flow_port _ _ _ ih

-- formula for remote copies also for non-singlet inputs
noncomputable abbrev leftCell (j : Axis) (K' : Calibration) (p : Cover) (S : Finset Cover) := reflectedBox j 0 (Selected.streetBox K' p S)
noncomputable abbrev rightCell (K' : Calibration) := Selected.streetBox K'
lemma tested_narrow (j : Axis) (p q : Cover) {f g : Family J}
    (t : InTest J false S false f) (h : InTest J false S false g) :
    InTest J false (leftCell j J p S ∪ rightCell J q S) false (Selected.remotePair j J p q f g) :=
  ((axial J j 0 (chart_narrow ordinate p t)).mono Finset.subset_union_left).mul ((chart_narrow ordinate q h).mono Finset.subset_union_right)

lemma lode_anchors {q t : ℕ} {o : Cover} {z : SU.Slot} (X : Family J) (h : X ∈ Lode J (Window.family z) (booty o t q) S) (p : X ≠ 0) : 0<q := by
  by_contra! g
  have hx : Lode J (Window.family z) (booty o t q) S ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro i ⟨i,e,k,f⟩
    cases i with
    | nil => contradiction
    | cons i t => have hi := i.isLt; have : q^4=0 := by rw [Nat.eq_zero_of_le_zero g]; norm_num
                  omega
  exact p (hx h)

/-- 'as is' transfer of the given physical mark into the local algebra. -/
noncomputable def insertAt (s : ℕ) : Selected.Marks (tent Y H) true →ₐ[ℂ] Tapestry.Altitude.Cloud (Tapestry.Dome (tent Y H)) := by
  let i₀ : Selected.Marks (tent Y H) true →ₐ[ℂ] Dome (tent Y H) := {
    toFun := fun x => resolutionProbe Y H x
    map_add' _ _:= rfl
    map_zero':= rfl
    map_one':= rfl
    map_mul' _ _:= rfl
    commutes' _:= rfl }
  exact (pinhole _ s).comp i₀
lemma inserts_at (s : ℕ) (f : Selected.Marks (tent Y H) true) :
    insertAt Y H s f = pinhole (Dome (tent Y H)) s (resolutionProbe Y H f) := rfl
-- eventually narrower Q support preserved.
lemma insert_visible {s : ℕ} {wide : Bool} (f : Selected.Marks (tent Y H) true)
    (p : InTest (tent Y H) wide S false f.val) :
    insertAt Y H s f∈ circum Λ l K wide (silhouette Λ l s S) (Set.Iic s) :=
  one_rung_licensed Y H (f:=resolutionProbe Y H f) p ((marksSpec true f).2 rfl) Set.Subset.rfl

lemma insert_visible_all {s : ℕ} {wide : Bool} (f : Selected.Marks (tent Y H) true)
    (p : InTest (tent Y H) wide S false f.val) : insertAt Y H s f ∈ localEuclidean Λ l (tent Y H) wide (silhouette Λ l s S) :=
  local_at (silhouette_compact ..) (insert_visible Y H f p)
end formula
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  (D : Exhibition Y H i k I E L B)
variable (j d : Axis) (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
local notation "χ₀" => Dome (tent Y H)
local notation "Ĉ" => euclideanHalf Λ l (tent Y H) j
variable (c : (displayAlgebra Y H V G.history G.clipped d false (T d)) →⋆ₐ[ℂ] ℂ)
local notation "χ" => Selected.displacement Y H V G.history G.clipped d false (T d) c j (T j)
local notation "rχ" => resident Y H V G d false (T d) c
local notation "ρ" => indoor Y H V G.history G.clipped j false (T j) χ
local notation "P" => procession Y H V G.history G.clipped j false (T j) χ
local notation "Ω" => doorstep Y H V G.history G.clipped j false (T j) χ
local notation "Ψ" => matchGNS Y H V G j false (T j) d (T d) c
local notation "𝒱" s:max x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x
local notation "Θ" => onDrawing Y H V G D d T rχ
local notation "Mx" => evaluate Y H V G d T rχ
local notation "Ex" s:max => Selected.response Y H V s G.history G.clipped j false (T j) χ

lemma response_matches (s : ℕ) (f : Selected.Marks (tent Y H) false) :
    Mx s f.val=(Ex s) f := (evaluates Y H V G d T rχ s f).trans
      ((sameReading Y H V G d false (T d) c s f).trans (across_response Y H V s G.history G.clipped d false (T d) c f j (T j)).symm)

lemma total_extension (s : ℕ) : Mx s = pigmentReading Y H V s G.history G.clipped j (T j) χ := by
  funext f
  by_cases h : TestFamily (tent Y H) true f
  · let m : Selected.Marks K false := PhaseChoice.observe h
    exact (response_matches Y H V G j d T c s m).trans (reads_color Y H V s G.history G.clipped j (T j) χ m).symm
  unfold evaluate pigmentReading; rw [dif_neg h,dif_neg]
  intro v; exact h v.1

lemma draw_read (s : ℕ) (f : Selected.Marks (tent Y H) true) :
    Θ (insertAt Y H s f)=(Ex s) (bosonLabel (tent Y H) f) := (plugged Y H V G D d T rχ s (resolutionProbe Y H f)).trans (response_matches Y H V G j d T c s (bosonLabel (tent Y H) f))
include V in
lemma further_finish (s n : ℕ) (f : Selected.Marks (tent Y H) true) :
    ((vistaFinish Y H (s+n) D) (insertAt Y H s f)).val=stream Y H G.refine s n f.val := by
  rw [inserts_at]; induction n with
  | zero=> exact congrArg (fun x : Dome K => x.val) ((vistaDressing Y H D).outcrop (auxiliaryPad K) s _)
  | succ n h=>
    rw [show s+(n+1)=s+n+1 by omega,vistaFinish, Decking.joins (p:=Tapestry.Altitude.climbs (Dome K) (Nat.le_add_right s n) (short_pinhole s _))]
    exact (lifts_here Y H V G D _ _).trans (by rw [stream_step]; exact congrArg _ h)

section readings
variable (S : Finset Cover)
variable (s q t : ℕ) (o : Cover) (z : SU.Slot) (f : Selected.Marks (tent Y H) true)
variable (h : ThresholdInteraction Y H V s G.history G.clipped j (T j) S (Selected.displacement Y H V G.history G.clipped d false (T d) c j (T j)) f z o q t)
local notation "C₀" s:max => insertAt Y H s
local notation "σ" n:max => silhouette Λ l n
local notation "h₀" => h.witness.link

include h
lemma one_probe :
    (C₀ s) f ∈ circum Λ l K false ((σ s) S) (Set.Iic s) ∧
    1/4≤ ‖Θ ((C₀ s) f)‖ ∧ ¬ _root_.YM.CF.Pannier.Chancel.Parcel K (Window.family z) (booty o t q) S (Mx s) ∧
    (∀ n : ℕ, let F : Selected.Marks (tent Y H) true := upward Y H G.history true f s n; 
      (C₀ (s+n)) F ∈ circum Λ l K true (silhouette Λ l s S) (Set.Iic (s+n)) ∧
      Θ ((C₀ (s+n)) F)=Θ ((C₀ s) f)) := by
  rw [total_extension Y H V G j d T c s]
  refine ⟨insert_visible Y H f (FilTest (h₀).mark_mem), (draw_read Y H V G D j d T c s f).symm ▸ h.witness.responds,h.witness.factor_failure,?_⟩
  intro n F; have hp : F.val∈ observ (tent Y H) (volumeAround Λ l n S) true := ((h₀).further n).2.1
  refine ⟨circum_widens Y H (sheltered_still n) Set.Subset.rfl (insert_visible Y H F ((obs_in ..).1 hp).1),?_⟩
  rw [draw_read Y H V G D j, draw_read Y H V G D j]
  exact moves_up Y H V s G.history G.clipped j false (T j) χ (bosonLabel K f) n

/-- Strengthen the transfer of resources with the PhaseChoice assay / native nonzero
product qualification. -/
lemma anchored : 0<q ∧ ∃ (a : Family (tent Y H)) (F : PairsC → ℂ),
    a∈ Lode K (Window.family z) (booty o t q) S ∧ Coeff false S F ∧ Mx s a=0 ∧ Mx s (scalar K F*a)≠0 := by
  -- not using suite.
  have hx:= h.witness.factor_failure
  rw [← total_extension Y H V G j d T c s] at hx
  unfold _root_.YM.CF.Pannier.Chancel.Parcel at hx; push Not at hx
  obtain ⟨a,u,p,w,r⟩:= hx
  have k:= (consistency Y H V G d T rχ S s).footprint (h₀).anchor_inj u
  rw [k,mul_zero] at r
  refine ⟨lode_anchors (z:=z) a u ?_, a,p,u,w,k,r⟩
  intro l; exact r (by rw [l,mul_zero]; exact (consistency Y H V G d T rχ S s).nil_v)

end readings
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.one_probe
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.anchored
