import YM.SU5.Selected.BridgedAxes
/-!
# Close the odd-step loophole for the cap history at fixed marks

Indeed we can even extend to every single-step here. Each time ripple at z=0 positive; a
single gaugeShift-displacement's positive bill uses the RP form halfway between! The Euclidean
duration now includes these values; before using on genuine spacetime need also space and
Lorentz information. Use even applications for support separation when required.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "Ε" => advance Y H V Q.circuit j 0 r C
local notation "℘" => gaugeShift Λ.block
local notation "τ" s:max => tick Y H s j 0 r
variable (s : ℕ)
lemma translate_region (z : ℤ) (t : ℕ) {S : Finset Cover} (h : Tower.region j z (K).ℓ S) :
    Tower.region j (z + ℘ (t:ℤ)) (K).ℓ (Tower.address j (℘ (t:ℤ)) S) := by
  intro i b; obtain ⟨x,p,rfl⟩ := mem_image.mp b; rw [moves,if_pos rfl]
  have h0 : 0 ≤ ℘ (t:ℤ) := by unfold gaugeShift; positivity
  linarith only [h x p,h0]
include V Q C
lemma seed_odd (x : F₊ s) (t : ℕ) :
    0 ≤ inner ℂ ((φ s) x) ((φ s) ((τ s) t x)) := by
  obtain ⟨S,h,e⟩ := ((purpose_ok ..).1 x.property).1
  rw [stems Y H V,area0]; rw [area0] at e
  let f := x.val
  let g := chime K j (℘ (t:ℤ)) f
  have hx : 0 ≤ E s (mirror K j (℘ (t:ℤ)) g * g) :=
    boson_axial Y H V s (a:=j) (z:=t) (flow_port K j _ h) (by simpa only [zero_add] using translate_region Y H j 0 t e)
  change 0 ≤ E s (mirror K j 0 f * g)
  have hu : mirror K j (℘ (t:ℤ)) g = mirror K j 0 f :=
    reversal _ _ _ (axial K j 0 h)
  rwa [hu] at hx

lemma ripple_pos (t : ℕ) : 0 ≤ (ρ s) t := by
  let u := (ρ s) t; have p : u.adjoint=u:=current_adjoint ..
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).2
  refine ContinuousLinearMap.isPositive_def'.2 ⟨p,?_⟩; intro x
  let S : Set (A) := { x | 0 ≤ (inner ℂ (u x) x).re }
  have hu : itinerary Y H V Q.circuit j 0 r C ⊆ S := by
    intro y hy; obtain ⟨m,v,rfl⟩ := Set.mem_iUnion.mp hy
    let k := max s m; let ht : m ≤ k := le_max_right ..; let hk : s ≤ k := le_max_left ..
    let h := Raise Y H Q.circuit j 0 r m k ht v
    change 0 ≤ (inner ℂ ((ρ s) t ((φ m) v)) ((φ m) v)).re
    unfold u at p
    rw [←p,ContinuousLinearMap.adjoint_inner_left, ←join_actor Y H V Q.circuit j 0 r C m k ht]
    rw [limited_time Y H V s Q.circuit j 0 r C t hk]; exact (Complex.le_def.mp (seed_odd Y H V Q j r C k h (amount Λ s k t))).1
  refine closure_minimal hu (show IsClosed S from isClosed_le continuous_const (by fun_prop)) (sounds Y H V Q.circuit j 0 r C x)
-- tune exact placeholder

omit V Q C
private theorem many_positive {L : Mesh} {X : Hilbert} (F : Many L X) (x : ℝ≥0) :
    0 ≤ F.track x := by
  have h := F.track_times (x/2) (x/2)
  have hv : F.track x = (F.track (x/2)).adjoint.comp (F.track (x/2)) := by
    rw [F.track_adjoint,h,add_halves]
  rw [hv]; exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 (ContinuousLinearMap.isPositive_adjoint_comp_self _)
lemma many_half_time {L : Mesh} {X : Hilbert} (F : Many L X) (t i : ℕ) (h : 0 ≤ F.move t i) :
    F.track (whenly L t i/2) = F.move t i := by
  have ht : F.track (whenly L t i/2)^2=(F.move t i)^2 := by
    simp only [sq]; change _ = (F.move t i).comp (F.move t i)
    rw [F.add]; change (F.track _).comp (F.track _)=_
    rw [F.track_times,add_halves,F.track_even, ← two_mul i]; rfl --]
  exact (CFC.sqrt_sq _ (many_positive F _)).symm.trans ((congrArg CFC.sqrt ht).trans (CFC.sqrt_sq _ h))

include V Q C
lemma at_every (t : ℕ) : (ρ s) t = Ε (whenly (timeMesh Λ) s t/2) :=
  (many_half_time (clockdrive Y H V Q.circuit j 0 r C) s t (ripple_pos Y H V Q j r C s t)).symm

def stepTest (z : ℤ) (x : Test) : Test :=
  ⟨chime K j (℘ z) x.val,
   aux_test (flow_port K j _ x.property.1.paid.choose_spec),
   fun b => chime_cov K j _ x.property.1.paid.choose_spec (x.property.2 b)⟩

include Qc
lemma natural_shift (k : ℕ) (x : Test) : (M s) (stepTest Y H j r k x)=(M s) x := by
  let z := Classical.choice (anyporch Y H s j r x)
  let y : F₊ s := z.fwd.val
  let F := stepTest Y H j r k x
  have hv : ((τ s) k y).val = relocate K j z.rise F.val := by
    change chime K j _ z.fwd.val.val = _
    rw [z.yes]; unfold relocate; change chime K j _ (chime K j _ _)= chime K j _ (chime K j _ _)
    exact twin_slide j j _ _ x.property.1.paid.choose_spec -- args order?
  apply distinguish Y H V Q Qc j r C
  change (N s) F Ω = (N s) x Ω
  rw [cap_via_actor Y H V Q Qc j r C s F _ ((τ s) k y) hv,
    cap_via_actor Y H V Q Qc j r C s x _ y z.yes]
  have he : (ρ s) k ((φ s) y) = (φ s) ((τ s) k y) := by rw [limited_time Y H V s Q.circuit j 0 r C k le_rfl,amount_reset]
  rw [←he, at_every Y H V Q]; exact congr_fun (congrArg DFunLike.coe (behind Y H V Q j r C _)) _

lemma whole_shift (z : ℤ) (x : Test) : (M s) (stepTest Y H j r z x)=(M s) x := by
  rcases le_total 0 z with p | p
  · exact ((Int.toNat_of_nonneg p) ▸ natural_shift Y H V Q Qc j r C s z.toNat x)
  let w := (-z).toNat
  have h : (w:ℤ)= -z:=Int.toNat_of_nonneg (neg_nonneg.mpr p)
  have he : stepTest Y H j r w (stepTest Y H j r z x)=x := by
    apply Subtype.ext
    change chime K j _ (chime K j _ x.val) = _
    rw [Tower.bumps K j (℘ (w:ℤ)) (℘ z) x.property.1.paid.choose_spec,h,
      show (℘ (-z))+(℘ z)=0 from by unfold Heat.gaugeShift; ring]
    exact Tower.wake K j x.property.1.paid.choose_spec
  rw [←natural_shift Y H V Q Qc j r C s w _,he]

lemma stationarity (z : ℤ) (x : Test) (v : Axis) : (M s) (stepTest Y H v r z x)=(M s) x := by
  obtain ⟨P⟩ := voyage_H Y H V Q.circuit v 0 r
  apply (coincide Y H V Q Qc j r C v P).injective; exact (phase_hit Y H V Q Qc j r C v P _ _).trans ((whole_shift Y H V Q Qc v r P s z x).trans (phase_hit Y H V Q Qc j r C v P s x).symm)
end YM.CF.Buffered.Afterglow.Tower.Selection
