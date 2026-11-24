import YM.SU5.Same.Motion

/-!
I. Compare also **operators**. Use whenever developing the thin lab with actual CP27 estimates,
which are on these operators (Wick budgets including aperture). This buys operator, not
only ket, meaning on BOTH Euclidean presentations of any such estimate. No assertion of
operator-norm bounds portable across shrinking footprints.

II. Form a per-probe Wick scheduling certificate. We will apply at every height on the
axis 3 consultations, including for the two opposite-in-time supports of the CP18 marks.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P : Spine) (a : Axis) (x : P.Spectrum0 a) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "V" => P.law
local notation "G" => P.projection
local notation "c" => P.glassAxis a x j
local notation "ξ" => P.advocate a x j
local notation "R" => P.glassSpace a x j
local notation "S" => P.ColorHil j ξ
local notation "L" => P.toGlass a x j
local notation "K" => P.calibration
local notation "L₀" => (L).toLinearIsometry.toContinuousLinearMap
local notation "M" => timeMesh P.par

abbrev glassEntryOp (s w : ℕ) (p : 0 < w) (f : P.Card j s w) :=
  Selected.procession Y H V P.history P.projection.clipped j false (P.room j) (P.glassAxis a x j)
    (Selected.entrance Y H V s P.history P.projection.clipped j false (P.room j) f p)

set_option maxHeartbeats 1250000 in
lemma toGlass_entry_eq (s w : ℕ) (p : 0 < w) (f : P.Card j s w)
    (e : P.voxTest j s f.val ∈ enclave K) :
    (L₀).comp (P.colorSpace j ξ (P.door j s w p f e)) = (P.glassEntryOp a x j s w p f).comp L₀ := by
  have he (t u : ℕ) (p : 0 < u) (f : P.Card j t u) (e : P.voxTest j t f.val ∈ enclave K)
      (y : P.Test) (q : P.birthF j t y) :
      L ((P.colorSpace j ξ (P.door j t u p f e)) (P.viewF j ξ t q)) =
        (P.glassEntryOp a x j t u p f) (L (P.viewF j ξ t q)) := by
    obtain ⟨b,g⟩ := P.accepted_view j ξ t u p f e q
    rw [g,P.toGlass_view,P.toGlass_view]
    refine Eq.symm ((Selected.slotted Y H V t P.history P.projection.clipped j false (P.room j) c
      f p (P.bornVox j t q)).trans ?_)
    apply congrArg (Selected.bud Y H V t P.history P.projection.clipped j false (P.room j) c)
    exact Subtype.ext (slab_eq ..)
  apply ContinuousLinearMap.ext_on (P.partner_dense j ξ)
  rintro _ ⟨⟨t,g,k⟩,rfl⟩
  change L ((P.colorSpace j ξ (P.door j s w p f e)) (P.viewF j ξ t k)) = (P.glassEntryOp a x j s w p f) (L (P.viewF j ξ t k))
  let t' := max s t
  have v : s ≤ t' := le_max_left ..
  let F := furnished Y H s P.history j false w f t' v
  let w' := (P.par.R.L.val)^(t'-s)*w
  have d : P.voxTest j t' F.val ∈ enclave K := P.refine_keeps s _ e _
  have u0 : 0 < w' := Nat.mul_pos (pow_pos P.par.R.L.property _) p
  let A := P.rig j t t' k (le_max_right ..)
  rw [←P.view_rig j ξ t t' k (le_max_right ..), show P.door j s w p f e =
    P.door j t' w' u0 F d from Subtype.ext (P.upper_tab j s w p f t' v)]
  simp only [glassEntryOp]
  rw [show Selected.entrance Y H V s P.history P.projection.clipped j false (P.room j) f p =
    Selected.entrance Y H V t' P.history P.projection.clipped j false (P.room j) F u0 from
      Subtype.ext (refined_box Y H V s P.history P.projection.clipped j false (P.room j) w f p t' v)]
  exact he t' w' u0 F d _ A

lemma toGlass_entry (s w : ℕ) (p : 0 < w) (f : P.Card j s w)
    (e : P.voxTest j s f.val ∈ enclave K) (y : S) :
    L ((P.colorSpace j ξ (P.door j s w p f e)) y) =
      (P.glassEntryOp a x j s w p f) (L y) :=
  DFunLike.congr_fun (P.toGlass_entry_eq a x j s w p f e) y

open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

/-- The recovered CP27 stripOp on the same operator (with exact day/width). -/
lemma toGlass_Follows (s w : ℕ) (p : 0 < w) (f : P.Card j s w)
    (e : P.voxTest j s f.val ∈ enclave K) :
    Follows Y H V G j (P.room j) c (FirstWindows.ticket Y H G s (P.voxTest j s f.val))
      (notch (timeMesh P.par) s (w:ℤ))
      ((L).conjStarAlgEquiv (P.colorSpace j ξ (P.door j s w p f e))) := by
  have h : (L).conjStarAlgEquiv (P.colorSpace j ξ (P.door j s w p f e)) =
      P.glassEntryOp a x j s w p f := by
    ext1 u
    obtain ⟨u,rfl⟩ := (L).surjective u
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]
    exact P.toGlass_entry a x j s w p f e u
  rw [h]
  exact FirstWindows.Chambers.arrangement Y H V G j (P.room j) c s w f p

open Set OS.Semigroup Anvil

/-- Mark-level matched registration estimate, identifying the positive-time OS ket
for use in a future real-time **program** (Lens.stroke). Note `d` attaches
before any zero-scale extrapolation. -/
structure WithTicket (Q : Set RSpace) (d : marks (timeMesh P.par)) (t : ℕ)
    (f : P.Test) (v : P.ColorHil j ξ)
    (A : (P.glassSpace a x j).Op) : Prop where
  extent : f ∈ insideAt P.par P.width P.calibration true Q t
  pose : Q ⊆ Chambers.strip j 0 d
  stripOp : Follows Y H V G j (P.room j) c (FirstWindows.ticket Y H G t f) d A
  hit : L v = A (P.glassVac a x j)
  birth : ∃ b : P.birthF j t f, v = P.viewF j ξ t b

local notation "π₁" => P.wealth j ξ
local notation "π₂" => P.fortProj a x j
local notation "ι₁" => P.enter j ξ
local notation "ι₂" => P.fortIn a x j
local notation "F" => P.toFort a x j
local notation "X₂" => P.glassFort a x j
local notation "Ω₂" => P.glassHeaven a x j
local notation "Λ₀" => P.glasshouseCharacter a x
local notation "λ₁" => opCarries Y H V G j (P.room j) c
local notation "Hc" => Crease.Charter Y H V G P.room a Λ₀ j
local notation "Wc" => Crease.floor Y H V G P.room a Λ₀ j

section
variable {P a x j} {Q : Set RSpace} {d : marks (timeMesh P.par)} {t : ℕ} {f : P.Test} {v : P.ColorHil j (P.advocate a x j)}
    {A : (P.glassSpace a x j).Op}

theorem WithTicket.compressed_hit (e : P.WithTicket a x j Q d t f v A) :
    (F (π₁ v)) = λ₁ A Ω₂ := by
  rw [P.toFort_wealth,e.hit,← P.fortHeaven_in a x j]; rfl

/-- At any *one actual stencil* its budget converts to a booking required by
Enclosure. No uniformity in the stencil parameters from this. -/
theorem WithTicket.from_glass (e : P.WithTicket a x j Q d t f v A) (v0 : 0 < (d : ℝ))
    (h : IsCompact Q) (g : Crease.Enclosure Y H V G P.room a Λ₀ j) :
    (∃ M', Hc (Crease.panelFace j Q) d (λ₁ A) M') ∧
    (∀ M' : ℕ → ℂ → (X₂).Op, Hc (Crease.panelFace j Q) d (λ₁ A) M' → Anvil.Limited atTop (fun i => M' i 1) (λ₁ A)) := by
  let p := ticket_mem Y H G e.extent
  exact g.stamp (FirstWindows.ticket Y H G t f) Q d v0 h e.pose (domain_loose Y H G _ p) A e.stripOp

/-- Precisely what CP27's prescription does to an actual budgeted mark when its hypotheses
hold. This doesn't assert real Mink properties of the transported/padded operator itself. -/
theorem WithTicket.program (e : P.WithTicket a x j Q d t f v A) (v0 : 0 < (d : ℝ))
    (h : IsCompact Q) (w : BoostBacking Y H V G P.room a Λ₀) (g : Crease.Enclosure Y H V G P.room a Λ₀ j) :
    ∃ M' : ℕ → ℂ → (X₂).Op, Hc (Crease.panelFace j Q) d (λ₁ A) M' ∧
      Anvil.Limited atTop (fun i => M' i 1) (λ₁ A) ∧
      (∀ p : P.glassSpace a x j, Tendsto (fun i => inner ℂ p (ι₂ ((M' i 1) Ω₂))) atTop
        (𝓝 (inner ℂ p (L v)))) ∧
      ∀ (i : ℕ) (η : ℝ), Lens.stroke (P.glassSeason a x j) (M' i) η 0 (Real.toNNReal (d:ℝ)) ∈
        Wc (Lens.period j (Crease.panelFace j Q) η 0 (Real.toNNReal (d:ℝ))) := by
  obtain ⟨⟨N,hN⟩,q⟩ := e.from_glass v0 h g
  refine ⟨N,hN,q N hN,?_,fun n η => Crease.from_price Y H V G P.room a Λ₀ w j Q a d _ N hN η (0:marks (timeMesh P.par)) n ⟩
  intro p
  have he : L v = ι₂ (λ₁ A Ω₂) := by
    rw [← e.compressed_hit,P.toFort_wealth]; exact Eq.symm (complete_p Y H V G j (P.room j) c (w.present j) (L v))
  have eq (q:X₂) : inner ℂ p (ι₂ q) = inner ℂ (π₂ p) q :=
    Eq.symm (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right («K»:= P.glassWalkers a x j) q p)
  rw [he]; simp_rw [eq]; exact hN.scout _

end

theorem can_ticket (Q : Set RSpace) (d : marks (timeMesh P.par)) (t : ℕ) (f : P.Test)
    (p : f ∈ insideAt P.par P.width P.calibration true Q t) (q : Q ⊆ Chambers.strip j 0 d) (v0 : 0 < (d:ℝ)) (b : P.birthF j t f) :
    ∃ A, P.WithTicket a x j Q d t f (P.viewF j ξ t b) A := by
  let T := FirstWindows.ticket Y H G t f
  have v := insideAt_mono q (insideAt_loose t p)
  obtain ⟨A,h⟩ := Chambers.fits Y H V G j (P.room j) c d v0 T (ticket_mem Y H G v)
  refine ⟨A,p,q,h,?_,b,rfl⟩
  rw [P.toGlass_view,P.glassBud_physicalKet, Reflector.emp Y H V G P.room a Λ₀ j _ d h]
  rfl

#print axioms toGlass_Follows
#print axioms WithTicket.program
#print axioms can_ticket
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
