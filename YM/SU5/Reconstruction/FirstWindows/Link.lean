import YM.SU5.Reconstruction.FirstWindows.MovingKets
import YM.SU5.Reconstruction.FirstWindows.Sharp
/-!
# First reconstruction bridge for the interaction

Checks of interpretation for selected probes: the actual mixed test with that budget
in the determining spacetime algebra and prefactorization domain. Nonfactorization in the
exact sense of Clinic, realized here on that domain (comparison necessarily involves some
loose, nongauge-invariant *parts* of the terms). The observable whose lower bound we
transmit is itself gauge invariant. And narrow: all Links accesses in the test on the
first field and transported/reflected according to the very same frame moves. Even the
prescribed curvature-requiring choice, paid at THIS character in all its Hilbert spaces,
using the same test support at all resolutions on the sharp path. This does not refine
an individual-letter support and assert their disjointness inside either source cell.
Not claiming a truncated nonzero between the cells. See AllGap.
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
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
  Fock Lat Lifted Peaks Spire Tenant Vale
  SlabMark MeshClock Tapestry.Exhibition Tapestry.Altitude
attribute [local instance] opCStarAlgebra
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
set_option quotPrecheck false

section legs
variable (j : Axis) {J : Calibration}
variable (p w : Cover)
noncomputable def fromStrict (f : Marks J true) : Dome J := ⟨f.val, f.property.1⟩
noncomputable def leg (j : Axis) (p : Cover) : Dome J →ₗ⋆[ℂ] Dome J :=
  (aureole J j 0).comp (reposition J p)
noncomputable def twin (x y : Dome J) : Dome J := leg j p x * reposition J w y
local notation "x₀" => leg j p
local notation "y₀" => reposition J w
variable (x y : Dome J)

@[simp] theorem twin_val : (twin j p w x y).val=remotePair j J p w x.val y.val := rfl

local notation "rBox" s:max => streetBox J p s
local notation "pBox" s:max => reflectedBox j 0 (streetBox J p s)
local notation "qBox" s:max => streetBox J w s

lemma street_narrow {J : Calibration} (A : List Axis) {S} {f : Family J} (h : InTest J false S false f) :
    InTest J false (drivePlot w J A S) false (cad J A w f) := by
  induction A with
  | nil => exact h
  | cons i t ih=> exact flow_port _ _ _ ih
variable {x y}

lemma leg_narrow {S : Finset Cover} (h : InTest J false S false x.val) :
    InTest J false (pBox S) false (x₀ x).val := axial J j 0 (street_narrow p ordinate h)

lemma other_narrow {S : Finset Cover} (h : InTest J false S false y.val) :
    InTest J false (qBox S) false (y₀ y).val := street_narrow w ordinate h

lemma twin_product {a b c d : Dome J} : twin j p w (a*b) (c*d) = twin j p w a c * twin j p w b d :=
  Subtype.ext (remotePair_factors j J p w b.property c.property)

-- `silence`: no reading on the first field entirely trivial. This property's obligations on
-- translated or reflected probes do not include restoration on unrelated rotated or Curved axes.
def Silence (f : Family J) := ∀ (m : Side) (v : Fields (J.c m)), v.1=1 → f m v=0

lemma mirror_silence {x : Family J} (h : Silence x) (s : ℤ) : Silence (mirror J j s x) := by
  intro m v e; unfold mirror reflMark; rw [h,_root_.YM.CF.Fock.theta_zero]
  change fling j s (J.c m) v.1 = _
  rw [e,fling_eq]; funext i; simp [Lattice.pull,Lattice.Step.read]

lemma street_silence {x : Family J} (h : Silence x) (A : List Axis) : Silence (cad J A p x) := by
  induction A with
  | nil => exact h
  | cons i a ih => exact mirror_silence _ (mirror_silence _ ih _) _

lemma silence_at_link {u d} {f : observable (tent Y H) true} {ζ : ℝ} {o : Cover} (e : 0<u) (hz : 0≤ζ)
    (t : ∀ (m : Side) (v : Fields ((tent Y H).c m)) (r : Fin (u^4)), SU.group.chord (faceValue (onC _ v.1) (facet ((booty o d u) r))) ≤ ζ→ f.val m v=0) : Silence f.val := by
  intro m v h; apply t m v ⟨0,by positivity⟩
  rw [h,show onC _ (1: Pane ((tent Y H).c m))=1 from funext (fun i=> onC_spec _ 1 i), show faceValue (1 : LinksC) (facet _) = 1 from ?_, Gauge.chord_one]; exact hz
  simp [faceValue,square,Lattice.travel,Lattice.Step.read]

lemma twin_silent (h : Silence x.val) : Silence (leg j p x).val ∧ Silence (reposition J w x).val ∧ Silence (twin j p w x x).val := by
  have ht : Silence (leg j p x).val := mirror_silence j (street_silence p h ordinate) 0
  refine ⟨ht,street_silence w h _,fun m v g=>?_⟩
  change (leg j p x).val m v * _ = _; rw [ht m v g,zero_mul]
end legs

section charges
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
variable (s : ℕ) (p w : Cover)
local notation "F" => osValue Y H V G j C χ
local notation "Tt" => twin j p w
local notation "ℒ" => Domain Y H G false Set.univ
-- any ticket. no proof obligations off the test domain.
noncomputable def sameRead : Dome (tent Y H) → ℂ := fun x =>
  F ⟨ticket Y H G s x,ticket_loose ..⟩

lemma pigment_here (f : Dome (tent Y H)) : sameRead Y H V G j C χ s f = pigmentReading Y H V s G.history G.clipped j C χ f.val := by
  unfold sameRead
  rw [os_ticket_val,oneAt_reads]; exact (reads_color Y H V s G.history G.clipped j C χ (asLoose K f)).symm

-- This test class: products formed in questions algebra (first pair factors
-- supported, second in a separate region, generation/chiral pair input and
-- separately translated pure-gauge coefficients; see `WitnessCharge` below).
-- Links with the fixed generation label system and OFF-anchors matter at this
-- observing scale. The test is meaningful even when the *parts* of an investigated
-- singlet would have to be evaluated outside the singlet space (and gauge invariant
-- under exactly the same pennant test, in the sense of VALUE invariance).
local notation "Psi" => sameRead Y H V G j C χ s
structure NoDecompose (z : SU.Slot) (u d : ℕ) (S : Finset Cover) (o : Cover)
    (a b g g' : Dome (tent Y H)) : Prop where
  charge₁ : a.val ∈ Lode K (Window.family z) (booty o d u) S
  charge₂ : b.val ∈ Lode K (Window.family z) (booty o d u) S
  bareGauge₁ : ∃ Fo, Coeff false S Fo ∧ g.val=scalar K Fo
  bareGauge₂ : ∃ Fo, Coeff false S Fo ∧ g'.val=scalar K Fo
  matterKernels : Psi (twin j p w a b)=0
  operational : 0<‖Psi (twin j p w (g*a) (g'*b)) - Psi (twin j p w a b) * Psi (twin j p w g g')‖

lemma decomposition_fails {z : SU.Slot} {u d : ℕ} {o : Cover} {S : Finset Cover}
    (h : ¬RemoteSplit j K p w S (booty o d u) (Window.family z) (pigmentReading Y H V s G.history G.clipped j C χ))
    (b : Disjoint (reflectedBox j 0 (streetBox (tent Y H) p S)) (streetBox (tent Y H) w S))
    (t : Injective (booty o d u)) :
    ∃ a b g g' : Dome (tent Y H), NoDecompose Y H V G j C χ s p w z u d S o a b g g' := by
  unfold RemoteSplit at h; push Not at h
  obtain ⟨x,hx,y,hy,f,v,hf,hv,k'⟩ := h -- possible order
  let a':= (⟨x,aux_test (Lode_test (W:=Window.family z) (b:=booty o d u) hx|>.widen)⟩ : Dome (tent Y H))
  let b':= (⟨y,aux_test (Lode_test (W:=Window.family z) (b:=booty o d u) hy|>.widen)⟩ : Dome (tent Y H))
  let f':= (⟨scalar K f,aux_test ((InTest.seed hf).widen)⟩ : Dome (tent Y H))
  let g':= (⟨scalar K v,aux_test ((InTest.seed hv).widen)⟩ : Dome (tent Y H))
  refine ⟨a',b',f',g',hx,hy,⟨f,hf,rfl⟩,⟨v,hv,rfl⟩,?_,?_⟩
  · rw [pigment_here]
    exact Selected.remote_cold Y H V s G.history G.clipped j C χ w _ b (mirror K j 0 (cad K ordinate p x)) (axial K j 0 (street_narrow p ordinate (Lode_test (W:=Window.family z) (b:=booty o d u) hx)).widen) (booty o d u) t (Window.family z) y hy
  rw [pigment_here, pigment_here,pigment_here,mul_comm _ (pigmentReading ..)]; exact norm_pos_iff.mpr (sub_ne_zero.mpr k')

local notation "Mh" => bufferedHull Λ l s
local notation "g'₀" A:max => bufferedHull Λ l s (reflectedBox j 0 (streetBox (tent Y H) p A))
local notation "g'₁" A:max => bufferedHull Λ l s (streetBox (tent Y H) w A)

-- Show these leg readings are interpreted EXACTLY as separated operations on our domain.
structure OnCharge (S : Finset Cover) (x y : Dome (tent Y H)) : Prop where
  left : leg j p x ∈ insideAt Λ l K false (g'₀ S) s
  right : reposition K w y ∈ insideAt Λ l K false (g'₁ S) s
  pair : ticket Y H G s (twin j p w x y) = (ticket Y H G s (leg j p x)) * ticket Y H G s (reposition K w y)

lemma charge_check {S : Finset Cover} {x y : Dome (tent Y H)}
    (b : Disjoint (g'₀ S) (g'₁ S))
    (t : InTest K false S false x.val) (w' : InTest K false S false y.val) : OnCharge Y H G j s p w S x y := by
  let v : leg j p x ∈ insideAt Λ l K false (g'₀ S) s := (mem_insideAt ..).2 ⟨⟨_, (leg_narrow j p t).widen, hull_support _ _ _ _⟩, nofun⟩
  let u : reposition K w y ∈ insideAt Λ l K false (g'₁ S) s := (mem_insideAt ..).2 ⟨⟨_, (other_narrow w w').widen, hull_support _ _ _ _⟩, nofun⟩
  exact ⟨v,u,ticket_separated Y H G v u b⟩

lemma witness_charge {z : SU.Slot} {u d : ℕ} {S : Finset Cover} {o : Cover} {a b g g' : Dome (tent Y H)}
    (h : NoDecompose Y H V G j C χ s p w z u d S o a b g g')
    (t : Disjoint (g'₀ S) (g'₁ S)) :
    OnCharge Y H G j s p w S a b ∧ OnCharge Y H G j s p w S g g' ∧ OnCharge Y H G j s p w S (g*a) (g'*b) := by
  have h₁ := Lode_test h.charge₁
  have h₂ := Lode_test h.charge₂
  obtain ⟨f,q,v⟩ := h.bareGauge₁; obtain ⟨f',p',e⟩ := h.bareGauge₂
  have u : InTest K false S false g.val := v.symm ▸ .seed q
  have w : InTest K false S false g'.val := e.symm ▸ .seed p'
  exact ⟨charge_check Y H G j s _ _ t h₁ h₂,charge_check Y H G j s _ _ t u w,
    charge_check Y H G j s _ _ t (u.mul h₁) (w.mul h₂)⟩

lemma narrow_price {S} {U : Set RSpace} {f : Dome (tent Y H)} (u : InTest K false S false f.val)
    (h : PhaseChoice.SupportedPhysically Λ l s S U) (v : f∈ insideAt Λ l K true U s) :
    pinhole (Dome K) s f ∈ PhaseChoice.circum Λ l K false U ((Set.univ : Set ℕ) ∩ Set.Iic s) := by
  have he := ((mem_insideAt ..).1 v).2 rfl
  exact oneSlotWell Λ K l false (PhaseChoice.handstamp U) ((Set.univ : Set ℕ) ∩ Set.Iic s) s ⟨Set.mem_univ _, le_refl s⟩ ((Tapestry.keeps ..).2 ⟨S,(Tapestry.locates ..).2 u,h⟩) he

-- The actual compound singlet interrogation in the ordinary determining algebra AND
-- the compactly supported spacetime domain, with answer on the same character. In a
-- reconstruction the operations here should be transported, not a new later narrow source.
local notation "pin" => pinhole (Dome K) s

lemma reposition_strict (f : Marks (tent Y H) true) : reposition K p (fromStrict f) = fromStrict (relocateWorld Y H true p f) :=
  Subtype.ext (world_val Y H true p f).symm
lemma leg_strict (f : Marks (tent Y H) true) : leg j p (fromStrict f)=fromStrict (mirrorInMarks Y H j true (relocateWorld Y H true p f)) := by
  change aureole K j 0 ((reposition K p) _) = _
  rw [reposition_strict]; rfl

variable (S : Finset Cover) (z : SU.Slot) (o : Cover) (u d : ℕ) (f : Marks (tent Y H) true)
local notation "D₀" => g'₀ S -- tune
local notation "D₁" => g'₁ S
local notation "z₀" => leg j p (fromStrict f)
local notation "z₁" => reposition (tent Y H) w (fromStrict f)
-- explicitly no unfolding at application surprises, also proves polynomial through algebra eval at common level
local notation "E₀" => insideAt Λ l K true
local notation "Ω" => ((Set.univ : Set ℕ) ∩ Set.Iic s)
local notation "κ" => ticket Y H G s
open SelectionAnalysis Spectral Germ
variable (δ : ℝ)
local notation "I₀" => indoor Y H V G.history G.clipped j false C χ
local notation "I₁" => fort Y H V G.history G.clipped j false C χ

noncomputable def compassKet : Domain Y H G true (flank j 0) →ₗ[ℂ] fort Y H V G.history G.clipped j false C χ :=
  ((saunters Y H V G.history G.clipped j false C χ).orthogonalProjectionOnto).toLinearMap.comp
    (physicalKet Y H V G j C χ)

lemma compass_land (x : Tower.Field Y H s j 0 false) (y : Dome (tent Y H)) (v : y.val=x.val)
    (p : y ∈ insideAt Λ l K true (flank j 0) s) (b : ticket Y H G s y ∈ Domain Y H G true (flank j 0)) :
    compassKet Y H V G j C χ ⟨ticket Y H G s y,b⟩=land Y H V s G.history G.clipped j false C χ x := by
  let y' := (⟨y,insideAt_loose s p⟩ : insideAt Λ l K false (flank j 0) s)
  have h : asField Y H j false s y'=x := Subtype.ext v
  change (saunters Y H V G.history G.clipped j false C χ).orthogonalProjectionOnto (OSvector Y H V G j C χ ⟨ticket Y H G s y,_⟩)=_
  rw [←h,field_ticket Y H V G j C χ s y (insideAt_loose s p)]; rfl

lemma compass_domain_dense : DenseRange (compassKet Y H V G j C χ) := by
  apply (shore_dense Y H V G.history G.clipped j C χ).mono; intro x p
  obtain ⟨t,h⟩ := mem_iUnion.mp p; obtain ⟨f,rfl⟩ := h; let y:= fromField Y H j t f
  exact ⟨enclose Y H G (flank j 0) true t y, compass_land Y H V G j C χ t _ y.val rfl y.property (ticket_mem Y H G y.property)⟩

local notation "B₀" => (peninsula Y H V G.history G.clipped j false C χ).E
local notation "R" => (peninsula Y H V G.history G.clipped j false C χ).U
local notation "W" x:max => compassKet Y H V G j C χ x

structure LinkCheck : Prop where
  life : Exceeds Y H V s G.history G.clipped j C χ δ f z S o u d p w
  base : Survivor Y H V s G.history G.clipped j C z o u d S f χ
  first : z₀ ∈ insideAt Λ l K true (g'₀ S) s
  second : z₁ ∈ insideAt Λ l K true (g'₁ S) s
  spacing : ∀ i : Axis, ∀ x ∈ g'₀ S, ∀ y ∈ g'₁ S, x i+δ≤ y i
  apart : Disjoint D₀ D₁
  coveredRegions : IsCompact D₀ ∧ IsCompact D₁
  -- no periodic shortcut *between* them on all these levels and all lifts; support
  -- control maps `g'₀`,`g'₁` into the corresponding hulls. Used in interpreting
  -- displacement with Euclidean data on finite partners (not for imaginary times).
  coverDistances : ∀ᶠ n in atTop, ∀ t : ℕ, PhaseChoice.FullDistances
    (volumeAround Λ l t (reflectedBox j 0 (streetBox (tent Y H) p S) ∪ streetBox (tent Y H) w S)) (Journey.side Y (i (G.rows n)) (s+t))
  inquiry : pinhole (Dome K) s z₀ * pinhole (Dome K) s z₁ ∈ PhaseChoice.circum Λ l K false (D₀∪D₁) Ω
  paid : κ (z₀*z₁) = (ticket Y H G s (leg j p (fromStrict f))) * κ z₁
  -- Lower bound for the actual gauge-inv physical test on the selected reconstruction domain
  answer : 1/32 ≤ ‖sameRead Y H V G j C χ s (z₀*z₁)‖
  -- Thus no product reading on this very gauge--matter split basis for this budget.
  see_basis : ∃ a b g g' : Dome (tent Y H), NoDecompose Y H V G j C χ s p w z u d S o a b g g'
  -- Carry its definite response into the spatially continuous candidate. In general the
  -- projections change the Gram. Not this one; and scene is a partially-continuous extension.
  presentation :
    ∃ x y : Domain Y H G true (flank j 0), flipMark j (tent Y H) x.val=κ z₀ ∧ y.val=κ z₁ ∧
      inner ℂ (physicalKet Y H V G j C χ x) (physicalKet Y H V G j C χ y)=Psi (z₀*z₁) ∧
      inner ℂ (W x) (W y)=Psi (z₀*z₁) ∧
      ∀ᶠ v : RSpace in 𝓝 0,1/33 ≤ ‖inner ℂ (W x) (B₀ (v j).toNNReal (R (diameter v) (W y)))‖
  flat_silence : Silence f.val →
    Silence (leg j p (fromStrict f)).val ∧ Silence (reposition K w (fromStrict f)).val ∧ Silence (twin j p w (fromStrict f) (fromStrict f)).val

end charges
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
