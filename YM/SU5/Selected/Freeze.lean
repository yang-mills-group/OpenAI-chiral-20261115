import VerifiedSatinGroundInteraction
/-!
# Freeze ONE mixed physical mark: finite observing resolution, in the consistent hierarchy

Use the gauge-site metric convention of `Narrowgate.lean`. One does not
send the source's observing resolution to ∞. Nonzero physical separation
here refers to the gauge--chiral link test class in `Filigree.lean`. It
includes pure matter words multiplied by gauge coefficients (on the first,
not auxiliary, field); each removal origin used by such a word is one of
the anchors, and none of its creation origins is any anchor. This
separation within the stencil, in **physical units**, is paid at the
observing resolution. We record it via the support lists and a bound on
`gaugePosition` valid for *any* such occurrences (the grammar uses y ≠ b
i); also record a fixed physical localization of even the arbitrarily fine
representatives. They are block transports of the mark, NOT evaluations of
its same formula on smaller mesh. Not a claim that individual letter
supports after smearing stay disjoint, nor that spacetime dilation or even
a change of observing resolution of the source of the test is available.
See also the separate questions of products at physically separated
supports, selection, interaction interpretation, and continuum geometry.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 1050000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Py.Rate.Pannier
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)

/-- One level-s gauge spacing in B/Tower's convention in level-zero fermion units. -/
def gaugeMesh (Λ : Preparation) (s : ℕ) : ℝ := 1 / (2 * (Λ.R.L.val : ℝ)^s)

def gaugePosition (Λ : Preparation) (s : ℕ) (x : Cover) (j : Axis) : ℝ :=
  (x j : ℝ) * gaugeMesh Λ s

lemma gaugeMesh_pos (Λ : Preparation) (s : ℕ) : 0 < gaugeMesh Λ s := by
  have ht := Λ.R.L.property
  unfold gaugeMesh
  positivity

/-- How the physical coordinates here compare to the actual reconstructed
(non-relativistic as of yet) tower clock and lattice translations. -/
lemma double_clock_calibration (Λ : Preparation) (s n : ℕ) :
    (whenly (timeMesh Λ) s n : ℝ) = (ruler Λ.block : ℝ) * n * gaugeMesh Λ s := by
  simp [whenly, MeshClock.mill, timeMesh, ruler, gaugeMesh]; ring

/-- Points in a translated box are displaced by physical n-tick displacements along j. -/
lemma shifted_points (j : Axis) (S : Finset Cover) (n : ℕ) {x : Cover}
    (p : x ∈ plow (tent Y H) j (n : ℤ) S) :
    ∃ y ∈ S, gaugePosition Λ s x j - gaugePosition Λ s y j =
      (whenly (timeMesh Λ) s n : ℝ) ∧
      ∀ i : Axis, i ≠ j → gaugePosition Λ s x i = gaugePosition Λ s y i := by
  obtain ⟨y,v,rfl⟩ := plow_stays K j (n:ℤ) S p
  refine ⟨y,v,?_,fun i h => ?_⟩
  · simp only [gaugePosition, moves, ↓reduceIte, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, double_clock_calibration]
    have e : (K).B = Λ.block := rfl
    rw [e]; ring
  · simp only [gaugePosition, moves, if_neg h]

lemma separate_chiral (Λ : Preparation) (s : ℕ) {x y : Cover} (h : x ≠ y) :
    ∃ j : Axis, 2 * gaugeMesh Λ s ≤
      |gaugePosition Λ s (nodeC x) j - gaugePosition Λ s (nodeC y) j| := by
  have h' : ¬ ∀ j : Axis, x j = y j := fun e => h (funext e)
  obtain ⟨j,hj⟩ := not_forall.mp h'
  refine ⟨j,?_⟩
  have e : nodeC x j - nodeC y j = 2*(x j-y j) := by simp [Lifted.nodeC]; ring
  have v : (1:ℤ) ≤ |x j-y j| := abs_pos.mpr (sub_ne_zero.mpr hj)
  rw [gaugePosition,gaugePosition,← _root_.sub_mul, abs_mul, abs_of_pos (gaugeMesh_pos ..)]
  apply mul_le_mul_of_nonneg_right _ (gaugeMesh_pos ..).le
  exact_mod_cast (show (2:ℤ) ≤ |nodeC x j - nodeC y j| by
    rw [e,abs_mul, abs_of_nonneg (by norm_num : (0:ℤ) ≤ 2)]
    omega)

/-- Uniform physical localization (a finer site plus its own buffer also
stays in the SOURCE'S buffering of the source support). -/
lemma physical_shield (Λ : Preparation) (l : ℕ) (s : ℕ) (S : Finset Cover)
    (n : ℕ) {x : Cover} (v : x ∈ volumeAround Λ l n S) :
    ∃ y ∈ S, ∀ j : Axis, |gaugePosition Λ (s+n) x j - gaugePosition Λ s y j| +
      (reserve Λ l : ℝ) * gaugeMesh Λ (s+n) ≤ (reserve Λ l : ℝ) * gaugeMesh Λ s := by
  obtain ⟨y,hy,p⟩ := shield Λ l S n v
  have hL : 0 < Λ.R.L.val := Λ.R.L.property
  have he : gaugeMesh Λ s = (Λ.R.L.val:ℝ)^n * gaugeMesh Λ (s+n) := by
    rw [gaugeMesh,gaugeMesh,pow_add]; field_simp
  refine ⟨y,hy,fun j => ?_⟩
  specialize p j
  simp only [Pi.sub_apply,nsmul_eq_mul, Pi.mul_apply, Pi.pow_apply, Nat.cast_pow, Pi.natCast_apply] at p
  simp only [gaugePosition,he]; rw [←mul_assoc,← _root_.sub_mul,abs_mul,abs_of_pos (gaugeMesh_pos ..),←add_mul,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (gaugeMesh_pos ..).le
  have ht : |(x j:ℝ) - (Λ.R.L.val:ℝ)^n*(y j:ℝ)| + (reserve Λ l:ℝ) ≤ (Λ.R.L.val:ℝ)^n * (reserve Λ l:ℝ) := by exact_mod_cast p
  simpa only [mul_comm] using ht

variable {z : SU.Slot} {o : Cover} {q d w : ℕ}

/-- The observable in one fixed election, with its signs and inner readings at
all higher levels, physically contained in the *same* (buffered) local region.
Same Course and E for all of this data. -/
structure FixedLink (z : SU.Slot) (o : Cover) (q d : ℕ)
    (S : Finset Cover) (F : observable (tent Y H) true) : Prop where
  anchor_inj : Injective (booty o d q)
  anchors_here (r : Fin (q^4)) : nodeC (booty o d q r) ∈ S
  mark_mem : F.val ∈ Filigree K (Window.family z) (booty o d q) S
  noncontact : 0 < gaugeMesh Λ s ∧
    ∀ (r : Fin (q^4)) (y : Cover), y ≠ booty o d q r →
      ∃ j : Axis, 2*gaugeMesh Λ s ≤
        |gaugePosition Λ s (nodeC y) j - gaugePosition Λ s (nodeC (booty o d q r)) j|
  mixed : 1 / 4 ≤ ‖E s F.val‖
  further (n : ℕ) :
    let f := upward Y H Q true F s n
    f.val = stream Y H D s n F.val ∧
    f.val ∈ observ K (volumeAround Λ l n S) true ∧
    E (s+n) f.val = E s F.val ∧
    (∀ x ∈ volumeAround Λ l n S, ∃ y ∈ S, ∀ j : Axis,
      |gaugePosition Λ (s+n) x j - gaugePosition Λ s y j| +
        (reserve Λ l : ℝ) * gaugeMesh Λ (s+n) ≤ (reserve Λ l : ℝ) * gaugeMesh Λ s) ∧
    ∀ (j : Axis) (C : Arena Y H Q.circuit j 0 true),
      let Ω := seat0 Y H V Q j true C
      let A := cap Y H V (s+n) Q Qt j true C f
      A = cap Y H V s Q Qt j true C F ∧
        inner ℂ Ω (A Ω) = E s F.val

lemma freeze (F : observable (tent Y H) true) (S : Finset Cover)
    (g : Injective (booty o d q)) (seats : ∀ r, nodeC (booty o d q r) ∈ S)
    (p : F.val ∈ Filigree K (Window.family z) (booty o d q) S)
    (m : 1/4 ≤ ‖E s F.val‖) : FixedLink Y H V s Q Qt z o q d S F := by
  refine ⟨g,seats,p,⟨gaugeMesh_pos .., fun _ _ => separate_chiral Λ s⟩,m,?_⟩
  have h := (FilTest p).widen
  intro n
  refine ⟨rfl,chroma Y H Q.circuit s n ((obs_in ..).2 ⟨h,F.property.2 rfl⟩),
    (proceeds Y H Q.circuit s n h).2,fun _ v => physical_shield Λ l s S n v,?_⟩
  intro j C
  have he := cap_level (F := F) Y H V s Q Qt j true C (s+n) (Nat.le_add_right s n)
  rw [show s+n-s=n by omega] at he
  refine ⟨he,?_⟩
  rw [he, inspected Y H V]

lemma late_fixed_link (z : SU.Slot) {C Z : ℝ} (g : Papal.Cornet Y H q d w C Z) :
    ∀ᶠ s in atTop, ∀ o : Cover, ∃ F : observable (tent Y H) true,
      FixedLink Y H V s Q Qt z o q d (Sen o (payout d q w)) F ∧
      ¬ CF.Pannier.Chancel.Parcel K (Window.family z) (booty o d q)
        (Sen o (payout d q w)) (E s) := by
  let G : SatinVerification.GroundExtension (i := i) (k := k) (E := E) Y H := ⟨D,a,b,Q,Qt⟩
  let j : Axis := 0
  let room := Classical.choice (voyage_H Y H V Q.circuit j 0 true)
  have hp := Papal.ground_mixed_probes Y H V G j room g z
  filter_upwards [hp, Papal.Cornet.impression Y H C Z V z g] with s p u
  intro o
  obtain ⟨F,v,t,h,he⟩ := p o
  refine ⟨F,freeze Y H V s Q Qt F _ (g.cents o) (Papal.stake_centers Y H o d q w) v (by rwa [h] at he), u o⟩

/-- First step before specializing a vacuum component. -/
theorem first_step (ε η : ℝ) (small : 0 < η) :
    ∃ (P : Preparation) (l : ℕ), ε < P.x ∧ P.d ≤ η ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
    ∃ (H : Real.exp 1 ≤ P.x) (Y : Course P (VolumeCape.Dream.Nimbus l))
      (a b : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ)
      (E : ℕ → Family (tent Y H) → ℂ) (V : Universal Y H a b I E)
      (G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H)
      (q d w s : ℕ), ∀ (z : SU.Slot) (o : Cover), ∃ F : observable (tent Y H) true,
        FixedLink Y H V s G.history G.clipped z o q d (Sen o (payout d q w)) F ∧
        ¬ CF.Pannier.Chancel.Parcel (tent Y H) (Window.family z) (booty o d q)
          (Sen o (payout d q w)) (E s) := by
  obtain ⟨P,l,Z,large,bound,nom,H,Y,q,d,w,C,g,a,b,I,E,V,⟨G⟩,_⟩ :=
    Papal.mixed_law_with_ground ε η small
  obtain ⟨s,h⟩ := (Filter.eventually_all.mpr (fun z : SU.Slot =>
    late_fixed_link Y H V G.history G.clipped z g)).exists
  exact ⟨P,l,large,bound,nom,H,Y,a,b,I,E,V,G,q,d,w,s,h⟩

end YM.CF.Buffered.Afterglow.Tower.Selected
#check @YM.CF.Buffered.Afterglow.Tower.Selected.first_step
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.physical_shield
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.shifted_points
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.first_step
