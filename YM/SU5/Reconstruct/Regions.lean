import YM.SU5.Reconstruct.Chiral
/-!
# Keep the hierarchy on the actual panel over these bare-measurement limits

Using the finish prescription throughout; do *not* assert that coincident
products are products of independently blocked fields. `response` for a
character is in general not the vacuum average. We define the polynomial
measurement in a character by its matching reading AFTER E selection, using
SameCharacter, and prove that the bare integrals feed this very panel (i.e.
as the ORIGINAL joint E from which these characters are taken; no replacing
E globally by one `response`). This supports the later common dense OS test
system.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected
open Exhibition

/-- All our regional polynomial observables. Use actual physical regions in units of
**matter** spacing at level zero. Even chiral gauge invariants. -/
abbrev Pol (U:Set RSpace):= circum Λ l (tent Y H) true U Set.univ
abbrev PolAt (s:ℕ)(U:Set RSpace):= circum Λ l (tent Y H) true U (Set.univ∩ Set.Iic s)

lemma pol_of_level {U:Set RSpace}{s:ℕ}: PolAt Y H s U ≤ Pol Y H U :=
  PhaseChoice.circum_widens Y H Set.Subset.rfl Set.inter_subset_left
lemma polAt_up {U:Set RSpace}{s t:ℕ} (p:s ≤ t) : PolAt Y H s U ≤ PolAt Y H t U :=
  PhaseChoice.circum_widens Y H Set.Subset.rfl
    (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr p))
lemma levels {U:Set RSpace}{x:Altitude.Cloud (Dome K)} (p:x∈ Pol Y H U) : ∃ s, x∈ PolAt Y H s U:=
  declaredGate Λ K l true _ _ p
lemma isotone {s:ℕ} : Monotone (PolAt Y H s) :=
  fun _ _ h=> PhaseChoice.circum_widens Y H h Set.Subset.rfl
lemma inside_budget {U:Set RSpace}{s:ℕ}{x:Altitude.Cloud (Dome K)}
    (p:x∈ PolAt Y H s U) : x∈ boardedDB K s := relatedHeight Y H s p le_rfl
lemma industry {U:Set RSpace}{s:ℕ}{x:Altitude.Cloud (Dome K)}
    (p:x∈ PolAt Y H s U) :
    ∀ g : GPhysical, rainfall Λ K g x=x := ((well_spec ..).1 p).2
lemma pressured {U:Set RSpace}{s:ℕ}{x:Altitude.Cloud (Dome K)}(p:x∈ PolAt Y H s U) :
    ∃ C:ℝ, 0 ≤ C ∧ x∈PolAt Y H s (U ∩ Tapestry.cabin C) := by
  obtain ⟨n,h⟩:= (wellExhaustion Λ K l true (handstamp U) _ x p).exists
  refine ⟨n,(by positivity), wellGrows Λ K l true _ _ _ _ Set.Subset.rfl ?_ h⟩
  intro i t; refine ⟨t.1,?_⟩; intro j
  have hl:|i j|≤(n:ℝ):= t.2 j
  change |i j/2|≤ (n:ℝ)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)
section barebill
local notation "ir" r:max=> i (G.rows r)
local notation "uv" r:max=> k (G.columns r)

/-- The bare readings, on the sector clock itself (honest joint sharp histories,
on the selected lanes). No variable-probe limit being claimed. -/
noncomputable def readingAtTop (m t:ℕ) (x:Altitude.Cloud (Dome (tent Y H))) :=
    let μ:= prior SU.group (More (side Y m (Y.uv t)))
    (∫ U: Pane (side Y m (Y.uv t)), bareAmplitude Y m t (atCutoff Y H m t x) U ∂μ)/
      (∫ U: Pane (side Y m (Y.uv t)), bareAmplitude Y m t 1 U ∂μ)

lemma interior_payment (s:ℕ): ∀ᶠ r:ℕ in atTop, Pay Y s (i (G.rows r)) (k (G.columns r)) := by
  filter_upwards [G.history.finance s] with i p
  exact ⟨p.depth,p.enters⟩

lemma gives_E {s:ℕ} {x:Altitude.Cloud (Dome K)} (p:x∈boardedDB K s) :
    Tendsto (fun r:ℕ=>readingAtTop Y H (i (G.rows r)) (k (G.columns r)) x) atTop
      (𝓝 (vistaTake Y H D.toExhibition x)) := by
  let c: ℕ→ WedgeStage:=fun y=> ⟨G.rows y,G.columns y,(D.status ..).mp (G.history.gate y)⟩
  have h : Tendsto c atTop followStage:=tendsto_comap_iff.mpr G.history.growsA.tendsto_atTop
  obtain ⟨S,w⟩:= anyWords K s x p
  obtain ⟨Tg,z⟩:= Tapestry.issued.mp w
  apply ((D.livePocket Y H S s z).2.comp h).congr'
  filter_upwards [interior_payment Y H G s] with i v
  exact (identifyRevenue Y H _ _ s p v).2.2
end barebill

variable (C : ∀ j:Axis, Tower.Arena Y H G.history.circuit j 0 false)
local notation "𝔇" i:max => displayAlgebra Y H V Q Qt i false (C i)
-- choose axis 0 as in Glass
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)

noncomputable def sch : Altitude.Cloud (Dome K) →ₗ[ℂ] ℂ :=
    onDrawing Y H V G D.toExhibition 0 C (SameCharacter.resident Y H V G 0 false (C 0) c)

local notation "S" c:max => sch Y H D G C c
noncomputable abbrev fieldArg (x: Dome K) : Marks K false :=
  ⟨x.val,x.property,by simp⟩
local notation "arg" x:max=> fieldArg Y H x
local notation "Ω" c:max s:max=> response Y H V s Q Qt 0 false (C 0) c

lemma sch_mark (s:ℕ) {x:Altitude.Cloud (Dome K)} (p:x∈boardedDB K s) :
    (sch Y H D G C c) x = response Y H V s Q Qt 0 false (C 0) c
      (fieldArg Y H ((P₀ s) x)):= by
  let R:=SameCharacter.resident Y H V G 0 false (C 0) c
  have he := drawAt Y H V G D.toExhibition 0 C R p
  let f := fieldArg Y H ((P₀ s) x)
  refine he.trans ?_
  exact (evaluates Y H V G 0 C R s f).trans (SameCharacter.sameReading Y H V G 0 false (C 0) c s f)
lemma sch_axes (j:Axis) (s:ℕ) {x:Altitude.Cloud (Dome K)}(p:x∈boardedDB K s) :
    (S c) x= response Y H V s Q Qt j false (C j)
      (displacement Y H V Q Qt 0 false (C 0) c j (C j))
      (fieldArg Y H ((P₀ s) x)) :=
  (sch_mark Y H D G C c s p).trans (across_response ..).symm

lemma sch_sample (s:ℕ)(x:χ): (S c) (pinhole χ s x) = (Ω c s) (fieldArg Y H x):=by
  rw [sch_mark Y H D G C c s (short_pinhole s x), Exhibition.vistaFinish,Decking.outcrop]; rfl
lemma measures_mean
    (P: Panel Y H D.univ_ G.history G.clipped 0 false (C 0))
    (p: Issued Y H D.univ_ G.history G.clipped 0 false (C 0) P) (n:ℕ)
    {x:O} (q:x∈boardedDB K n) :
    (∫ a,(S (P.character a)) x∂P.μ) = vistaTake Y H D.toExhibition x := by
  simp_rw [sch_mark Y H D G C _ n q]
  rw [survives_check Y H V n Q Qt 0 false (C 0) P p,vistaCall Y H n _ (Dₚ) q]; rfl
lemma panel_from_readings
    (P: Panel Y H D.univ_ G.history G.clipped 0 false (C 0))
    (p: Issued Y H D.univ_ G.history G.clipped 0 false (C 0) P) (n:ℕ)
    {x:O} (q:x∈boardedDB K n) :
    Tendsto (fun r:ℕ=> readingAtTop Y H (i (G.rows r)) (k (G.columns r)) x) atTop (𝓝 (∫ a, (S (P.character a)) x∂ P.μ)) := by
  rw [measures_mean Y H D G C P p n q]; exact gives_E Y H D G q
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
