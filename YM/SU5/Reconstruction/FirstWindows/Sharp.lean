import YM.SU5.Reconstruction.FirstWindows.Chiral
/-!
# All local chiral even and polynomial readings, paid to one path

Physical realization and compatibility of the refinement with BOTH the sharp chiral
histories and the selected linear value. On the same joint (further thinning G) path,
through any cutoff. Even with observation levels different between queries. We do not
claim that the component's own readings are limits of the unselected finite-history
readings; their **mixture** is. -/
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
open SlabMark Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
  Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false

variable {L : Rack Λ l} {B : Clay Λ l} {T : ℕ → ℕ → Tariff} {t : ℕ → Tariff}
  (Z : Fashion Y H i k I E L B T t)
variable {q : Bool} (U : Set RSpace) (x : FiniteGaugeDataPoly (tent Y H))

local notation "ℒ" => Domain Y H G false Set.univ
local notation "ir₀" n:max => i (G.rows n)
local notation "uv₀" n:max => k (G.columns n)
local notation "f₀" => (⟨realize Y H Z.toExhibition x, always_realizes Y H V G Z.toExhibition x⟩ : Domain Y H G false Set.univ)

set_option maxHeartbeats 500000 in
lemma value_along : Tendsto (fun n => taking Y H (i (G.rows n)) (k (G.columns n)) x.val) atTop
    (𝓝 (vistaTake Y H Z.toExhibition x.val)) := by
  obtain ⟨n,h⟩ := curve.mp x.property
  let A : ℕ → WedgeStage := fun m=>⟨G.rows m,G.columns m,(Z.status ..).mp (G.history.gate m)⟩
  obtain ⟨S,v⟩ := anyWords K n x.val h
  obtain ⟨M,v⟩ := issued.mp v
  let b := Z.livePocket Y H S n v
  let F (t:WedgeStage) : ℂ := taking Y H (i t.vol) (k t.uv) x.val
  have hh : Tendsto F followStage (𝓝 (vistaTake Y H Z.toExhibition x.val)) := b.2
  change Tendsto (F ∘ A) atTop _
  exact hh.comp (show Tendsto A atTop followStage from tendsto_comap_iff.mpr G.history.growsA.tendsto_atTop)

theorem along_election (C : ∀ j:Axis, Arena Y H G.history.circuit j 0 false) (j : Axis)
    (P : Panel Y H V G.history G.clipped j false (C j))
    (p : Issued Y H V G.history G.clipped j false (C j) P) :
    Tendsto (fun n => taking Y H (i (G.rows n)) (k (G.columns n)) x.val) atTop
      (𝓝 (∫ a, osValue Y H V G j (C j) (P.character a) f₀ ∂P.μ)) := by
  rw [mixture Y H V G j (C j) P p]
  have hT : Nonempty P.X := by
    letI := p.normalized
    -- Measure univ=1
    exact MeasureTheory.nonempty_of_isProbabilityMeasure P.μ
  rw [(realize_read Y H V G Z.toExhibition j C (P.character (Classical.arbitrary _)) x _).2]
  exact value_along Y H G Z x

section period

abbrev HeightWindow (J : Calibration) (U : Set RSpace) (s : ℕ) :=
  jetty Λ l J true (PhaseChoice.handstamp U) ((Set.univ : Set ℕ) ∩ Set.Iic s)

-- lower declaration PaidQuality. no H':σ positivity statement below.
local notation "roll" t:max m:max k:max => ((Y.voyage m).X (Y.uv k)).gram t
local notation "cape" m:max k:max => (Y.voyage m).CapeT k
local notation "S₀" m:max s:max => Journey.side Y m s
local notation "Tst" s:max m:max k:max => attire (breathing Y H s m k x.val)

structure SharpRecord (q : Bool) (s n m k' : ℕ) (S : Finset Cover) : Prop where
  affordable : Pay Y (s+n) m k'
  -- check actual representation, even though `x` declaration above needed
  care : x.val ∈ HeightWindow (Λ:=Λ) (l:=l) (tent Y H) U s
  region : AtSupport false (Satin.region (volumeAround Λ l n S) (Journey.side Y m (s+n)))
    (attire (breathing Y H (s+n) m k' x.val))
  pays_region : PhaseChoice.SupportedPhysically Λ l (s+n) (volumeAround Λ l n S) U
  unwrapped : PhaseChoice.FullDistances (volumeAround Λ l n S) (Journey.side Y m (s+n))
  covariant : q = true → Buffered.covariant (attire (breathing Y H (s+n) m k' x.val))
  reading :
    let Tt:= s+n
    let Z:=roll Tt m k'
    let F:= fun z: Orbit (Journey.side Y m Tt)=>
      inner ℂ (mateK (S₀ m Tt)) (acts ((Tst Tt m k') (drawn (cape m Tt) z)) (denZ Z Λ.U (cape m Tt) z))
    (((Y.voyage m).X (Y.uv k')).gram 0).beta = Λ.x
    -- same partition denominator and actual normalized formula
    ∧ Integrable F (city (Journey.side Y m Tt)) ∧
      partitionZ Z Λ.U (cape m Tt)≠0 ∧ taking Y H m k' x.val = (∫ z,F z∂city (Journey.side Y m Tt)) / partitionZ Z Λ.U (cape m Tt)
      ∧ partitionZ Z Λ.U (cape m Tt) = partitionZ (roll (Y.uv k') m k') Λ.U (cape m (Y.uv k'))

include V
theorem sharp_record (v : x.val ∈ questions Λ l K q U) (s : ℕ)
    (h : x.val∈ HeightWindow (Λ:=Λ) (l:=l) (tent Y H) U s) :
    ∃ S : Finset Cover, PhaseChoice.SupportedPhysically Λ l s S U ∧ ∀ᶠ r in atTop,
      Tapestry.Pay Y s (ir₀ r) (uv₀ r) ∧
        ∀ n, s+n ≤ Y.uv (uv₀ r) → SharpRecord Y H U x q s n (ir₀ r) (uv₀ r) S := by
  obtain ⟨S,t,e⟩ := covers_now Y H s x.val h
  have ha := jettyBan Λ l K true (PhaseChoice.handstamp U) Set.univ s h
  refine ⟨S,t,?_⟩
  have hU : ∀ᶠ r : ℕ in atTop, ∀ n : ℕ, PhaseChoice.FullDistances (volumeAround Λ l n S) (S₀ (ir₀ r) (s+n)) :=
    ((V.pick.grow_i.comp G.history.growsA).tendsto_atTop).eventually (unwrapped Y H s S)
  filter_upwards [G.history.finance s,hU] with r p hx
  have hz : Pay Y s (ir₀ r) (uv₀ r) := ⟨p.depth,p.enters⟩
  refine ⟨hz,fun n u=>?_⟩
  have hw : Pay Y (s+n) (ir₀ r) (uv₀ r):=⟨hz.1,u⟩
  obtain ⟨a,w,y⟩ := taking_formula Y H (s+n) (ir₀ r) (uv₀ r) x.val hw (Altitude.climbs _ (Nat.le_add_right ..) ha)
  refine ⟨hw,h,hike_coverage Y H s S ha (ir₀ r) (uv₀ r) n hw (e _ _ hz), t.persists n,hx n,?_ ,?reading⟩
  · intro he; exact paid_coherence Y H (ir₀ r) (uv₀ r) (s+n) hw x.val
      (show x.val ∈ well Λ K l true (PhaseChoice.handstamp U) Set.univ from (by rw [he] at v; exact v))
      (Altitude.climbs _ (Nat.le_add_right ..) ha)
  case reading =>
    exact ⟨prescribed_pivot ..,a,w,y, ((Y.voyage (ir₀ r)).X _).balance (s+n) u⟩

end period
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
