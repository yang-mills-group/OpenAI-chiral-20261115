import YM.SU5.Same.BareReading

/- Reissue on auxiliary smears, adapting YM/SU5/Same/BareReading -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

variable (P : Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) (c r n:ℕ→ℕ) (w : Lead.Clan → Prism)
local notation "K" => P.calibration
local notation "Q" k:max i:max => P.soldTrumpet A c r n w k i
local notation "G₀" k:max i:max => P.gaugeTrumpet A c r n w k i
local notation "G₁" k:max i:max => (G₀ k i).kiss P 3
local notation "P₁" k:max i:max => (Q k i).kiss P 3

variable (F U : SampleDose) (T' : P.HandleWith x c r A n) (a b : Lead.Clan) (i t : ℕ)

local notation "X" t:max k:max i:max => P.prepared t (P₁ k i) F
local notation "Y" t:max k:max i:max => P.prepared t (Q k i) U
local notation "X'" t:max k:max i:max => P.prepared t (G₁ k i) F
local notation "Y'" t:max k:max i:max => P.prepared t (G₀ k i) U
local notation "b!" a:max i:max => P.gaugeTrumpet_birth x A c r n w T' a i
local notation "z'" t:max k:max i:max => P.thinGridKet x t (G₀ k i) (b! k i) (flipDose F 3)
local notation "v'" t:max k:max i:max => P.thinGridKet x t (G₀ k i) (b! k i) U
local notation "π[" t "]" => P.thinSplit x t
local notation "σ[" t "]" => P.singleState 3 t x
local notation "m!" i:max => c (n i)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "ι" => P.enter 3 ξ

private lemma iroPair (B L : P.Apron)(h : B.s ≤ t)(hh : L.s ≤ t)
    (v0 : P.WallBefore B F 0)(v1:P.WallAfter L U 0)(pB : P.birthF 3 B.s B.F)
    (pL : P.birthF 3 L.s L.F)
    (k₀ : PureGauge K B.F) (k₁ : PureGauge K L.F)
    (eB : P.singleState 3 B.s x B.F = 0)(eL : P.singleState 3 L.s x L.F=0) :
    P.ShadowPair x F U t B L pB pL (P.spacePrice (B.kiss P 3) F) (P.spacePrice L U) := by
  have hL := P.reflect_keepsPure k₀ 3
  have hp : PureGauge K (P.prepared t (B.kiss P 3) F) := P.prepare_pure (B.kiss P 3) t hL F
  have he : PureGauge K (P.prepared t L U) := P.prepare_pure (L) t k₁ U
  obtain ⟨v,d,g,q'⟩ := P.thin_grid_flip x t (B) pB F v0 h
  have hv : P.reflectTest 3 (P.prepared t (B.kiss P 3) F) = v := by rw [← d]; exact aureoleTwice ..
  let g' : P.birthF 3 t (P.reflectTest 3 (P.prepared t (B.kiss P 3) F)) := hv.symm ▸ g
  have hl : σ[t] (P.prepared t (B.kiss P 3) F) = 0 := P.Dose_zero t (B.kiss P 3) F x
    (((P.common_reading B.s x (B).F 3).2.2.1).trans ((congrArg star eB).trans (star_zero _))) h
  have hr : σ[t] (P.prepared t L U) = 0 := P.Dose_zero t (L) U x eL hh
  let f (a' : P.Test) (p : PureGauge K a') := (P.thin_comparator_LocalFieldBounds x t).1.link a' p
  exact {
    pureL := hp
    pureR := he
    locatorL := P.prepared_at t (B.kiss P 3) F h
    locatorR := P.prepared_at t (L) U hh
    ketL := ⟨g', (P.identical_F 3 ξ t g' g hv).trans q'⟩
    ketR := P.thin_grid_view x t (L) pL U v1 hh
    pairL := P.thin_pair_grid x t (B) pB F (L) pL U v0 v1 h hh
    share := f _ (gaugePure_mul K hp he)
    halt := ⟨(f _ hp).trans hl,(f _ he).trans hr,hl,hr⟩ }

variable (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
    (g h : ℕ) (J:P.Ellis 3 x) {s k : ℕ} {K' : P.Register}
local notation "C" => reviewEarlierBox
local notation "D" => reviewLaterBox
local notation "Υ" t:max i:max => P.gaugeShadowPrism A c r n w F U i t
local notation "Ξ!" k:max => DoseTravel.beam H F (P.earlierProfile x V w 1 k)
local notation "J!" k:max => DoseTravel.beam H U (P.laterProfile x V w 1 k)
local notation "Y₀" => P.readPrism x V w 1 F U


structure Sheets :Prop where
 supports:tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites
 armada: P.ThinArmada x A c r n w T' V g h
 then_read: P.AuthorizedPair x A c r n w V T' 1 F U

variable (R:P.Sheets x A c r n w F U T' V g h)
variable (K₀ : ∀ i, PureGauge P.calibration (A i).F)
include R K₀
omit R in
private lemma iroBare (t : ℕ) (a b : Lead.Clan) (i : ℕ) (z : m! i ≤ t) (v0 : P.WallBefore (G₀ a i) F 0) (v1 : P.WallAfter (G₀ b i) U 0) :
    P.SolidShadow x A c r n w F U T' a b i t := by
  refine iroPair P x F U t (G₀ a i) (G₀ b i) z z v0 v1 (b! a i) (b! b i)
    (P.gaugeTrumpet_purity A c r n w a i (K₀ i)) (P.gaugeTrumpet_purity A c r n w b i (K₀ i))
    (P.trumpets_center (w a) (P.gaugeStitch a (A i) (c (n i)) (r (n i))) x)
    (P.trumpets_center (w b) (P.gaugeStitch b (A i) (c (n i)) (r (n i))) x)

lemma iroShelter : ∀ᶠ i in atTop, ∀ t : ℕ, m! i ≤ t → ∀ a b : Lead.Clan,
    P.SolidShadow x A c r n w F U T' a b i t := by
  filter_upwards [R.then_read.epoch] with i q t h a b
  let E := q a b
  have v0 : P.WallBefore (G₀ a i) F 0 := fun x u=> by
    rw [P.gaugeTrumpet_width]; have hp := E.beforeWall x u; rw [Apron.kiss_width] at hp; exact hp
  have v1 : P.WallAfter (G₀ b i) U 0 := fun x u=> by
    rw [P.gaugeTrumpet_width]; exact E.afterWall x u
  exact P.iroBare x A c r n w F U T' K₀ t a b i h v0 v1

omit K₀
include J
lemma iroPos (p: ∀ x∈tsupport U.val,(1:ℝ) ≤ x (3:Axis)) (t:ℕ→ℕ) (z:Tendsto t atTop atTop):
    Tendsto (fun i=> v' (t i) b i) atTop (𝓝 (ι (J! b))) := by
  apply P.dynamic_grid_ket x (fun i => G₀ b i) (fun i=>b! b i) U 1 (P.profilesH x w b V)
    (P.profilesZ x V w b) J (R.armada.energy b).1 zero_lt_one
    (fun t p=> P.illuminate_bank x A c r n w V g h T' R.armada b t p) p _ t z
  exact P.gaugeTrumpet_heat_H x A c r n w T' b V g h R.armada 1 (by norm_num)
-- `p: U support` argument; R still specialized with F U. earlier flip use pure repeat because R not available with flipDose
lemma iroPre (t:ℕ→ℕ) (z:Tendsto t atTop atTop):
    Tendsto (fun i=> z' (t i) a i) atTop (𝓝 (ι (Ξ! a))) := by
  rw [← P.illuminate_flip x w V 1 a F]
  apply P.dynamic_grid_ket x (fun i=> G₀ a i) (fun i=>b! a i) (flipDose F 3) 1 (P.profilesH x w a V) _
    J (R.armada.energy a).1 zero_lt_one (fun t p=> P.illuminate_bank x A c r n w V g h T' R.armada a t p) _ _ t z
  · intro y p
    have e: poseMirror 3 y ∈ tsupport F.val:= (show y ∈ poseMirror 3 ⁻¹' tsupport F.val from flipBudget .. ▸ p)
    have hx : (opposeR 3 y) 3 < -1 := (R.supports.1 e (3:Axis) (Set.mem_univ _)).2
    rw [show opposeR 3 y 3 = - y 3 from if_pos rfl] at hx
    linarith
  exact P.gaugeTrumpet_heat_H x A c r n w T' a V g h R.armada 1 (by norm_num)
include K₀

structure Iridescence : Prop where
  shelter : ∀ᶠ i in atTop, ∀ t : ℕ, m! i ≤ t →
    ∀ a b : Lead.Clan, P.SolidShadow x A c r n w F U T' a b i t
  pureField (a : Lead.Clan) (i : ℕ) : PureGauge K (G₀ a i).F
  budgetWidth (z : Lead.Clan) (i : ℕ) (j : Axis) : (G₀ z i).realWidth P j = (Q z i).realWidth P j
  sameProfile (z : Lead.Clan) (t : ℝ) (e : 0<t) :
    Tendsto (fun i => P.cradleH x (G₀ z i) (b! z i) t) atTop (𝓝 (P.profilesH x w z V t))
  owns (t:ℕ→ℕ) (p:∀ᶠ i in atTop, m! i ≤ t i) :
    (∀ a b : Lead.Clan, Tendsto (fun i=> z' (t i) a i) atTop (𝓝 (ι (Ξ! a))) ∧
      Tendsto (fun i=> v' (t i) b i) atTop (𝓝 (ι (J! b)))) ∧
    Tendsto (fun i=> (Υ (t i) i) (P.thinSplit x (t i))) atTop (𝓝 Y₀)
  -- incompatible same vacuum comparator by these exact segment means
  mixedForecast (t:ℕ→ℕ)(p:∀ᶠ i in atTop, m! i ≤ t i) :
    Tendsto (fun i=> P.reportPrism A c r n w F U i (t i) π[t i]) atTop (𝓝 0)

theorem earnsIridescence : P.Iridescence x A c r n w F U T' V := by
  let e := P.iroShelter x A c r n w F U T' V g h R K₀
  refine ⟨e,fun a i=> P.gaugeTrumpet_purity A c r n w a i (K₀ _),fun a i j=> P.gaugeTrumpet_width A c r n w a i j,
    fun a t p=> P.gaugeTrumpet_heat_H x A c r n w T' a V g h R.armada t p,
    fun t p=> ?_, fun t p=> ?_⟩
  · have ht := tendsto_atTop_mono' _ p R.then_read.high
    have h₁ (a : Lead.Clan) := P.iroPre x A c r n w F U T' a V g h J R t ht
    have h₂ (a : Lead.Clan) := P.iroPos x A c r n w F U T' a V g h J R
      (fun x hk=> ((R.supports.2 hk (3:Axis) (Set.mem_univ _)).1).le) t ht
    refine ⟨fun a b=>⟨h₁ a,h₂ b⟩, tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=>?_⟩
    have hw := (h₁ a).inner (𝕜:=ℂ) (h₂ b)
    rw [LinearIsometry.inner_map_map] at hw
    refine hw.congr' ((p.and e).mono fun i u=> ?_)
    exact ((((u.2 (t i) u.1 a b).share).trans (u.2 (t i) u.1 a b).pairL)).symm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [p,R.then_read.comparison] with i t' q
  exact (q _ t').2.symm


#print axioms earnsIridescence
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
