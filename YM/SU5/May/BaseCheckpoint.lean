import SU5SatinVerifiedNovember6
import YM.SU5.May.KetMatch
/-!
# May Project - the fixed probes and this vacuum. CP1

Remaining physical operator price: part of the analytic continuation. The
bounded operators now constructed and their Hilbert spaces/time
translations are NOT yet localized in the Mink sense. This checkpoint buys,
among other things, the eligibility and quite a bit of the Euclidean operator
and pre-real-time part of the specification. It fixes the support and what
the weak approximations on this character would have to achieve on them.

**NO** rechoice of character. Unpack the given witness only HERE to build
`existsPurchase`. Work with precisely this data (not a piecemeal existential)
through subsequent checkpoints.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine

open Aria Germ Alliance SelectionAnalysis Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "C" => P.room
local notation "Y" => P.run
local notation "L" => P.large
local notation "P₁" => P.par
local notation "V" => P.law
local notation "G" => P.projection
local notation "H" => P.history
local notation "H₁" => P.projection.clipped
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J
open Selected (doorstep indoor fort ride peninsula vocation displacement compass_origin placement atEstate vocate)
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget
local notation "ℳ" => marks (timeMesh P.par)
local notation "Q" => Follows Y L V G j (C j) χ
local notation "K" => P.calibration
local notation "D'" => Domain Y L G
local notation "X'" => Sky K
local notation "Hr" => Selected.ride Y L V H H₁ j false (C j) χ
local notation "R" => peninsula Y L V H H₁ j false (C j) χ
local notation "Pₓ" => P.maySaunters x j
local notation "P₀" => (Pₓ).orthogonalProjectionOnto
local notation "M" => P.mayFort x j
local notation "Ω'" => vocation Y L V H H₁ j false (C j) χ
local notation "ι" => OSvector Y L V G j (C j) χ
local notation "Ψ" => osValue Y L V G j (C j) χ
local notation "α" => P.glasshouseCharacter 3 x
local notation "Z" => P.mayCarries x j
local notation "mv" => FirstWindows.move K
local notation "ej" => Chambers.eject j
local notation "tk" t:max => FirstWindows.ticket Y L G t

open MacroGrid SatinNucleus SatinJets DoseTravel
open Anvil
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
structure Trust
    (spine : Spine)
    (register : spine.Register)
    (x : spine.Spectrum0 3)
    (c : ℕ→ℕ)
    (r : ℕ→ℕ)
    (ellis : spine.Ellis 3 x)
    (i0 : ℕ)
    (F : SampleDose)
    (U : SampleDose)
    (A : ℕ→ spine.Apron)
    (n : ℕ→ℕ)
    (w : Lead.Clan→ Prism)
    (crew : ∀ j : Axis, List Axis → ℝ → spine.ColorHil j (spine.advocate 3 x j))
    (g : ℕ)
    (h : ℕ)
    (handle : spine.HandleWith x c r A n)
    (early : spine.MayBooth F reviewEarlierBox)
    (late : spine.MayBooth U reviewLaterBox) : Prop where
  beta : ∀ i k, (((spine.run.voyage i).X (spine.run.uv k)).gram 0).beta = spine.par.x
  exp : Experiment spine register c r x ellis
  tr : spine.Transmission x c r
  normal : F.Normalized ∧ U.Normalized
  inside : tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites
  six : spine.ReturnsSix x (c i0) (r i0) 0 F U
  fixed : spine.FixedSatinReadings register x (c i0) (r i0) 0 F U
  lab : spine.FullPrismLab x A c r n w crew g h handle 1 F U reviewEarlierBox reviewLaterBox (c i0) (r i0) register
  loud : ∃ d : ℝ, 0 < d ∧ LoudMargin (spine.readPrism x crew w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (spine.azurePrism x A c r n w F U i t) d
  limits : (∀ᶠ i in atTop, Tendsto (fun t => spine.azurePrism x A c r n w F U i t) atTop
          (𝓝 (spine.thinJournal x A c r n w handle F U i))) ∧
          Tendsto (spine.thinJournal x A c r n w handle F U) atTop (𝓝 (spine.readPrism x crew w 1 F U))
  excludes : ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
        ∀ u : Charm.W spine.calibration, Verne.GNative spine.calibration u →
            (spine.prepared t (((spine.soldTrumpet A c r n w) a i).kiss spine 3) F).val ≠ u.val ∧
            (spine.prepared t ((spine.soldTrumpet A c r n w) a i) U).val ≠ u.val

abbrev Purchase : Type :=
  Σ ( spine : Spine) ,
    Σ ( register : spine.Register) ,
    Σ ( x : spine.Spectrum0 3) ,
    Σ ( c : ℕ→ℕ) ,
    Σ ( r : ℕ→ℕ) ,
    Σ ( ellis : spine.Ellis 3 x) ,
    Σ ( i0 : ℕ) ,
    Σ ( F : SampleDose) ,
    Σ ( U : SampleDose) ,
    Σ ( A : ℕ→ spine.Apron) ,
    Σ ( n : ℕ→ℕ) ,
    Σ ( w : Lead.Clan→ Prism) ,
    Σ ( crew : ∀ j : Axis, List Axis → ℝ → spine.ColorHil j (spine.advocate 3 x j)) ,
    Σ ( g : ℕ) ,
    Σ ( h : ℕ) ,
    Σ' ( handle : spine.HandleWith x c r A n) ,
    Σ ( early : spine.MayBooth F reviewEarlierBox),
    { late : spine.MayBooth U reviewLaterBox // Trust spine register x c r ellis i0 F U A n w crew g h handle early late }
lemma existsPurchase : Nonempty Purchase := by
  obtain ⟨P,K',c,r,x,J',i0,F,U,beta,ex,tr,e,f,p,q,s,k,A,n,w,v,g,h,T,u,j,l,t⟩:= exists_disclosed_satin_native_contrast
  obtain ⟨D⟩:= MayBooth.choose P F reviewEarlierBox e p
  obtain ⟨E⟩:= MayBooth.choose P U reviewLaterBox f q
  exact ⟨⟨P,K',x,c,r,J',i0,F,U,A,n,w,v,g,h,T,D,E,beta,ex,tr, ⟨e,f⟩,⟨p,q⟩,s,k,u,j,l,t⟩⟩
noncomputable def purchased : Purchase := Classical.choice existsPurchase

namespace Purchase
variable (y:Purchase)
abbrev spine := y.1
abbrev register := y.2.1
abbrev point := y.2.2.1
abbrev c := y.2.2.2.1
abbrev r := y.2.2.2.2.1
abbrev ellis := y.2.2.2.2.2.1
abbrev i0 := y.2.2.2.2.2.2.1
abbrev F := y.2.2.2.2.2.2.2.1
abbrev U := y.2.2.2.2.2.2.2.2.1
abbrev A := y.2.2.2.2.2.2.2.2.2.1
abbrev n := y.2.2.2.2.2.2.2.2.2.2.1
abbrev w := y.2.2.2.2.2.2.2.2.2.2.2.1
abbrev crew := y.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev g := y.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev h := y.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev handle := y.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev early := y.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev late := y.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma trust : Trust y.spine y.register y.point y.c y.r y.ellis y.i0 y.F y.U y.A y.n y.w y.crew y.g y.h y.handle y.early y.late := y.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

abbrev budget (t:ℕ) := y.c (y.n t)
abbrev body (a:Lead.Clan) (i:ℕ) : y.spine.Apron := y.spine.soldTrumpet y.A y.c y.r y.n y.w a i
abbrev earliest (a:Lead.Clan) (i t:ℕ) := y.spine.prepared t ((y.body a i).kiss y.spine 3) y.F
abbrev latest (a:Lead.Clan) (i t:ℕ) := y.spine.prepared t (y.body a i) y.U
abbrev euHead (a:Lead.Clan) (i t:ℕ) : (y.spine.mayHil y.point j).Op := y.spine.mayHead y.point j y.F y.early y.A y.c y.r y.n y.w a i t -- binder j FIRST by prior-variable convention
abbrev euToe (a:Lead.Clan) (i t:ℕ) : (y.spine.mayHil y.point j).Op := y.spine.mayToe y.point j y.U y.late y.A y.c y.r y.n y.w a i t
abbrev carry := y.spine.mayCarries y.point j
abbrev actualPrism := y.spine.reportPrism y.A y.c y.r y.n y.w y.F y.U
abbrev angularPrism := y.spine.fortPrism y.point j y.F y.U y.early y.late y.A y.c y.r y.n y.w
abbrev page := y.spine.thinJournal y.point y.A y.c y.r y.n y.w y.handle y.F y.U
abbrev finalPage := y.spine.readPrism y.point y.crew y.w 1 y.F y.U
abbrev headKet := y.spine.preLeft y.point 3 y.F y.early y.A y.c y.r y.n y.w
abbrev toeKet := y.spine.preRight y.point 3 y.U y.late y.A y.c y.r y.n y.w
abbrev headThin := fun a=> y.spine.mayThinLeft y.point y.F y.w y.crew a 1
abbrev toeThin := fun a=> y.spine.mayThinRight y.point y.U y.w y.crew a 1
abbrev read := fun t=> y.spine.singleState 3 t y.point
abbrev compareSplit := y.spine.thinSplit y.point
structure BasePrice : Prop where
  stamps : ∀ᶠ i:ℕ in atTop, ∀ t:ℕ,y.budget i ≤ t → ∀ (j:Axis) (a:Lead.Clan),
    y.spine.MayChord y.point j t y.early (y.earliest a i t) (y.euHead j a i t) ∧
    y.spine.MayChord y.point j t y.late (y.latest a i t) (y.euToe j a i t)
  pens (j:Axis) : Selected.Victory y.spine.run y.spine.large y.spine.law y.spine.history y.spine.projection.clipped false j (y.spine.room j) (y.spine.mayChar y.point j)
  buys (j:Axis) (v:y.spine.ManyF j (y.spine.advocate 3 y.point j)) (d:E4):
    let f:= y.spine.mayIntertwineS y.point j; let T:= peninsula y.spine.run y.spine.large y.spine.law y.spine.history y.spine.projection.clipped j false (y.spine.room j) (y.spine.mayChar y.point j); let S:= y.spine.seasons j (y.spine.advocate 3 y.point j)
    T.unit.translation d (f v)=f (S.unit.translation d v) ∧ T.ℚmeasure.diagonal (f v)= S.ℚmeasure.diagonal v
  reading : ∀ᶠ i:ℕ in atTop, ∀ t:ℕ,y.budget i ≤ t → (∀ (a:Lead.Clan),
    (read y t) (y.earliest a i t)=0 ∧ (read y t) (y.latest a i t)=0) ∧ y.actualPrism i t (y.compareSplit t)=0 ∧
    ∀ (j:Axis), y.angularPrism j i t = y.spine.glasshousePrism y.point y.A y.c y.r y.n y.w y.F y.U i t ∧
       y.angularPrism j i t=y.actualPrism i t (read y t)-y.actualPrism i t (y.compareSplit t)
  margin : ∃ d>0, LoudMargin y.finalPage d ∧ ∀ᶠ i in atTop, ∀ t : ℕ, y.budget i ≤ t → ∀ j:Axis,LoudMargin (y.angularPrism j i t) d
  matrix_limits : (∀ᶠ i in atTop, ∀ j:Axis, Tendsto (fun t=> y.angularPrism j i t) atTop (𝓝 (y.page i))) ∧ Tendsto y.page atTop (𝓝 y.finalPage)
  kets :
    (∀ᶠ i in atTop,∀ a:Lead.Clan,let T:=y.spine.sold_birth y.point y.A y.c y.r y.n y.w a i y.handle; let Z':=y.spine.mayIntertwineS y.point 3;
       Tendsto (y.headKet a i) atTop (𝓝 ((Z' (y.spine.thinKet y.point (y.body a i) T (flipDose y.F 3))).val)) ∧
       Tendsto (y.toeKet a i) atTop (𝓝 ((Z' (y.spine.thinKet y.point (y.body a i) T y.U)).val))) ∧
    (∀ a:Lead.Clan, let Z':=y.spine.mayIntertwineS y.point 3;
       Tendsto (fun i=> Z' (y.spine.thinKet y.point (y.body a i) (y.spine.sold_birth y.point y.A y.c y.r y.n y.w a i y.handle) (flipDose y.F 3))) atTop (𝓝 (y.headThin a)) ∧
       Tendsto (fun i=> Z' (y.spine.thinKet y.point (y.body a i) (y.spine.sold_birth y.point y.A y.c y.r y.n y.w a i y.handle) y.U)) atTop (𝓝 (y.toeThin a))) ∧
    ∀ a b, y.finalPage a b=inner ℂ (y.headThin a) (y.toeThin b)

lemma basePrice : Purchase.BasePrice y := by
  constructor
  · exact y.spine.mayEver_stamped y.point y.F y.U y.early y.late y.A y.c y.r y.n y.w y.crew y.g y.h y.handle (trust y).lab
  · exact fun j=> y.spine.mayVictory y.point j ((trust y).exp.ground.2.1.accepted j)
  · exact fun j a b=> ⟨(y.spine.mayContinues y.point j b a).symm,(y.spine.maySpectrum y.point j a).symm⟩
  · filter_upwards [y.spine.mayEver_matrix y.point y.F y.U y.early y.late y.A y.c y.r y.n y.w y.crew y.g y.h y.handle (trust y).lab,(trust y).lab.then_read.comparison] with i u v t h
    exact ⟨fun a=> (trust y).lab.then_read.bothZero a i t h,(v t h).2,u t h⟩
  · obtain ⟨d,u,p,v⟩:= (trust y).loud; refine ⟨d,u,p,?_⟩
    filter_upwards [y.spine.mayEver_matrix y.point y.F y.U y.early y.late y.A y.c y.r y.n y.w y.crew y.g y.h y.handle (trust y).lab,v] with i w t s h j
    unfold angularPrism; rw [(w s h j).1, y.spine.glasshousePrism_eq_azure]; exact t s h
  · refine ⟨?_,(trust y).limits.2⟩
    filter_upwards [y.spine.mayEver_matrix y.point y.F y.U y.early y.late y.A y.c y.r y.n y.w y.crew y.g y.h y.handle (trust y).lab,(trust y).limits.1] with i v h j
    apply h.congr'
    filter_upwards [eventually_ge_atTop (y.budget i)] with t p
    exact ((v t p j).1.trans (y.spine.glasshousePrism_eq_azure ..)).symm
  exact ⟨y.spine.mayMesh_limit y.point y.F y.U y.early y.late y.A y.c y.r y.n y.w y.crew y.g y.h y.handle (trust y).lab, y.spine.mayThin_limit y.point y.F y.U y.A y.c y.r y.n y.w y.crew y.g y.h y.handle (trust y).lab,fun a b=> y.spine.mayThin_matrix y.point y.F y.U y.w y.crew a b 1⟩
end Purchase
#check existsPurchase
#print Purchase.BasePrice
#print axioms existsPurchase
#print axioms Purchase.basePrice
#print axioms mayOrderedOp
#print axioms mayBoth
#print axioms mayProjectionVac
#print axioms mayLeft_project
#print axioms mayFortKetPair
#print axioms mayEver_warm
#print axioms mayIndoor_strongLimit
#print axioms maySector
#print axioms mayPayments
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
