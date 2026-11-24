import YM.SU5.May.GraphPrice
import SatinGlasshouseFixedProbesNovember6
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
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
/-!
# The CP1 payments packaged for the selected experiment, and reading its
actual measurement programme with those credits (always on the character
used with P.large; Gram, strips, support, and physical hinge included).
The outstanding Mink registration obligation stated using the new interface
in May application does NOT follow from this CP1 theorem.
-/
variable (F U: SampleDose)(D : P.MayBooth F reviewEarlierBox)(E : P.MayBooth U reviewLaterBox)
open MacroGrid SatinNucleus SatinJets DoseTravel
variable (A:ℕ → P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)
-- named marks. They are literally the markings of `exists_disclosed_satin_native_contrast`.
local notation "W" => P.soldTrumpet A c r n w
local notation "Φ" a:max i:max t:max => P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F
local notation "Λ" a:max i:max t:max => P.prepared t ((P.soldTrumpet A c r n w) a i) U
variable (v : ∀ j:Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
variable (g h:ℕ)(T:P.HandleWith x c r A n)
local notation "Δ" => P.mayGap j F U D E
local notation "dℝ" => Real.toNNReal ((P.mayGap j F U D E):ℝ)
variable (a b:Lead.Clan)(i t:ℕ)
local notation "p" t:max=> P.singleState 3 t x
variable {D₀ : Doorway} {F₀: SampleDose}
open DoseTravel
section chord
variable (B:P.MayBooth F₀ D₀)
-- Panel props, to feed Registered. No warning about `q=Bool` needed, insist true
structure MayChord (f:P.Test) (X:(P.mayHil x j).Op) : Prop where
  prints : f∈ FirstWindows.insideAt P.par P.width P.calibration true B.box.sealing t
  pays : Chambers.Follows Y L V G j (C j) χ (mv (ej (-B.low j)) ((tk t) f)) (B.width j) X
  stamp : mv (ej (- B.low j)) ((tk t) f) ∈ D' true (P.panelShift j (- B.low j) B.box.sealing)
  tracks : (p t) f = inner ℂ Ω (X Ω) ∧ (p t) f = inner ℂ Ω' ((Z X) Ω')

def mayScript (f:P.Test) : (I₀).Op := if h:f∈ FirstWindows.insideAt P.par P.width P.calibration true B.box.sealing t
    then P.mayOperator x j B (ticket_mem Y L G h) else 0
lemma mayMakes (f:P.Test) (q:f∈ FirstWindows.insideAt P.par P.width P.calibration true B.box.sealing t):
    P.MayChord x j t B f (P.mayScript x j t B f):= by
  unfold mayScript; rw [dif_pos q]; have h:=P.mayGraph x j B (ticket_mem Y L G q); let X:=P.mayOperator x j B (ticket_mem Y L G q)
  have he: (p t) f = inner ℂ Ω (X Ω):= Eq.trans (P.mayTicketReads x j t f (ticket_loose ..)).symm (P.mayGraphReads x j h (ticket_loose ..))
  exact ⟨q,h, P.boothStamps j B (ticket_mem Y L G q), he, he.trans (P.mayRemembers x j X)⟩
end chord

abbrev mayHead := P.mayScript x j t D (Φ a i t)
abbrev mayToe := P.mayScript x j t E (Λ a i t)
local notation "a₀" a:max i:max t:max => P.mayHead x j F D A c r n w a i t
local notation "a₁" b:max i:max t:max => P.mayToe x j U E A c r n w b i t
local notation "B₀" => a₀ a i t
local notation "B₁" => a₁ b i t
local notation "Uₓ" k:max=> P.mayIntertwine x k
local notation "Ωt" k:max=> Selected.doorstep Y L V H H₁ k false (C k) (P.mayChar x k)
local notation "H₀" k:max=> Selected.ride Y L V H H₁ k false (C k) (P.mayChar x k)
local notation "χ'" t:max=> P.thinSplit x t

def fortPrism : CrossRead := Matrix.of fun a b : Lead.Clan => inner ℂ Ω' ((Z (a₀ a i t)) ((R).E dℝ ((Z (a₁ b i t)) Ω')))
lemma mayBoth (u : P.MayChord x j t D (Φ a i t) (B₀)) (z:P.MayChord x j t E (Λ b i t) (B₁)) :
    let X:= (tk t) (Φ a i t)
    let y:= (tk t) (Λ b i t)
    X*y=(tk t) ((Φ a i t)*(Λ b i t)) ∧ X*y∈ Domain Y L G true (D.box.sealing∪E.box.sealing) ∧
    Chambers.Follows Y L V G j (C j) χ (mv (ej (-D.low j)) (X*y)) (E.high j-D.low j)
      ((B₀) * (Hr).E dℝ * (B₁)) ∧
    (p t) ((Φ a i t)*(Λ b i t))=P.fortPrism x j F U D E A c r n w i t a b ∧
    P.fortPrism x j F U D E A c r n w i t a b = inner ℂ Ω ((B₀) ((Hr).E dℝ ((B₁) Ω))) := by
  intro X y; have v:= ticket_mem Y L G u.prints; have q:= ticket_mem Y L G z.prints
  have hh:X*y=(tk t) ((Φ a i t)*(Λ b i t)) := (ticket_separated Y L G u.prints z.prints (P.booths_disjoint F U D E)).symm
  have hw : X*y∈ Domain Y L G true (D.box.sealing∪E.box.sealing) := domain_mult Y L G v q (P.booths_disjoint F U D E)
  have hp:= P.mayOrderedOp x j F U D E u.pays z.pays
  let m := domain_le_lawDomain Y L G _ hw
  have hj : (p t) ((Φ a i t)*(Λ b i t))= Ψ ⟨X*y,m⟩ := by convert (P.mayTicketReads x j t ((Φ a i t)*(Λ b i t)) (ticket_loose ..)).symm using 1 <;> apply congrArg Ψ; exact Subtype.ext hh
  have he : Ψ ⟨X*y,m⟩=P.fortPrism x j F U D E A c r n w i t a b:= (DFunLike.congr_fun
    (os_across Y L V G 3 (C 3) α j (C j)) _).trans
    (P.mayPair x j F U D E (domain_loose Y L G _ v) (domain_loose Y L G _ q) u.pays z.pays m)
  exact ⟨hh,hw,hp,hj.trans he,he.symm.trans (P.mayGraphReads x j hp m)⟩
section bought
variable {K':P.Register} {μ:ℝ} {s k:ℕ}
variable (Z' : P.FullPrismLab x A c r n w v g h T μ F U reviewEarlierBox reviewLaterBox s k K')
local notation "t!" i:max=> c (n i)
include Z'
lemma mayEver_stamped : ∀ᶠ i:ℕ in atTop, ∀ t:ℕ, t! i ≤ t → ∀ (j:Axis)(a:Lead.Clan),
    let X:= P.mayHead x j F D A c r n w a i t; let Y':= P.mayToe x j U E A c r n w a i t
    P.MayChord x j t D (Φ a i t) X ∧ P.MayChord x j t E (Λ a i t) Y':= by
  filter_upwards [P.fullPrism_admitted x F U D E A c r n w v g h T Z'] with i u t e j a
  exact ⟨P.mayMakes x j t D _ (u t e a).1,P.mayMakes x j t E _ (u t e a).2⟩
lemma mayEver_matrix : ∀ᶠ i:ℕ in atTop,∀ t:ℕ, t! i ≤ t →∀ j:Axis,
    P.fortPrism x j F U D E A c r n w i t=P.glasshousePrism x A c r n w F U i t ∧
    P.fortPrism x j F U D E A c r n w i t= P.reportPrism A c r n w F U i t (p t) - P.reportPrism A c r n w F U i t (χ' t):= by
  filter_upwards [P.mayEver_stamped x F U D E A c r n w v g h T Z', P.fullPrism_azure_comparison x A c r n w v g h T F U Z'] with i q l t e j
  rw [P.glasshousePrism_eq_azure, ← l t e,and_self, P.fullPrism_azure_actual x A c r n w v g h T F U Z' i t e]
  ext1 a b
  exact ((P.mayBoth x j F U D E A c r n w a b i t (q t e j a).1 (q t e j b).2).2.2.2.1).symm
end bought
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
