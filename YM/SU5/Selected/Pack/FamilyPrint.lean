import YM.SU5.Selected.Pack.Procure
import YM.SU5.Selected.Pack.Crisp

/-! # Retain price for a pair of marks in sharp with all observation tolerances.
Full `V` for mixed_law on this Course. No uniform UV in all periods required.
Selecting avatars for variance comes after this step. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
open Satin Tapestry
open Lifted (nodeC node_of)

namespace Council
open CF.Pannier.Chancel.Survival

-- now ANY same Voucher & our upper price produce neutral pair bound at sharp
local notation "K" => tent Y H
variable (s i k:ℕ)
local notation "Ω" => Papal.count Y s i
local notation "r" => Journey.compass Y i k s

include H in
lemma molten_stamp (F:Mark Ω) (u:Continuous F) (S:Finset Cover) (p:Roomy S Ω) (t: AtSupport false (Satin.region S Ω) F)
    (j:Axis) (L: Disjoint (hyphen j 0 (Satin.region S Ω)) (Satin.region S Ω)) (e: Tapestry.Pay Y s i k) :
    r (reflMark j 0 (molasses F)*molasses F)= r (reflMark j 0 F*F) := by
 refine lawful_both j u r (fun g h=>?_) (fun g l=>?_)
 · exact course_boil g h _ ((Y.voyage i).ownership s).paid.bill _ (Marks.can_read _ _ _ _ (Y.each_level i k s e.1 e.2)) _
 obtain ⟨a,t'⟩:= separated_harmony j K S (momentm Y i s) (terrain Y H (Y.ir i) s).symm p t L g l
 exact (trueHarmony Y s i k e a t').symm

variable (z:SU.Slot)(x:Buffered.Family (tent Y H))
local notation "B" => payout d q w
local notation "U" => camp (payout d q w)
local notation "S" => Sen (camp (payout d q w)) (payout d q w)
local notation "σ" => Journey.sharp Y H s i k
local notation "Z" => taggin Y s i k q d w (camp (payout d q w)) z

def pledgeVolume (x:Buffered.Family K)(j: Axis) := (Afterglow.Tower.mirror K j 0 (1+x)) * (1+x) -- order use
local notation "f" x:max j:max=> pledgeVolume Y H x j
lemma pledge_test (j : Axis) (S' : Finset Cover)(p:InTest K true S' false x) : InTest K true (S'∪Tower.reflectedBox j 0 S') false (f x j) := by
 let hv := InTest.one.add p
 exact ((Tower.axial K j 0 hv).mono subset_union_right).mul (hv.mono subset_union_left)
lemma tag_frame (p: Voucher Y H q d w κ (camp (payout d q w)) s i k z) :
    AtSupport false (Satin.region (S) Ω) ((Z).frame) := by
 obtain ⟨_,_,⟨γ,_,h⟩,_⟩:= p
 have e : Satin.region S Ω=(Z).broad:=(sen_islet ..).symm
 rw [e]; exact h.atCost

include H
lemma at_voucher {L:ℝ} (j:Axis)(e:Voucher Y H q d w κ (camp (payout d q w)) s i k z)
    (p: (K).ℓ≤ B)(n:6*(payout d q w)+1≤ (Ω).val)
    (l: ‖Journey.compass Y i k s (reflMark j 0 (taggin Y s i k q d w (camp (payout d q w)) z).frame*(Z).frame)‖ ≤ L)
    (t : exhibit Y H s i x=aliquot Y s i k q d w (camp (payout d q w)) z) :
    ‖σ (f x j)‖ ≤ L := by
 let R:= Z
 have hu : Continuous R.frame:= feastReady ..
 have ht: Roomy S Ω:= e.1 -- red
 have he:AtSupport false (Satin.region S Ω) R.frame:= tag_frame Y H s i k z e
 have hg: Disjoint (hyphen j 0 (Satin.region S Ω)) (Satin.region S Ω):= (show Islet Ω U B = Satin.region S Ω from sen_islet ..) ▸ unmix K j p n
 have h: exhibit Y H s i (1+x)=molasses R.frame:=by rw [actual_add,t,actual_one]; exact add_sugar hu
 have hx:exhibit Y H s i (Tower.mirror K j 0 (1+x))=reflMark j 0 (exhibit Y H s i (1+x)):= displayRef .. -- tune implicit
 have hr: r (reflMark j 0 (molasses R.frame)*molasses R.frame)=r (reflMark j 0 R.frame*R.frame):= molten_stamp Y H s i k R.frame hu S ht he j hg e.2.1
 unfold pledgeVolume; rw [actualRead, actual_product, hx,h]; exact (congrArg (fun x:ℂ=> ‖x‖) hr).trans_le l
-- cost of brother at ANY plane in native torus
local notation "M" => momentm Y i s
local notation "uN" => (K).c (momentm Y i s)
private lemma balm {C:ℝ}(t:∀ y, ‖x M y‖ ≤ C)(g: Fields uN): ‖(1+x) M g‖ ≤ 1+C:= (norm_add_le _ _).trans (add_le_add (le_of_eq (by change ‖(1:FC _)‖=1; exact norm_one)) (t _))
omit H in
private lemma lotion (K':Buffered.Calibration) {m:Side} (j:Axis)(x:Buffered.Family K')(y) : ‖(Tower.mirror K' j 0 x) m y‖= ‖x m (reflFields j 0 y)‖ :=by
 exact Afterglow.theta_fee .. /- or nn -/ -- tune
lemma pledge_cost (j:Axis){C:ℝ}(p:0≤C)(t:∀ y, ‖x M y‖ ≤ C)(g: Fields uN) : ‖(f x j) M g‖≤ (1+C)^2:=by
 refine (norm_mul_le ((Tower.mirror K j 0 (1+x)) M g) ((1+x) M g)).trans ?_; rw [sq,lotion]; exact mul_le_mul (balm Y H s i x t _) (balm Y H s i x t _) (norm_nonneg _) (by linarith) -- include t tune
end Council
end Papal
end LocalLimit
end Rate
end YM.CF.Py
