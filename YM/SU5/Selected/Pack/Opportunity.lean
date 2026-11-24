import YM.SU5.Selected.Pack.FamilyPrint

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

variable (C Z Ω':ℝ)(p:Choir Y H q d w C Z Ω') {a' b:ℕ→ℕ}
  {I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}
  (V:Universal Y H a' b I E)
local notation "A*" => (payout d q w)
local notation "bM" => camp (payout d q w)
local notation "S" => Sen (camp (payout d q w)) (payout d q w)
local notation "F" x:max j:max => pledgeVolume Y H x j
local notation "σ" i:max s:max k:max => Journey.sharp Y H s i k

include V in
lemma total_precision (S':Finset Cover)(δ R:ℝ)(u:0<δ)(h:0<R) :
    ∀ᶠ i in atTop,∀ k:ℕ, legacy Y (a' i) (b k) →
      ∀ x:Buffered.Family K, InTest K true S' false x→
      (∀ y, ‖x (momentm Y (a' i) s) y‖≤ R) → ‖(σ (a' i) s (b k)) x-E s x‖ ≤ δ := by
 let f:= δ/R; have hf:0<f:= div_pos u h
 filter_upwards [(Satin.boutique Y H V S' s).2 f hf,(V.pick.grow_i.tendsto_atTop.eventually (roomyTail Y H s S'))] with i k e
 intro k' ε x t p
 let hx:Hosp S' ((K).c (momentm Y (a' i) s)):= (terrain Y H (Y.ir (a' i)) s).symm ▸ Roomy.seats e
 exact ((k x t _ hx R p).2 _ ε).trans_eq (div_mul_cancel₀ _ h.ne')
include V p
lemma glimpses (j:Axis) : ∀ᶠ s in atTop, ∀ z: SU.Slot, ∃ (F':Buffered.Family K), F'∈ Filigree K (Window.family z) (booty bM d q) S ∧ Neutral K F' ∧ 1/4 ≤ ‖E s F'‖ ∧ ‖E s (F F' j)‖ ≤3*Real.exp (1-Ω') := by
 let X:=S; let Y₀:= S∪Tower.reflectedBox j 0 S
 let c:= C+1; let v:= Real.exp (1-Ω')
 have hc: 0<c:= add_pos p.corn.heap one_pos ; have h:0≤c:= hc.le
 filter_upwards [p.corn.here,p.Cena] with s u rG
 let M := V.pick.grow_i.tendsto_atTop; let R := V.pick.grow_k.tendsto_atTop; obtain ⟨i,⟨⟨hs,e⟩,r'⟩,fG⟩:= ((((M.eventually (u bM)).and (total_precision Y H s V X (1/4) c (by norm_num) hc)).and (M.eventually rG)).and (total_precision Y H s V Y₀ v ((1+c)^2) (Real.exp_pos _) (by positivity))).exists -- nested pattern tune
 obtain ⟨k,⟨t,y⟩,β⟩:= (((R.eventually hs).and (R.eventually r')).and (cadence Y b V.pick.grow_k (a' i))).exists
 intro z; let i':= a' i; let k':= b k
 have hu:= t z; have hn:= y z
 obtain ⟨-,p',_,_,_,g,F₀,f,ht,he,wR⟩:= t z
 have x':= (FilTest f).widen
 let m:=momentm Y i' s
 have W(x): ‖F₀ m x‖ ≤ c:= by
    have hp : ∀y, ‖F₀ m y‖ ≤ c:= (displayPositive (terrain Y H (Y.ir i') s) c _).mpr (fun x=>by rw [show arrange _ _ (terrain Y H (Y.ir i') s) (F₀ m)= _ from he]; exact g x)
    exact hp x
 have V':= e k β F₀ x' W
 refine ⟨F₀,f,ht,?_,?_⟩
 · exact le_trans (by linarith only [wR] : 1/4 ≤ ‖(σ i' s k') F₀‖-1/4) (by change ‖(σ i' s k') F₀‖-_ ≤ ‖E s F₀‖; change ‖(σ i' s k') F₀-E s F₀‖ ≤ _ at V'; linarith only [V', norm_sub_norm_le ((σ i' s k') F₀) (E s F₀)])
 let t:= F F₀ j
 have a: ‖(σ i' s k') t - E s t‖ ≤ v := fG k β t (pledge_test Y H F₀ j S x') (pledge_cost Y H s i' F₀ j h W)
 have hv: ‖(σ i' s k') t‖ ≤ 2*v:= at_voucher Y H s i' k' z F₀ j hu (from_width K p.small) hn.1 (hn.2 _) he
 change ‖E s t‖≤ 3*v; exact (norm_le_norm_sub_add (E s t) ((σ i' s k') t)).trans (by rw [norm_sub_rev]; linarith only [a,hv]) -- `rw` rev maybe rewrites all
end Council
end Papal
end LocalLimit
end Rate
end YM.CF.Py
