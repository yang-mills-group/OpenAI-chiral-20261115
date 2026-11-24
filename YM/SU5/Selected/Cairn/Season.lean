import YM.SU5.Selected.Cairn.Comete
import YM.SU5.Selected.Cairn.North
import YM.SU5.Selected.Attic.Price
import YM.SU5.Selected.Dais.Seat
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
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
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
open YM.CF.Pannier.Chancel.Lantern
variable (H:Real.exp 1≤ P.x)
open Crest
namespace Convent
local notation "κI" i:max s:max k:max => (gram Y s i k).J.M
local notation "SN" i:max s:max => Papal.count Y s i
open CF.Pannier.Chancel (cows)
open CF.Pannier.Chancel.Attic CF.Pannier.Chancel.Lantern.Alternative
open CF.Pannier.Chancel.Cuve CF.Pannier.Chancel.Attic.Cairn CF.Pannier.Chancel.Attic.Cairn.Giant
open CF.Pannier.Chancel.Attic
open Bulb
open Rail (Maj Rates basisRule mounts)
local notation "K0"=> tent Y H
open Rundle
open Airy (mtn)
variable {A:Giant}{Z:A.Notes→basisRule}{Ω C γ:ℝ}(p:PriceE TipC Ω (crew Y H) A Z C γ) (v : guardFee A≤ P.h)(u:P.d ≤ enter)(q':Scooped P)
variable {T:Type}[Fintype T][DecidableEq T](U:Society T)
local notation "uℓ"=> A.debt.val
local notation "B₀"=> A.sampleW
local notation "Λ"=> coastCap C
local notation "η"=> wageL C
local notation "d₁" => enter
open Tender
open Tapestry Bulb.Commission
open Tower.SlabMark
variable {i' k':ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}
   (V: Universal Y H i' k' I E)
local notation "W"=> U.qu.kin
local notation "μ"=> 2*Real.exp (1-Ω)
local notation "β"=> A.Broad
local notation "P0"=> plow K0 3 1 A.ascX ∪ A.ascX
private lemma lift_box (K: Calibration)(N m:Side)(z:A.block=K.B)(t:N=K.c m){M:Tulip.Male}
    (c:Pride A Z C enter γ M N)(d:A.tokenS<N.val)(u:∀ b,Roomy (A.patio b) N)(h:Roomy (plow K 3 1 A.ascX ∪ A.ascX) N) : ∃ X Y:SpireBook A K W, arrange _ N t.symm ((X.bouquet A K).val m)= (A.lobo Z U false c d).frame ∧ arrange _ N t.symm ((Y.bouquet A K).val m)= (A.lobo Z U true c d).frame ∧ Equatorial A K W X Y := by subst N; exact uFocus A Z U C K c d z u h
variable (s i k:ℕ)(c:Pride A Z C enter γ (gram Y s i k).J.M (Papal.count Y s i))(d:A.tokenS<(Papal.count Y s i).val)(h:Satellite Y U s i k A Z Ω C γ c d)
local notation "G" F:max=> Tower.mirror K0 3 0 F * F
local notation "g" F:max => G ((SpireBook.bouquet A K0 F).val)
local notation "Z0"=> momentm Y i s
include c h d
set_option maxRecDepth 4500 in
lemma price_bf (b:Bool)(F:Buffered.Family K0)(e: arrange _ (SN i s) (terrain Y H (Y.ir i) s) (F Z0)=(A.lobo Z U b c d).frame): ‖Journey.sharp Y H s i k (G F)‖ ≤ μ ∧ ∀ x, ‖((G F) Z0 x)‖≤ η^2:=by
 let M:= A.lobo Z U b c d; let Θ:= (SN i s); let Z':= G F; let P':= exhibit Y H s i; have hu:P' Z'= reflMark 3 0 M.frame *M.frame:= by unfold P' Z'; rw [actual_product,Tower.mirror_time, actual_reflect, show exhibit Y H s i _= _ from (show exhibit Y H s i F=M.frame from e)]
 refine ⟨(by change ‖Journey.sharp Y H s i k Z'‖≤_; rw [actualRead, (show exhibit Y H s i Z'= _ from (hu: P' Z'= _))]; exact h.salutes b),?_⟩
 apply (displayPositive (terrain Y H (Y.ir i) s) (η^ (2:ℕ)) ((G F) Z0)).mpr; intro i; change ‖P' Z' i‖ ≤ _; rw [hu];
 change ‖reflMark 3 0 M.frame i * M.frame i‖ ≤ _; apply le_trans (norm_mul_le ..); rw [show ‖reflMark 3 0 M.frame i‖=_ from (Afterglow.theta_fee ..), sq]; exact mul_le_mul (h.habit b _) (h.habit b _) (norm_nonneg _) ((norm_nonneg _).trans (h.habit b i))
include p
lemma week (e:∀ b,Roomy (A.patio b) (SN i s))(e':Roomy (P0) (SN i s)) : ∃ X Y':A.SpireBook K0 W, Equatorial A K0 W X Y'∧ (‖Journey.sharp Y H s i k (g X)‖ ≤ μ ∧ ∀ x, ‖((g X) Z0 x)‖≤ η^2) ∧ ‖Journey.sharp Y H s i k (g Y')‖ ≤ μ ∧ ∀ x, ‖((g Y') Z0 x)‖≤ η^2:=by
 obtain ⟨F,F',pF,pF',he⟩:= lift_box U K0 (SN i s) Z0 (pass_key Y H p).2 (terrain Y H (Y.ir i) s).symm c d e e'; -- K param order N m. 
 exact ⟨F,F',he,price_bf Y H U s i k c d h false _ pF,price_bf Y H U s i k c d h true _ pF'⟩
omit c d h
include p v u q' U V
local notation "ς"=>3*Real.exp (1-Ω)
lemma koy (hp:0<Ω): ∀ᶠ s in atTop,∃ (F F':SpireBook A K0 W), ‖E s (g F)‖ ≤ ς ∧ ‖E s (g F')‖ ≤ ς ∧ Equatorial A K0 W F F' := by
 have ht:Real.exp (1-Ω) >0:= Real.exp_pos _; let ν:= Real.exp (1-Ω); let r:= (η)^ (2:ℕ); have he: 1≤r:= one_le_pow₀ (Tender.toll_pos (by have h:= Giant.capCost C p.slope; linarith : 0 ≤ coastCap C)); filter_upwards [troupe Y H p v u q' U hp] with s y
 have hx : ∀ᶠ i in atTop, (∀ b:Bool,Roomy (A.patio b) (SN i s))∧ Roomy (P0) (SN i s) := (eventually_all.mpr fun b=>roomyTail Y H s _).and (roomyTail Y H s _)
 let L:= V.pick.grow_i.tendsto_atTop; obtain ⟨i,⟨hs,e⟩,t⟩:= (((L.eventually y).and (L.eventually hx)).and (Council.total_precision Y H s V (β ∪ Tower.reflectedBox 3 0 β) ν r ht (by linarith))).exists
 obtain ⟨k,⟨c,d,h⟩,f⟩:= ((V.pick.grow_k.tendsto_atTop.eventually hs).and (cadence Y k' V.pick.grow_k (i' i))).exists
 obtain ⟨F,F',he,x,x',z'⟩:= week Y H p U s (i' i) (k' k) c d h e.1 e.2
 let σ:= Journey.sharp Y H s (i' i) (k' k); have hz(F:SpireBook A K0 W)(h:‖σ (g F)‖ ≤ (μ))(l:∀ x, ‖(g F) (momentm Y (i' i) s) x‖ ≤ r): ‖E s (g F)‖ ≤ ς:=by
    let Y₀:= g F; have hc:= t k f _ (Mileage.Delay.reflective K0 β _ (Commission.blush (F.bouquet A K0)).widen) l; have hc : ‖σ Y₀-E s Y₀‖≤ν:= hc; unfold ν at hc; change ‖σ Y₀‖ ≤_ at h
    change ‖E s Y₀‖ ≤ _; refine (norm_le_norm_sub_add _ (σ Y₀)).trans ?_; rw [norm_sub_rev]; linarith only [h,hc]
 exact ⟨F,F',hz F x.1 x.2,hz F' x' z',he⟩
omit U
lemma stellar (hp:0<Ω): ∀ᶠ s in atTop,∀ T:Window.Family,∃ (F F':SpireBook A K0 T), ‖E s (g F)‖ ≤ ς ∧ ‖E s (g F')‖ ≤ ς ∧ Equatorial A K0 T F F':=by
 apply eventually_all.mpr; intro a; obtain ⟨T,u',v',W',rfl⟩:=Society.families a; letI:= u'; letI:=v'; exact koy Y H p v u q' W' V hp -- W conflicts
end Convent
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.Convent
#print axioms stellar
#print axioms price_bf
#print axioms lift_box
#check @stellar
