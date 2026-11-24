import YM.SU5.Selected.Cor.Pent
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
namespace Mileage
local notation "κI" i:max s:max k:max => (gram Y s i k).J.M
local notation "SN" i:max s:max => Papal.count Y s i
open Bulb Bulb.Mezz
open Airy (Coast Wq)
open CF.Pannier.Chancel.Lantern (Station)
open CF.Pannier.Chancel.Lantern.Tender
open Afterglow.Tapestry
open Bulb.Commission
local notation "K"=> tent Y H
variable {A:Mezz}{C Ω:ℝ}{w:ℕ}{X Z:Coast→ Wq A.marks} {R:ℝ}
local notation "τ₀"=> billR C
variable {d:Type}[Fintype d][DecidableEq d](U:Society d)(s i k:ℕ)
variable {b g:ℕ}{ε E₀:ℝ}(t:Delay Y H b g ε Ω C E₀ A w X Z)
variable {i' k':ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}
   (V: Universal Y H i' k' I E)
local notation "W'"=> U.qu.kin
local notation "μ"=> 2*Real.exp (1-Ω)
local notation "β"=> A.Broad
local notation "η"=> t.stationed Y H
open Tapestry
private lemma airB{T:Mezz}(K':Calibration)(U':Society d)(X Z:Coast→ Wq T.marks)(C':ℝ)(p:T.Legate)(m N:Side){M:Tulip.Male}(v: T.Caste (N:=N) M C' (tightH T.D (Mezz.billR C')) w X Z)(h:K'.c m=N)(g:∀ b (i:T.Lot),Roomy (T.yard i.1 b) N) : ∃ F:Sermon T K' U'.qu.kin, arrange _ N h ((F.solitude T K' p).val m)=(T.triumph U' X Z C' v).frame:=by
 subst N; obtain ⟨F,l⟩:= blast T U' X Z C' K' m v g; exact ⟨F,l⟩
local notation "Λ" F:max=> (Mezz.Sermon.solitude A K (η) F).val
local notation "α₀" F:max=> (Journey.sharp Y H s i k F)
local notation "Kc"=> momentm Y i s
local notation "K₀"=> (SN i s)
local notation "J" => CF.Pannier.Chancel.Lantern.Station.tollK (dueW τ₀)
local notation "vS" => ((CF.Pannier.Chancel.Lantern.Station.tollK (dueW τ₀)) ^ A.vowP)
-- square precision. strength along Lane of one selected F across s. expose on elected jTail i,k. output via Scope craft for χ later.
namespace Delay
variable (c:A.Caste (N:=Papal.count Y s i) (gram Y s i k).J.M C (tightH A.D (billR C)) w X Z)(hp: Luster Y U s i k Ω C A w X Z c)
local notation "α₁" F:max => (Tower.mirror (K) 3 0 F*F) -- use K const outside variable
include t c hp
lemma opportune (e:∀ b (j:A.Lot),Roomy (A.yard j.1 b) (SN i s)) : ∃ F:Sermon A K W', ‖Journey.sharp Y H s i k (α₁ (Λ F))‖ ≤ (μ) ∧ ∀ x, ‖(α₁ (Λ F)) (Kc) x‖ ≤ (vS)^ (2:ℕ):=by
 obtain ⟨F,hF⟩:= airB (K) U X Z C (η) (Kc) (SN i s) c (terrain Y H (Y.ir i) s) e
 let M:= A.triumph U X Z C c; let x:=(Λ F); let Θ:= (SN i s); let Z':= α₁ x; let P':= exhibit Y H s i; have hu:P' Z'= reflMark 3 0 M.frame *M.frame:= by unfold P' Z'; rw [actual_product,Tower.mirror_time, actual_reflect, show exhibit Y H s i _= _ from (show exhibit Y H s i x=M.frame from hF)] -- rw tune
 refine ⟨F,(by change ‖Journey.sharp Y H s i k Z'‖ ≤ _; rw [actualRead, (show exhibit Y H s i Z'= _ from (hu : P' Z'= _))]; exact hp.price),?_⟩
 apply (displayPositive (terrain Y H (Y.ir i) s) ((vS)^(2:ℕ)) ((α₁ x) (Kc))).mpr; intro i; change ‖P' Z' i‖ ≤ _; rw [hu]; -- may need fold Z'
 change ‖reflMark 3 0 M.frame i * M.frame i‖ ≤ _; apply le_trans (norm_mul_le ..); rw [show ‖reflMark 3 0 M.frame i‖=_ from (Afterglow.theta_fee ..), sq]; exact mul_le_mul (hp.quote _) (hp.quote _) (norm_nonneg _) ((norm_nonneg _).trans (hp.quote i)) -- param `eq P'.`
omit t c hp
lemma reflective (Ax: Calibration) (S:Finset Cover) (F:Buffered.Family Ax)(p:InTest Ax true S false F) : InTest Ax true (S∪Tower.reflectedBox 3 0 S) false (Tower.mirror Ax 3 0 F* F):= InTest.mul ((Tower.axial Ax 3 0 p).mono subset_union_right) (p.mono subset_union_left) -- local notation Ax conflict!
include t V U
lemma covers : ∀ᶠ s in atTop,∃ (F:Sermon A K U.qu.kin), ‖E s (α₁ (Λ F))‖ ≤ 3*Real.exp (1-Ω) := by
 have ht:Real.exp (1-Ω) >0:= Real.exp_pos _; let ν:= Real.exp (1-Ω); let r:= (vS)^ (2:ℕ); have he: 1≤r:=one_le_pow₀ (one_le_pow₀ (Tender.toll_pos (by have hp:= t.seed.price; change 0≤10000*C^ (4:ℕ); positivity))); filter_upwards [t.whips Y H U] with s x
 have hx : ∀ᶠ i in atTop, ∀ b (j:A.Lot),Roomy (A.yard j.1 b) (SN i s):= eventually_all.mpr fun b=>eventually_all.mpr fun j=>roomyTail Y H s _ -- Window event bool
 let L:= V.pick.grow_i.tendsto_atTop; obtain ⟨i,⟨hs,e⟩,v⟩:= (((L.eventually x).and (L.eventually hx)).and (Council.total_precision Y H s V (β ∪ Tower.reflectedBox 3 0 β) ν r ht (by linarith))).exists
 obtain ⟨k,⟨c,h⟩,f⟩:= ((V.pick.grow_k.tendsto_atTop.eventually hs).and (cadence Y k' V.pick.grow_k (i' i))).exists
 obtain ⟨F,p,x'⟩:= opportune Y H U s (i' i) (k' k) t c h e; let Y₀:= α₁ (Λ F)
 refine ⟨F,?_⟩; have hc:= v k f _ (reflective (K) β (Λ F) (blush (F.solitude A K (η))).widen) x' -- syntax
 change ‖E s Y₀‖ ≤ _; let σ:= Journey.sharp Y H s (i' i) (k' k);
 have hc : ‖σ Y₀-E s Y₀‖≤ν:= hc; change ‖σ Y₀‖ ≤_ at p; refine (norm_le_norm_sub_add _ (σ Y₀)).trans ?_; rw [norm_sub_rev]; unfold ν at hc; linarith only [p,hc]
omit U
lemma tallyD : ∀ᶠ s in atTop,∀ W: Window.Family, ∃ (F:Sermon A K W), ‖E s (α₁ (Λ F))‖ ≤ 3*Real.exp (1-Ω) := by
 apply eventually_all.mpr; intro W; obtain ⟨T,u,v,Q,rfl⟩:= Society.families W; letI:= u; letI:= v; exact covers Y H Q t V
end Delay
end Mileage
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.Mileage
#print axioms Delay.tallyD
#print axioms Delay.opportune
