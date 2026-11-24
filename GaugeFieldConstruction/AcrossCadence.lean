import GaugeFieldConstruction.AcrossBreather
import YM.SU5.FiniteGaugeData.LocalLimit.Voyage

/-!
# Concurrent credentialed visits. Every mask & period (Launch) and also
infinite same-wavelength shifted shots on each spare depth.
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2600
set_option maxHeartbeats 450000
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew

namespace LocalLimit.Preparation
open AcrossShots AcrossLands
variable {P:Preparation} {F:(n:Side)→Scree.Loom n→Prop} (Y:Course P F)

namespace Course
variable (i k : ℕ)
set_option quotPrecheck false
local notation "Σ" => (Y.voyage i).X k
local notation "Ω"=> mid (mesh (Y.ir i) P.R.L k) P.block
local notation "Ψ"=> P.P

abbrev capFunds (b:ℝ):=sharpHat (mesh (Y.ir i) P.R.L k) P.U (Y.meter.a k) b
abbrev capPayment (b:ℝ):=sharpWeight (mesh (Y.ir i) P.R.L k) P.U (Y.meter.a k) b
abbrev headIn := (((Y.voyage i).X k).gram k).beta
lemma headRates : entersReal (hat P.R.L P.x k) (Y.headIn i k):=by
 let h:= (Y.voyage i).paths k; obtain ⟨b,t,e,q⟩:=h.issued; unfold headIn; rw [e]; exact (h.paid.beta_ok P.H t.toRealQ k le_rfl).1
lemma headBounds : hat P.R.L P.x k / 2 ≤ Y.headIn i k ∧ Y.headIn i k ≤2* hat P.R.L P.x k:= by
 obtain ⟨h,u⟩:= Y.headRates i k; have he:= (Y.oneP.trans (Vale.crown P.R.L P.x k)); constructor <;> linarith
lemma headCost : 0<Y.headIn i k:= by linarith [(Y.headBounds i k).1, Y.oneP, Vale.crown P.R.L P.x k]
lemma appears {m:ℕ}{b:ℝ} (p:CompleteMask (p:=Y.meter.a k) P.J m b)(s:∃ c:Side, Y.ir i=c*P.M ∧ m≤c.val) : Envelope (Y.capFunds i k b) ∧ Y.capPayment i k b≠0:= by
 unfold capFunds capPayment; obtain ⟨c,g,h⟩:=s; rw [g,Month.ruler]; exact p.cashM _ (h.trans (mesh_ge ..))
def permitLand (n:ℕ):Prop:= ∃ c:Side,mesh (Y.ir i) P.R.L k=c*P.M ∧ n≤ c.val
lemma marketOpen {u:ℝ}{t:ℕ}(p:Y.permitLand i k t)(g:CompleteMask (p:=Y.meter.a k) P.J t u): Envelope (Y.capFunds i k u) ∧ Y.capPayment i k u≠0:=by
 obtain ⟨c,e,c'⟩:=p; unfold capFunds capPayment; rw [e]; exact g.cashM _ c'
lemma givenLand {n:ℕ} (v:n≤k): ∀ i:ℕ,Y.permitLand i k n:=by
 intro i; obtain ⟨c,e,h⟩:=(Y.lease i).1; unfold permitLand; rw [show Y.ir i=c*P.M from e,Month.ruler]; refine ⟨mesh c P.R.L k,rfl,?_⟩
 exact v.trans ((Vale.huge P.R.L (by have hp:= P.V.tallX; omega) k).trans (Nat.le_mul_of_pos_left _ c.property))

abbrev eligible (b ε:ℝ):=∃ τ:ℝ,|τ|≤ε ∧ CanonicalAt (Y.voyage i).funds (Y.voyage i).CapeT P.P k (gaugeFreq P (Y.tile*P.M)) b τ
lemma ready_mask (ε β:ℝ) (p:0<ε)(u:ε<Rx P.x)(hv:|β-Y.headIn i k| ≤ ε/2)(t:Y.capPayment i k β≠0) : Y.eligible i k β ε:=by
 let h:= (Y.voyage i).paths k; obtain ⟨b,e,v,g⟩:=h.issued
 apply moves_top _ P.H P.height P.direct h.paid e p u _ t; unfold headIn at hv; rw [v] at hv; exact hv

set_option quotPrecheck false
local notation "Θ2"=> gaugeFreq P (Y.tile*P.M)
abbrev owedTape (b ε d:ℝ):Prop:= ∃ t:ℝ, |t|≤ε ∧ ∃ r:Bet k, EarnTrunkSt (Y.voyage i).funds (P:=P.P) (J:=P.J) (f:=gaugeFreq P (Y.tile*P.M)) (X:=(Y.voyage i).CapeT) (h:=P.h) (q:=Chi.canonical) (D:=P.δ) (C:=P.C) (R0:=P.R0) ((Σ).gram) ((Σ).wave) t b d r
lemma readyTrunk (ε d:ℝ)(e:0<ε)(u:0<d)(h:Y.capPayment i k (Y.headIn i k)≠0) : ∃ t>0,∀ v:ℝ,|v-Y.headIn i k|≤t → Y.capPayment i k v≠0 → owedTape Y i k v ε d:=by
 let p:= (Y.voyage i).paths k; obtain ⟨μ,s,eμ,vμ⟩:= p.issued
 let x:= Actual Y.meter (Y.voyage i).funds (Y.voyage i).CapeT (Θ2) k; have he:(μ.read k).re=Y.headIn i k:=by unfold headIn; rw [eμ]
 let q:= tipBalance _ P.H P.height P.direct p.paid s he h
 obtain ⟨t,a,r⟩:=joint_visit _ P.H P.height P.direct p.paid P.response s (hx:=fun t g=>(q.2.2.2.2 t g).2.2.2.1) ε d e u
 refine ⟨t,a,fun v e u=>?_⟩; unfold owedTape; rw [eμ,vμ]; exact r v (by change |v-(μ.read k).re|≤_; rwa [he]) u
lemma late_volume (n:ℕ) : ∀ᶠ i:ℕ in atTop, ∃ c: Side,Y.ir i=c*P.M ∧ n≤c.val:=by
 filter_upwards [Y.ir_grows.tendsto_atTop.eventually_ge_atTop (n*P.M.val)] with i p
 obtain ⟨c,v,h⟩:=(Y.lease i).1; have e:Y.ir i=c*P.M:=v; refine ⟨c,e,le_of_mul_le_mul_right ?_ P.M.property⟩; rw [show c.val*_= _ from congrArg Subtype.val e.symm]; exact p
lemma common_places {n:ℕ} (Λ:Territory P.K P.J n)(ε:ℝ)(p:0<ε)(u:ε<Rx P.x):∃ β:ℝ, 0<β ∧ CompleteMask (p:=Y.meter.a k) P.J n β ∧ (∃ᶠ i in atTop,Y.eligible i k β ε):=by
 obtain ⟨b,h,f,hf,t⟩:= (isCompact_Icc (a:=hat P.R.L P.x k/2) (b:=2*hat P.R.L P.x k)).tendsto_subseq (fun i:ℕ=> (Y.headBounds i k))
 have hz':= (((Y.voyage 0).paths k).paid.can.pole k)
 have hb:0<b:= (show 0<hat P.R.L P.x k/2 by linarith [Y.oneP, Vale.crown P.R.L P.x k]).trans_le h.1
 obtain ⟨β,x,y,e⟩:= choose_paying P.direct Λ (Y.meter.a k) hz' (show b < b+ε/4 by linarith)
 refine ⟨β,hb.trans x,e,hf.tendsto_atTop.frequently ?_⟩
 have ht': |β-b|<ε/4:= abs_lt.mpr ⟨by linarith,by linarith⟩
 refine Eventually.frequently (Eventually.mp (hf.tendsto_atTop.eventually (Y.late_volume n)) (((Metric.tendsto_nhds.mp t) _ (show 0<ε/4 by positivity)).mono ?_)); intro i g s
 change dist (Y.headIn (f i) k) b < ε/4 at g
 exact Y.ready_mask _ _ _ _ p u (by linarith [show |b-Y.headIn (f i) k|<ε/4 from (by rwa [dist_comm,Real.dist_eq] at g),abs_sub_le β b (Y.headIn (f i) k)]) (Y.appears _ _ e s).2
#print axioms common_places
#print axioms readyTrunk
end Course
end LocalLimit.Preparation
end YM.CF.Py.Rate
end
