import YM.SU5.Intrinsic.Rate.Bills
import SatinThinFund

/-
# Apply the new price at all actual internal heights S, with all
path torus qualifications, before going to the endpoint poses.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
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
/-!
# Exact headroom asymptotic, all periods on the signed law.
 Not absolute values on the integrands. Comes from transporting the weights/norms of ZERO
 insertions; this still only pays downstream with further *matching upper* bounds.
-/
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
local notation "ℒ"=> Λ.R.L
local notation "v'" i:max s:max=> sites (Λ.Ctor (Y.ir i) s)
local notation "X₀" i:max k:max=> (Y.voyage i).X (Y.uv k)

abbrev ActualRate (Λ:Preparation) : Prop := WithReceipt Λ.J Chi.canonical Λ.N0
  (WithRate124 Λ.J Chi.canonical Λ.h) Λ.P

open Beau Ione
#print SupportRate
lemma full_rate (t:ActualRate Λ) : ∀ᶠ s in atTop, ∀ i k:ℕ,s<Y.uv k →
 let F:= ((X₀ i k).gram s)
 SupportRate (detectorBudget F.p) (head_L F.F) Λ.h (peripheryCost Λ.R.L (hat Λ.R.L Λ.x s)) :=by
 filter_upwards [(turnover Λ).eventually t] with s q i k u
 intro F; let A:=Y.voyage i; let G:= (X₀ i k)
 obtain ⟨b,hb,hT,v⟩:= (A.paths (Y.uv k)).issued; have ht:=(A.paths (Y.uv k)).paid;
 let R:=Actual Y.meter A.funds A.CapeT (gaugeFreq Λ (Y.tile*Λ.M)) (Y.uv k);
 have he:F=R.gram Λ.P b s:= congrFun hT s
 rw [he]; change SupportRate (detectorBudget (R.T.a s)) (head_L (R.chargeLevel Λ.P b s).1) _ _
 rw [ht.corr_successor Λ.H hb.toRealQ s u]; have hg: enters (hat Λ.R.L Λ.x s+Vale.billX Λ.R.L) ((b.read (s+1)).re:ℂ):= hat_step s ▸ (ht.beta_ok Λ.H hb.toRealQ (s+1) u).2
 exact q _ _ (R.toSpine.address s) _ _ (ht.request s u) _ _ hg (ht.flow (ht.charged Λ.H hb.toRealQ (s+1) u))

/-- XXI, equation 124. Actual family; rate = 1+10/B. Explicit scales and
poly exponent 8. Note `h` is the actual font order `Λ.h`; not making any
universal assertion over stronger fonts/germs/lit tests. See Lean type
of `SupportRate` for actual consultations, with all mask charges. -/
theorem provision124 (t:ActualRate Λ) : ∃ C>0, ∀ᶠ s in atTop, ∀ i k:ℕ,s<Y.uv k →
 let x:= hat Λ.R.L Λ.x s
 let F:= ((X₀ i k).gram s)
 SupportRate (detectorBudget F.p) (head_L F.F) Λ.h
       (C * (1+(radiusB x:ℝ))^8 * Scales.g SU.group Λ.R.L x^2 * Real.exp (Real.log (Real.log x)^2)) :=by
 obtain ⟨C,p,q⟩:=periphery_bound Λ.R.L; refine ⟨C,p,?_⟩
 filter_upwards [(full_rate Y t),(turnover Λ).eventually q] with s q u i k t
 obtain ⟨V,H,V'⟩:= (q i k t).supportCost; exact ⟨V,H,fun x=> (V' x).trans u⟩
#print axioms provision124

end LocalLimit
end Rate
end YM.CF.Py
