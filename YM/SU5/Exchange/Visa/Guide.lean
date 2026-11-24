import YM.SU5.Exchange.Visa.Fort
import YM.SU5.Exchange.Reg.RateMargin
import YM.CF.Vale.Wing
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
noncomputable section
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
local notation "xt" => hat P.R.L P.x

local notation "iO"=> P.J
local notation "Ω🌃" i:max s:max=> cell (Y.ir i) P.block P.R.L s
-- for visits from real path. includes Grasp, on wider d than needed lamp
abbrev VisaKit (s i k:ℕ)(a c u m:ℝ):Prop:= let R:=RootBook Y i k s; let n:= cell (Y.ir i) P.block P.R.L s; let A:= (Y.voyage i).CapeT s
 Tulip.Solo a c (funde P.K.j R.J.M n) P.d ∧ Tulip.Solo a c (Moire.bloom R.J.P) P.d ∧ Roof n P.J.k P.J.roomX P.J.n A ∧ P.U.roundZ ≤ n.val ∧ R.p.threshold ≤ P.J.k ∧ R.p.order=6 ∧ 3 ≤ R.p.B ∧ cipherK P.J.n ≤ 5 *R.p.B ∧ HopeT P.d u m R.p.order ∧ R.p.threshold ≤ m ∧ R.slip=0
structure Compass_sol : Prop where
 pays: ∃ a c u m:ℝ,0 < a ∧ 0 < c ∧ 0 < u ∧ 0 < m ∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k,s<Y.uv k→ VisaKit Y s i k a c u m
include flag
lemma visa_onPath (X:Solstitial P):Compass_sol Y:=by
 obtain ⟨a,c,u,v,qS⟩:= X.season
 obtain ⟨n,q⟩:= qS.exists
 obtain ⟨m,N,t⟩:= Rill.cozy 6 P.dpos
 refine ⟨a,c,N,m,u,v,t.ease,t.peta,?_⟩
 filter_upwards [(turnover P).eventually ((show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds t.peta)),(Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop (cipherK P.J.n+3)] with s hS w
 filter_upwards [Y.ir_grows.tendsto_atTop.eventually_ge_atTop n] with i h k hk
 let Y' := Y.voyage i; let D:=Coord i k; let v' := Y.meter.a s; let v1:=Y.meter.a (s+1); let m₀:= mesh (Y.ir i) P.R.L s; let m₁:=mesh (Y.ir i) P.R.L (s+1)
 let ρ:= Actual Y.meter Y'.funds Y'.CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k)
 let K:= ρ.toSpine.address s
 obtain ⟨p,b,hb,g⟩:= flag i (Y.uv k); let hQ:= hb.toRealQ
 have hl:ρ.active P.P b s=ρ.gram P.P b s:= p.success P.H hQ s hk (p.paysStep P.H hb s hk)
 have hv:= p.request s hk; let J:=ρ.active P.P b s; let A:=(Y.voyage i).CapeT s; let R:=P.R
 unfold VisaKit; unfold RootBook
 simp only [g.gramZ, ←hl]
 have H:= q _ (show n≤(cell _ _ _ s).val from le_trans h (Vale.amplit (Y.ir i) P.block R.L s))
 let o:=Y.meter.boot s; have hB: v'.B=radiusB (hat R.L P.x s):= o.2.1; let D₀:= (Y.voyage i).ownership s
 -- tune active unfold
 have ht:(J.p)=v':= rfl
 change Tulip.Solo _ _ (funde _ J.J.M _) _∧ Tulip.Solo _ _ (Moire.bloom J.J.P) _ ∧ Roof _ _ _ _ _ ∧ P.U.roundZ ≤ _ ∧ J.p.threshold ≤ _ ∧ J.p.order= _ ∧ 3≤ J.p.B ∧ _ ∧ _ ∧ _
 rw [ht]
 have hG:J.J=K.output:=rfl
 change cipherK P.J.n+3 ≤ radiusB (hat R.L P.x s) at w
 exact ⟨H.1 J.J.M,H.2 J.J (show InterestX .. from (show InterestX P.W.C _ K.output from hv.sound)), D₀.paid,P.J.gran.trans D₀.size,hv.pole,o.2.2.2.2,(hB.symm ▸ (by omega)), (hB.symm ▸ (by omega)), o.2.2.2.2.symm ▸ t, o.1.symm ▸ hS,True.intro⟩
end Preparation
end LocalLimit
end YM.CF.Py.Rate
