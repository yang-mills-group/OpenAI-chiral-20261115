import YM.CF.Vp929.Fixed.Delivery
import WinterX.Billing
import Thin.Rail
import Thin.Supply
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Branch
open Pitching Pitching.Focus
variable {J q h D C R0 T S ρ f i}
variable (s:Parcel J q h D C R0 T ht S ρ f k)
variable {delay:ℝ}{P:Prescription R B}(H:Service V U W J q h D C R0 P N0 delay)(t:s.Prepared P delay)
variable (G:Morn K)(Q:Diary)(sk:G.After R)(Lq:ShelfTh G Q R0 D C J q h P N0 delay)
local notation "Yc"=> (hat R.L x i)
local notation "Ar"=> G.armor
local notation "w0"=> ((Actual T ht S f k).toSpine.address i)
local notation "fϕ"=> thinAllot G.Mult R Yc
local notation "fZ"=> (3*dleaf R.L Yc)
include H t sk Lq
open Oath
lemma purchasedZ (hk:i<k) :
    Zodiac V U (s.gram i) (s.gram (i+1)) ((w0).step V) (w0).G (S i) (S (i+1)) (s.wave i).val q J.d h (Q.V1 Yc) (Q.KR Yc) (Q.W Yc)
    (Ar).delta (Ar).f0 (Ar).g0 (Ar).g1 (Ar).g2 (Q.Z Yc) (fZ+fϕ) (fZ+fϕ) (fZ+fϕ) fϕ (Ar).n ∧
    Arc_r (s.gram (i+1)) h fZ fZ fZ ∧ IncX primeU (s.gram (i+1)).F (s.gram (i+1)).p h 1:=by
 obtain ⟨Bon,b,u,Kz⟩:= t
 let M:= Actual T ht S f k; let F:=M.chargeLevel P b (i+1); let β:=(b.read (i+1)).re
 have hF:= Bon.flow (Bon.charged H u.toRealQ (i+1) hk)
 have hB:enters (Yc+billX R.L) (β:ℂ):= hat_step (L:=R.L) i ▸ (Bon.beta_ok H u.toRealQ (i+1) hk).2
 let p0:= Bon.late.trans (Vale.crown R.L x i)
 let pQ:=M.T.a i; let pU:=M.T.a (i+1); let pM:= Bon.request _ hk
 have hq:=Lq.snapZ sk w0 pQ pU p0 pM F (M.offset P b (i+1)) hB hF
 let Q0:ℝ:=3*dleaf R.L Yc
 obtain ⟨caps,r,Hh,r0,hR,Z⟩:= Lq.ships _ _ w0 Yc pQ pU p0 pM; letI:=hR; obtain ⟨b₀,_,_,hn⟩:=Z
 obtain ⟨A,C',r',a,c,v,z,T',m0,X,_,_,_,_,_,_,_,_,_,_,_,_,_,no,_⟩:=hn.merchants -- `no.i1` for Q0 bound
 have hi: Q0≤1:=no.i1
 have hpos:0≤Q0:=mul_nonneg (by norm_num) caps.high.le
 have hArc (v:ℂ): Arc_r ((w0).buildIn V pU β F v) h Q0 Q0 Q0:=by
    have he:Location.gross pU T' Q0 F:= gross_shape (w:=w0) (D:=T') hF le_rfl
    exact ⟨he.1,Fixed.Voltage.upgradeI _ _ ((Vale.lye _ pU h).1) hpos,he.2⟩
 unfold brightAllZ at hq; dsimp only at hq
 rw [Kz.gramZ,Kz.waveZ,←Bon.success H u.toRealQ i hk (Bon.paysStep H u i hk), Branch.gram_fine _ _ _ _ hk]
 let E:= hArc (M.offset P b (i+1))
 exact ⟨hq,E, Py.core_B _ _ _ _ _ E hi⟩
end Parcel
end YM.CF.Py.Rate

#print axioms YM.CF.Py.Rate.Parcel.purchasedZ
