import Thin.Unzoom
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (Scree.mid N B) (Scree.mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (Scree.mid N B)}{Y: GramM (Scree.mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
variable (U:Grasp V.U B d)(W:GivenX V U)(s0:ℕ)(I:Stake.Isle)(v_:SheepP V U W I A k p s0)(e_:LocalRatio L) (t':1 < I.fine)
variable (q q':Chi)(u w' a h kL:ℝ)(h_:0 < A)(hw:0<a)(wS:scope_v a l R)(j_:l+100 ≤ j)(hL:6 ≤ k)(pL:2 ≤ p)(l0:5 ≤ l)(l1:l ≤18)
variable (hu:0 < kL)(wv:2*kL < firstRadius SU.group)(hx:h<d)(p0':0<u)(pv:u≤h)(M₀:ℕ)
variable (D_:Corset d q' kL (k+2) p)(Dμ m0 mC C C' wτ:ℝ)(Xc:SkyC k C)(hM:1 ≤ m0)(ha:1 ≤ mC)(Xp₀:SuitP k C')(Wol:0 ≤ wτ){κ0:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (k+2) p D_)
local notation "Sκ"=> a+2+2
local notation "Lφ"=> (a/4)
local notation "Zr"=> keyS (a+2+2) A 1 Xp₀.C l p k
local notation "Pδ"=> thermV (Sκ) m0 mC (a/4) Dμ Zr 2 Xc p l

variable {Qφ:Pilot}{Z:Pluck R}{E:Tun I Z Qφ ((tollE a)*100000)}{kz n_:ℕ} {H PΨ ρ kC:ℝ}
lemma TroughW_Th.start_b (x:TroughW_Th (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp Qφ Z q E kz M₀ n_ u h kL H PΨ ρ kC):
  TroughW (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp Qφ Z q E kz M₀ n_ u h kL H PΨ ρ:=by
 refine ⟨?_⟩; intro f g t dH hf hg ht hd tL p ag Cg ga gv J
 obtain ⟨J₁,v,F,S,Dk,M,u₁,u₂,u₃,u₄,Lr,hℓ,Dμ,tp,a₀,Y,hY,hZ,hG,ens⟩:= x.block _ _ _ _ hf hg ht hd tL p ag Cg ga gv J
 refine ⟨J₁,v,F,S,Dk,M,u₁,u₂,u₃,u₄,Lr,?_⟩
 filter_upwards [ens] with y p; refine ⟨p.2.1,p.2.2.1,p.2.2.2.1,?_⟩
 intro α β vS vG vT A0 E0 X Yv T₀ T₁ va pb κc κd hS hz
 obtain ⟨Mm,Hm,PP,t',hm,hr,Vr,Yu,Vp,Jz,Pb⟩:=p.2.2.2.2 vS vG vT A0 E0 X Yv T₀ T₁ va pb hS hz
 refine ⟨Mm,Hm,PP,t',hm,hr,Vr,Yu,Vp,Jz,?_⟩
 intro s F F2 Bq Wt ZX Ex
 obtain ⟨h1,h2,ph⟩:=Pb s F F2 Bq Wt
 refine ⟨h1,h2,fun v pr=>?_⟩
 obtain ⟨ht,tc,vc,k⟩:= ph v pr
 exact ⟨ht,tc,vc,fun h=>⟨(k h).1,(k h).2.1⟩⟩
#check totemVolume_Th
end YM.CF.Py
