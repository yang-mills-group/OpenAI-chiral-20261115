import YM.CF.Vp929.Grant.River
import YM.CF.Ridge.Luz
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
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

variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Nor
variable (U:Grasp V.U B d)(W:GivenX V U)(s0:ℕ)(I:Stake.Isle)(v_:SheepP V U W I A k p s0)(e_:LocalRatio L) (t':1 < I.fine)
variable (q q':Chi)(u w' a h kL:ℝ)(h_:0 < A)(hw:0<a)(wS:scope_v a l R)(j_:l+100 ≤ j)(hL:6 ≤ k)(pL:2 ≤ p)(l0:5 ≤ l)(l1:l ≤18)
variable (hu:0 < kL)(wv:2*kL < firstRadius SU.group)(hx:h<d)(p0':0<u)(pv:u≤h)(M₀:ℕ)
variable (D_:Corset d q' kL (k+2) p)(Dμ m0 mC C C' wτ:ℝ)(Xc:SkyC k C)(hM:1 ≤ m0)(ha:1 ≤ mC)(Xp₀:SuitP k C')(Wol:0 ≤ wτ){κ0:ℝ}(Jp:PactH d kL (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (k+2) p D_)
local notation "Sκ"=> a+2+2
local notation "Lφ"=> (a/4)
local notation "Zr"=> keyS (a+2+2) A 1 Xp₀.C l p k
local notation "Pδ"=> thermV (Sκ) m0 mC (a/4) Dμ Zr 2 Xc p l

variable (F:Pilot)(Z:Pluck R)(E₀:Tun I Z F ((tollE a)*100000))(n₀:ℕ)(Hp:ℝ)(tH:1≤Hp)(Kz:ℕ)(Pav ρ:ℝ)
variable (pR: TroughW (j:=j) (l:=l) (A:=A) V U W I q' a kL D_ C' Xp₀ Jp F Z q E₀ Kz M₀ n₀ u h kL Hp Pav ρ)
namespace Rate
include pR
lemma retain : Trough (j:=j) (l:=l) (A:=A) V U W q' a kL D_ C' Xp₀ Jp F Z q Kz M₀ n₀ u h kL Hp Pav ρ:=by
 refine ⟨fun f g f' δ h0 h1 h2 h3=>?_⟩; obtain ⟨_,_,F',S',Dκ,P₁,e,i,a,z,Qht,H⟩:=pR.block f g f' δ h0 h1 h2 h3 δ h3 1 1 zero_lt_one zero_lt_one 0
 refine ⟨F',S',Dκ,e,i,a,Qht,?_⟩; filter_upwards [H] with x h; obtain ⟨u,v,g,h⟩:=h
 refine ⟨@u,v,g,fun {N P} S G T A0 E X Y p1 p2 p3 P0 {Z' γ} p4 p5=>?_⟩
 obtain ⟨M,Hm,PP,t',ht,h1,h2,h3,v,Jz,H⟩:=h S G T A0 E X Y p1 p2 p3 P0 p4 p5
 refine ⟨M,Hm,PP,t',ht,h1,h2,Jz,?_⟩; intro s F0 F1 Q Wu X' Uv; obtain ⟨u,v,p⟩:=H s F0 F1 Q Wu
 refine ⟨u,v,fun θ pY P_=>?_⟩; obtain ⟨p,τ,_,hq⟩:=p θ P_; exact ⟨p,τ,hq pY⟩
omit pR
lemma delay_Coffer {u₁ u₂:ℕ}(u0:Coffer (p:=p) (k:=k) V U W q a kL M₀ Pav u₁ u h Hp)(v:u₁≤u₂):Coffer (p:=p) (k:=k) V U W q a kL M₀ Pav u₂ u h Hp:=by
 refine ⟨fun f g f' δ p1 t p2 p3 hm=>?_⟩; obtain ⟨R0,E,C,D,e1,e2,e3,e4,H⟩:= u0.wrap f g f' δ p1 t p2 p3 hm; refine ⟨R0,E,C,D,e1,e2,e3,e4,?_⟩
 filter_upwards [H] with x h; obtain ⟨e,t'⟩:=h; refine ⟨e,fun {N P} S G=> ?_⟩; obtain ⟨c,w,y⟩:= t' S G
 refine ⟨c,w,?_⟩; intro T A0 B X Y θ t k P0 Z' γ hu hN; exact y T A0 B X Y θ t k P0 hu ((Nat.mul_le_mul_right _ v).trans hN)

lemma delay_HoldU {u₁ u₂:ℕ}(u0:HoldU (p:=p) (k:=k) V U W q a kL M₀ Pav u₁ u h Hp)(v:u₁≤u₂):HoldU (p:=p) (k:=k) V U W q a kL M₀ Pav u₂ u h Hp:=by
 refine ⟨fun f g f' δ p1 p2 p3 p4=>?_⟩; obtain ⟨R0,E,C,D,e1,e2,e3,e4,H⟩:= u0.wrap f g f' δ p1 p2 p3 p4; refine ⟨R0,E,C,D,e1,e2,e3,e4,?_⟩
 filter_upwards [H] with x h; obtain ⟨e,t'⟩:=h; refine ⟨e,fun {N P} S G=> ?_⟩; obtain ⟨c,w,y⟩:= t' S G
 refine ⟨c,w,?_⟩; intro T A0 B X Y θ t k P0 Z' γ hu hN; exact y T A0 B X Y θ t k P0 hu ((Nat.mul_le_mul_right _ v).trans hN)

lemma delay_VaultXU {u₁ u₂:ℕ}(u0:VaultXU (p:=p) (k:=k) V U W q a kL M₀ Pav u₁ u h Hp)(v:u₁≤u₂):VaultXU (p:=p) (k:=k) V U W q a kL M₀ Pav u₂ u h Hp:=by
 refine ⟨fun f g f' δ p1 p2 p3 p4=>?_⟩; obtain ⟨R0,E,C,D,e1,e2,e3,e4,H⟩:= u0.boot f g f' δ p1 p2 p3 p4; refine ⟨R0,E,C,D,e1,e2,e3,e4,?_⟩
 filter_upwards [H] with x h; obtain ⟨e,t'⟩:=h; refine ⟨e,fun {N P} S G=> ?_⟩; obtain ⟨c,w,y⟩:= t' S G
 refine ⟨c,w,?_⟩; intro T A0 B X Y θ t k P0 Z' γ hu hN; exact y T A0 B X Y θ t k P0 hu ((Nat.mul_le_mul_right _ v).trans hN)

end Rate
end YM.CF.Py
