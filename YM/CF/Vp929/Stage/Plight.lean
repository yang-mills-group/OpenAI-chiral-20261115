import YM.CF.Vp929.Stage.Treaty
set_option autoImplicit false
set_option maxHeartbeats 800000
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi)
variable {J q} {A C' Pay h ρ f ff τ ag Cg x β : ℝ} (D : Treaty J q A C' Pay h ρ) {κ κs : ℝ→ℝ}
lemma Treaty.provisions (hf: sizeK R.L 1 κ) (hg:sizeK R.L 2 κs) (hv: ∀ᶠ x in atTop, 0≤κ x ∧ 0≤κs x) (ha:0<ag)(hp:0<Cg)(J0:ℕ) :
    ∃ c:Estimate,c.Economic R ∧ J0 ≤ c.blips ∧ ∀ᶠ x in atTop, ∀ N0,D.size ≤ N0 → Provision (D:=D) c N0 x (κ x) (κs x) ag Cg := by
  obtain ⟨J₁,hJ,f,s,H,Qh,Fκ,Xr,P,h1,h2,h3,h4,h5,h6,h7,h8,Q,Hs⟩:=D.budget.block κs κs κs κs hg hg hg (hg.low (by omega)) _ (hf.scale (3:ℝ)) ag Cg ha hp J0
  let c:Estimate:=⟨J₁,f,s,H,Qh,Fκ,Xr,P,Q⟩
  refine ⟨c,⟨h1,h4,h2,h3,h5,h6,h7,h8⟩,hJ,?_⟩
  filter_upwards [Hs,hv,D.wide,(Scales.year SU.group R.L).eventually_gt_atTop 0,pondsVolume V D.pilot 105 5 (6+2) J.ht J.hv] with x hx ht hf hP he N0 hg
  obtain ⟨hw,hk,hq,hy⟩:= hx
  refine ⟨hk,hq,hf,fun a=> @he a,fun m n w p p' g=> ?_⟩
  let y:= Scales.y SU.group R.L x; have hb : y∈ Year R x:= by change y/2≤y ∧ y≤2*y; change 0< y at hP; constructor<;>linarith
  let Y:=Pitching.input (V:=V) (w:=w) p' y 0; let X:=Pitching.start (V:=V) (w:=w) p y
  have hr (β) (F:Corr (Scree.mid n B)) (b:β∈Year R x) : StatV V w.G (w.Φ (V:=V)) U W (w.buildOut V p (β+w.movement V) 0 0) (w.buildIn V p' β F 0) (V.L.charge w.lag) w.fee 1 x 2 6:=g.statv β F 0 0 b
  let Py:= Classical.choice (Pitching.start_base (D:=D) p p' 0 (Location.gross_zero D p' _ ht.1) y hb g)
  obtain ⟨M,H,P,t,v,hM,hP,s,hs,j,hj⟩:=hy (w.step V) w.G (w.Φ (V:=V)) w.coarse w.fine X Y g.rocket.paid g.roof g.rocket.pose Py (hr y 0 hb) ((Nat.mul_le_mul_right _ hg).trans g.size)
  have ht' := hj 1 0 0 0 0; have ha:H.ang=V.L.charge w.lag:=ht'.1; have hβ:H.fee=w.fee:=ht'.2.1
  let o:Pitching w D x:=⟨M,H,P,t,v,s,hs,hM,ha,hβ,j⟩
  have main (β)(F:Corr (Scree.mid n B))(hβ': β∈ Year R x)(T0:Pitching.base (V:=V) (w:=w) (J:=J) (q:=q) p' β F): StageP V (o.tinted β) (w.buildIn V p' β F 0) (w.buildOut V p (β+w.movement V) 0 0) U ∧ ∃ v':Pitching.fends p p' o β D.pilot,
    SiteCost (j:=105) (l:=5) (X:=w.buildOut V p (β+w.movement V) 0 0) (Y:=w.buildIn V p' β F 0) V U W D.I q 1 J.d D.pilot D.Z q (o.tinted β) D.E J.k o.t h ag Cg (3*κ x) (c.Pc x) c.blips o.SheepR o.bags ∧ (Location.gross p' D (κs x) F →
    (LookZ V (Xm:=Pitching.start (V:=V) (w:=w) p β) (Xu:=Pitching.input (V:=V) (w:=w) p' β F) o.SheepR v' T0 o.bags o.vista o.Jz (c.F x) ((tolQ p).supportExponent+1) ∧ Corona_Q (zv:=c.F x) V D.pilot D.Z o.SheepR (X:=Pitching.start (V:=V) (w:=w) p β) (Y:=Pitching.input (V:=V) (w:=w) p' β F) v' T0 o.bags o.t o.vista D.D h C' (κs x) D.X D.jp (c.H x) (Pay*gritY R.L.val) (c.small x) (c.Xr x) (c.Qh x) (c.Fκ x))) := by
    have hm := hj β F.1 0 F.2 0; dsimp only at hm; rw [ha,hβ] at hm
    obtain ⟨hh,ε',vκ,hc⟩:= hm.2.2 (hr β F hβ') T0
    refine ⟨hh,ε',vκ,fun p₁=>?_⟩
    exact hc ⟨p₁.1,(Location.gross_zero D p' _ ht.2).1,p₁.2⟩
  refine ⟨o, fun β h F v=> ?_,fun β F g v he T0=>?_,hP⟩
  · obtain ⟨R⟩:=Pitching.start_base p p' F v β h g; obtain ⟨hh,z,v,_⟩:=main β F h R; exact ⟨hr β F h,hh,z,⟨R⟩,v⟩
  obtain ⟨_,_,_,w⟩:= main β F g.statv.rest T0; exact w v
end YM.CF.Py.Rate
