import Thin.UnRiver
import YM.CF.Vp929.Stage.Plight
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
/-- This is the hypothesis on the very Treaty (not asserted generically!). -/
abbrev Treaty.Unbudget (kc:ℝ) := RiverWide_Th (j:=105) (l:=5) (A:=A) V U W D.I q 1 J.d D.D C' D.X D.jp D.pilot D.Z q D.E 3 J.n D.size J.k J.roomX J.d h Pay ρ kc
variable {w:Location (R:=R) B m n}
abbrev Pitching.SmallColorFee (c:Estimate) (o:Pitching w D x)(p p':BudgetPoint)(β:ℝ)(Fv:Corr (Scree.mid n B))(κ kc hv Dκ Dμ:ℝ) : Prop:=∀ A0:Pitching.base (w:=w) (q:=q) (J:=J) p' β Fv,∀ v':Pitching.fends p p' o β D.pilot,
 Clover (zv:=c.F x) V D.pilot D.Z (X:=Pitching.start (V:=V) (w:=w) p β) (Y:=Pitching.input (V:=V) (w:=w) p' β Fv) o.SheepR v' A0 o.bags o.t o.vista D.D h C' κ D.X D.jp (Pay*gritY R.L.val) (c.small x) Dκ ∧ Neon.Blush_X (X:=Pitching.start (V:=V) (w:=w) p β) (Y:=Pitching.input (V:=V) (w:=w) p' β Fv) V D.pilot D.Z o.SheepR v' A0 o.bags o.t o.vista h kc hv Dμ (c.small x)
structure ProvisionTh (c: Estimate)(N0:ℕ)(x f ff ag Cg kc hℓ Dκ Dμ:ℝ) : Prop extends Provision (D:=D) c N0 x f ff ag Cg where
 unzoom : ∀ m n (w:Location (R:=R) B m n) p p', w.Request V U W J q N0 x p p' → ∃ o:Pitching w D x,o.Gains c p p' f ff ag Cg ∧ ∀ β F, Pitching.Sample c p p' o f ag Cg β F→ Location.gross p' D ff F → Pitching.SmallColorFee D c o p p' β F ff kc hℓ Dκ Dμ

lemma Treaty.provisions_Th (kc:ℝ)(ub:D.Unbudget kc) (hf: sizeK R.L 1 κ) (hg:sizeK R.L 2 κs) (hv: ∀ᶠ x in atTop, 0≤κ x ∧ 0≤κs x) (ha:0<ag)(hp:0<Cg)(J0:ℕ) :
    ∃ c:Estimate,c.Economic R ∧ J0 ≤ c.blips ∧ ∃ hℓ:ℝ, ∃ Dκ Dμ:ℝ→ℝ, 0<hℓ ∧ Litt R 2 Dκ ∧ sizeK R.L 4 Dμ ∧ ∃ Yζ:BudgetPoint,Yζ.supportExponent=1 ∧ Yζ.order=6 ∧ Yζ.power=2 ∧ ∀ᶠ x in atTop, Neon.TimΞ R.L 6 2 5 x hℓ (Dμ x) Yζ ∧ ∀ N0,D.size ≤ N0 → ProvisionTh D c N0 x (κ x) (κs x) ag Cg kc hℓ (Dκ x) (Dμ x) := by
  obtain ⟨J₁,hJ,f,s,H,Qh,Fκ,Xr,P,h1,h2,h3,h4,h5,h6,h7,h8,Q,hℓ,Dμ,Dκ,Hv,Vμ,Hκ,pv,ey,et,eu,Hs⟩:=ub.block κs κs κs κs hg hg hg (hg.low (by omega)) _ (hf.scale (3:ℝ)) ag Cg ha hp J0
  let c:Estimate:=⟨J₁,f,s,H,Qh,Fκ,Xr,P,Q⟩
  refine ⟨c,⟨h1,h4,h2,h3,h5,h6,h7,h8⟩,hJ,hℓ,Dκ,Dμ,Hv,Hκ,Vμ,pv,ey,et,eu,?_⟩
  filter_upwards [Hs,hv,D.wide,(Scales.year SU.group R.L).eventually_gt_atTop 0,pondsVolume V D.pilot 105 5 (6+2) J.ht J.hv] with x hx ht hf hP he
  obtain ⟨pφ,hw,hk,hq,hy⟩:= hx
  -- common o both grants
  refine ⟨pφ,fun N0 hg=> ?_⟩
  suffices Hu: ∀ m n (w:Location (R:=R) B m n) p p', w.Request V U W J q N0 x p p' → ∃ o:Pitching w D x,o.Gains c p p' (κ x) (κs x) ag Cg ∧ ∀ β F, Pitching.Sample c p p' o (κ x) ag Cg β F→ Location.gross p' D (κs x) F → Pitching.SmallColorFee D c o p p' β F (κs x) kc hℓ (Dκ x) (Dμ x) by
    refine { revenue:=hk, crew:=hq, wide:=hf, warm:=fun a=> @he a, provides:= fun _ _ _ _ _ r=> (Hu _ _ _ _ _ r).imp fun _ w=>w.1, unzoom:=Hu }
  intro m n w p p' g
  let y:= Scales.y SU.group R.L x; have hb : y∈ Year R x:= by change y/2≤y ∧ y≤2*y; change 0< y at hP; constructor<;>linarith
  let Y:=Pitching.input (V:=V) (w:=w) p' y 0; let X:=Pitching.start (V:=V) (w:=w) p y
  have hr (β) (F:Corr (Scree.mid n B)) (b:β∈Year R x) : StatV V w.G (w.Φ (V:=V)) U W (w.buildOut V p (β+w.movement V) 0 0) (w.buildIn V p' β F 0) (V.L.charge w.lag) w.fee 1 x 2 6:=g.statv β F 0 0 b
  let Py:= Classical.choice (Pitching.start_base (D:=D) p p' 0 (Location.gross_zero D p' _ ht.1) y hb g)
  obtain ⟨M,H,P,t,v,hM,hP,s,hs,j,hj⟩:=hy (w.step V) w.G (w.Φ (V:=V)) w.coarse w.fine X Y g.rocket.paid g.roof g.rocket.pose Py (hr y 0 hb) ((Nat.mul_le_mul_right _ hg).trans g.size)
  have ht' := hj 1 0 0 0 0; have ha:H.ang=V.L.charge w.lag:=ht'.1; have hβ:H.fee=w.fee:=ht'.2.1
  let o:Pitching w D x:=⟨M,H,P,t,v,s,hs,hM,ha,hβ,j⟩
  have main (β)(F:Corr (Scree.mid n B))(hβ': β∈ Year R x)(T0:Pitching.base (V:=V) (w:=w) (J:=J) (q:=q) p' β F): StageP V (o.tinted β) (w.buildIn V p' β F 0) (w.buildOut V p (β+w.movement V) 0 0) U ∧ ∃ v':Pitching.fends p p' o β D.pilot,
    SiteCost (j:=105) (l:=5) (X:=w.buildOut V p (β+w.movement V) 0 0) (Y:=w.buildIn V p' β F 0) V U W D.I q 1 J.d D.pilot D.Z q (o.tinted β) D.E J.k o.t h ag Cg (3*κ x) (c.Pc x) c.blips o.SheepR o.bags ∧ (Location.gross p' D (κs x) F →
    (LookZ V (Xm:=Pitching.start (V:=V) (w:=w) p β) (Xu:=Pitching.input (V:=V) (w:=w) p' β F) o.SheepR v' T0 o.bags o.vista o.Jz (c.F x) ((tolQ p).supportExponent+1) ∧ Corona_Q (zv:=c.F x) V D.pilot D.Z o.SheepR (X:=Pitching.start (V:=V) (w:=w) p β) (Y:=Pitching.input (V:=V) (w:=w) p' β F) v' T0 o.bags o.t o.vista D.D h C' (κs x) D.X D.jp (c.H x) (Pay*gritY R.L.val) (c.small x) (c.Xr x) (c.Qh x) (c.Fκ x) ∧
     Clover (zv:=c.F x) V D.pilot D.Z (X:=Pitching.start (V:=V) (w:=w) p β) (Y:=Pitching.input (V:=V) (w:=w) p' β F) o.SheepR v' T0 o.bags o.t o.vista D.D h C' (κs x) D.X D.jp (Pay*gritY R.L.val) (c.small x) (Dκ x) ∧ Neon.Blush_X (X:=Pitching.start (V:=V) (w:=w) p β) (Y:=Pitching.input (V:=V) (w:=w) p' β F) V D.pilot D.Z o.SheepR v' T0 o.bags o.t o.vista h kc hℓ (Dμ x) (c.small x))) := by
    have hm := hj β F.1 0 F.2 0; dsimp only at hm; rw [ha,hβ] at hm
    obtain ⟨hh,ε',vκ,hc⟩:= hm.2.2 (hr β F hβ') T0
    refine ⟨hh,ε',vκ,fun p₁=>?_⟩
    exact hc ⟨p₁.1,(Location.gross_zero D p' _ ht.2).1,p₁.2⟩
  refine ⟨o, ⟨fun β h F v=> ?_,fun β F g v he T0=>?_,hP⟩,fun β F hs hc T0 v'=>?_⟩
  · obtain ⟨R⟩:=Pitching.start_base p p' F v β h g; obtain ⟨hh,z,v,_⟩:=main β F h R; exact ⟨hr β F h,hh,z,⟨R⟩,v⟩
  · obtain ⟨_,_,_,w⟩:= main β F g.statv.rest T0; exact ⟨(w v).1,(w v).2.1⟩
  obtain ⟨_,_,_,w⟩:= main β F hs.statv.rest T0; exact (w hc).2.2
end YM.CF.Py.Rate
