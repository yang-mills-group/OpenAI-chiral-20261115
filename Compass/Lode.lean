import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Py
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
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
open Neon Ione Lattice.PlaqAxes AnalyticBridge.VerifiedReset
variable {N0:Side}{h c:ℝ}(s:Sweep N0)(hs:Anchored s.s)(Q: BudgetPoint)
-- g moves old? (g s) o = old = a=s^-1 . Claim gInv injective. no quotient.
abbrev inspire(s:Sweep N0)(o:Site N0):Site N0:= Tofu (castX s⁻¹) N0 o
lemma node_inspire(o:Site N0): Cube.node (inspire s o)= (boxA s).symm (Cube.node o):=Shape.nodex ..
lemma drift_node(o:Site N0):inspire s⁻¹ (inspire s o)=o:=by
 apply (fun x y h=> (assembly N0).embed_injective (add_right_cancel (show _+(1:Site (More N0))=_+_ from h)): Function.Injective (@Cube.node N0)); rw [node_inspire,node_inspire,sitU]; exact (boxA s).apply_symm_apply _ -- Crop
local notation "γ" i:max=> AnalyticBridge.VerifiedReset.dirS s.s i
def tiltA (s:Sweep N0)(X:ArcΦ):ArcΦ := (fun i j=> let a:=rotate s.s⁻¹ i; let b:=rotate s.s⁻¹ j; (AnalyticBridge.VerifiedReset.dirS s.s a * AnalyticBridge.VerifiedReset.dirS s.s b) • Spire.payZ s⁻¹ (X.1 a b), driftH (s⁻¹).s s.charge (detX (s⁻¹).s) (spinU s.charge (s⁻¹).s) X.2)
lemma riseΦ_zero : tiltA s 0=0:=by
 apply Prod.ext; · funext i j; change _ • Spire.payZ s⁻¹ (0:ℂ)=0; exact (show _=_ from by unfold Spire.payZ; rw [Ione.sign0,smul_zero])
 have hp(X:UNI Hove.Kt): sings s.charge X 0=0:=by rw [singT,win_z,map_zero]
 have ht(v:Bool): Thera.jazz v (0:Op Hove.Kt)=0:=by unfold Thera.jazz; split; simp; rfl
 change driftH _ _ _ _ (0:Dome)=0; unfold driftH; split <;> first|skip
 all_goals refine Prod.ext ?_ (Prod.ext (funext fun i=>?_) (funext fun j=>?_))
 all_goals first| (change Thera.jazz _ (sings s.charge _ 0) = 0; rw [hp, ht])| (change _ • Thera.jazz _ (sings s.charge _ 0)=0; rw [hp,ht,smul_zero])| (change _ • sings s.charge _ 0=0; rw [hp,smul_zero])
lemma flash_one:flashA s (1: Pane N0)=1:=by rw [Skye.revoke]; funext ⟨i,j⟩; change polarT _ (Step.read ..) = 1; unfold Step.read; split <;> simp -- tune
lemma motDome (o:Site N0)(F:InkD N0)(X':Support (More N0))(v:Flour (camp X') (F 1).val)(w:Nonwrapping X' (Cube.node (inspire s o))):
 jetsL o (orbitPH ((step_F s F) 1))= driftH (s⁻¹).s s.charge (detX (s⁻¹).s) (spinU s.charge (s⁻¹).s) (jetsL (inspire s o) (orbitPH (F 1))) :=by
 let V:= spinU s.charge (s⁻¹).s; let p0:= s.charge; let r:=detX (s⁻¹).s; let A:= castX s⁻¹
 let M:=orbitPH (F 1)
 have he:orbitPH ((step_F s F) 1)=Thera.jazz r (sings p0 (siteU A p0 V _) M):=by
    have hx:F (flashA s 1)=F 1:=congrArg F (flash_one s)
    have hb:step_F s F 1=suit_Y s⁻¹ (F 1):=by unfold step_F; simp only [Function.comp_apply,hx]
    refine (congrArg orbitPH hb).trans ?_
    change orbitPH (paintR p0 r (siteU A p0 V N0) (F 1))= _; exact paral (F 1) p0 r (siteU A p0 V _)
 rw [he]; exact dome_P A V p0 r (spinZ ..) o X' w _ (op_cut (F 1) X' v)
include hs
section
variable (s:Sweep (mid N B))(hs':Anchored s.s)
omit hs
include hs'
lemma motives(o:Site (mid N B))(T:Scree.Hub (mid N B))(X':Scree.Hub (mid N B))(e:moveHub s T=X')(W:InkD (mid N B))(hx: PressB Q X' W h c)(u:0≤h)(h':T.val.1=Cube.node o)(z:4≤ (More (mid N B)).val)(wr: Nonwrapping X'.val.2 X'.val.1):
 pillar (N:=N) (B:=B) o (step_F s W) Q= tiltA s (pillar (N:=N) (B:=B) (inspire s o) W Q) :=by
 -- mid 1 N0 is ??? inspect. Axon defined mid N B $ product maybe def = CSide N B= N*B. leading ? need use with n = mid. instead define lemma using inks with N0:=mid and replace.
 let F:=suit_Y s⁻¹
 let m':= Haro.orbitPH (W 1)
 have he: X'.val.1=Cube.node (inspire s o):=by rw [←e,node_inspire,←h']; rfl
 refine Prod.ext ?_ ?_
 · funext k l; change tooth (Cube.node o) Q _ k l= _
   obtain ⟨a,rfl⟩:=(transform s.s).surjective k; obtain ⟨b,rfl⟩:=(transform s.s).surjective l
   change tooth (Cube.node o) Q (step_F s W) (rotate s.s a) (rotate s.s b)=(AnalyticBridge.VerifiedReset.dirS s.s _* _) • Spire.payZ s⁻¹ (tooth (Cube.node (inspire s o)) Q W (rotate _ (rotate _ a)) (rotate _ (rotate _ b)))
   rw [rotate_inv,rotate_inv,←h',←he,←e]; change _= (AnalyticBridge.VerifiedReset.dirS s.s (rotate s.s⁻¹ (rotate s.s a)) * AnalyticBridge.VerifiedReset.dirS _ (rotate s.s⁻¹ (rotate s.s b))) • _; rw [rotate_inv,rotate_inv]; exact sombr T Q s W hs' (e.symm ▸ hx) u (e.symm ▸ wr) z a b
 change jetsL o (Haro.orbitPH ((step_F s W) 1))= _
 exact motDome s o W _ (hx.fitted _) (he ▸ wr)
end
end YM.CF.Compass
