import YM.CF.DPress.Act.Village
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {x:ℝ}{C:Tew W}{β:ℝ}{O:Shore0} {Q:Maud x C G S}
 {P_:Campus C}
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Arco WagesC
open UVNext.PricedKernels Work.F03 WilsonStartup
namespace Act
open Harvester WagesC Urban
namespace Silo
variable {A:Harvester P_}{ξ:ℝ→ℝ}(T: Silo A ξ Q O) (Wν : Blend (mid N B) A.μ) (α:ℝ)
local notation "vΠ"=> mid N B
local notation "vℓ"=> Q.X.p
open Rue
variable (E:Lobby Q O β)(p: HonestL E)(t:Can Q P_ O.δ α)
include t
-- no zero-risk. D(v).betaL equals upper fixed theta term.X)' ...(κphi only). absorb PicSharp. use Exp. No norm assumptions.
variable (z:Orbit (mid N B))(g:FleetS Q.X.p.threshold z.1)
local notation "AΛ"=> T.priceGas E p z
local notation "Δ'"=> T.Δa α E p
local notation "E0"=> T.Hrel β
local notation "I'"=> enerS_K (T.Hrel β) (Δa T α E p) z
local notation "Pu"=> πH (Q:=Q) Wν α z
include g
abbrev host : Cipher (mid N B) → Scree.Phys (mid N B):= fun f=> acts (Scree.tank (spar K.j Q.X.J.M (Q.G₀ z)) f) (Scree.relV U Q.X.J (Q.G₀ z))
lemma SFS(v:ℂ): Scree.denZ (T.D Wν α E p v) U Q.G₀ z= Complex.exp (((T.Hrel β).betaL Q.G₀ z)+v-((T.eventL α E p t -πH (Q:=Q) Wν α z:ℝ):ℂ)) • host (Q:=Q) z (AΛ) :=by
 let X:= T.D Wν α E p v; let s:= T.eventL α E p t+I'-Pu; let y:= X.board z; have ht:(AΛ)=Real.exp s • y:=by rw [T.gainΦ Wν α E p t z g]; unfold y GramM.board; rw [show X.slip=0 from rfl,Vale.still_Footprint,add_zero]
 let k:=spar K.j Q.X.J.M (Q.G₀ z); let b(C:ℝ):ℂ:=Real.exp C; let hv: IsStarProjection k:= eligible z; have he(C:ℝ):host (Q:=Q) z (Real.exp C • y)= b C • host (Q:=Q) z y:=by
    unfold host; rw [←Complex.coe_smul]; apply Eq.trans (?_: _=acts ((↑(Real.exp C):ℂ) • tank k y) (relV U Q.X.J (Q.G₀ z))); · exact act_smul ..
    refine congrArg (fun A=> acts A _) ?_; change Scree.tank k _=_; rw [tank_eq _ _ hv,tank_eq k y hv]; exact map_smul ((nursery k hv).eval) (↑(Real.exp C):ℂ) y.val -- tune `kernel eval` Prop.s
 let x:= (E0).betaL Q.G₀ z; have hx:X.betaL Q.G₀ z=x+v+(I':ℝ):=by unfold x X D GramM.betaL GramM.H0 spark_B slew_e enerS_K; rw [show (T.Hrel β).v=0 from rfl]; push_cast; ring -- check coercion.Lean.RecordUpdate
 change Complex.exp (X.betaL Q.G₀ z) • host (Q:=Q) z y= _; rw [hx,ht,he,smul_smul]; refine congrArg (· • _) (?_: _= _ * _); unfold b; rw [Complex.ofReal_exp,←Complex.exp_add]; apply congrArg Complex.exp; unfold s; push_cast; unfold x; ring -- timeout abel PicSharp!
variable (Z:Monk SU.group S)
abbrev vπ := Vκ0 T Wν E p Z + ((T.eventL α E p t-T.L0 E p:ℝ):ℂ)
omit g t
lemma zero_vπ : vπ T Wν 0 E p (base0 O.pos) Z= Vκ0 T Wν E p Z:=by unfold vπ L0; rw [sub_self,Complex.ofReal_zero,add_zero]
include g t
lemma PI_step : denZ (T.D Wν α E p (vπ T Wν α E p t Z)) U Q.G₀ z= Real.exp (πH (Q:=Q) Wν α z) • stoneP T E p z:=by
 rw [T.meter_P Wν E p Z z g,T.SFS Wν α E p t z g,T.SFS Wν 0 E p (base0 O.pos) z g,← Complex.coe_smul, smul_smul,Complex.ofReal_exp,←Complex.exp_add]; refine congrArg (· • _) (congrArg Complex.exp ?_); rw [show πH (Q:=Q) Wν 0 z=0 from Wν.origin Q.X.p z.1]; unfold vπ L0; push_cast; ring -- unfolds not literally L0 RHS? tune
end Silo
end Act
end YM.CF.Py.Kay
