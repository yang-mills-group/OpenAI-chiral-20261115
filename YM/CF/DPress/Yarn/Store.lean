import YM.CF.DPress.Act.LPC
import YM.CF.Tar.Dome
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
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
-- ordinary schedule $s,size functions.Litt ... before lambda grant always stores.Hermes
structure Align (C:Tew W)(J:Robes M' V W):Prop where
 one : C.M₀=J.n
 point : C.kL = J.d
 νs : C.dS=J.roomX
 v0 : C.vS = J.k
abbrev Ntop(P_:Campus C):= C.n₀ + P_.μN
abbrev ΛFit (P_:Campus C) (x:ℝ):= Month x C.w C.i C.p (Ntop P_) V W
abbrev ηD:= A.C_D * (R.L.val:ℝ)⁻¹
structure Thrift (A:Harvester P_) where
 w:ℝ→ℝ
 O:ℝ→ Shore0
 ξ : ℝ→ℝ
 getW : ∀ x,w x = (O x).δ
 he : ηD (A:=A) ≤ 1/4
 posBoring : 20 * A.μ < R.L.val
 hp : Litt R 2 (χCost (C:=C) ξ)
 rtD : Chill_v (Ψs (P_:=P_))
 ζS : sizeK R.L 2 P_.Rs
 ζM : sizeK R.L 2 (fun x=>P_.rM (O x))
namespace Thrift
variable (Ω: Thrift A)
abbrev η := ηD (A:=A) -- not include Ω . ok.
abbrev named := Ψs (P_:=P_)
abbrev σ (R:Patch):= billX R.L /16
structure Past (X:ℝ): Prop where
 tax : Festival A X Ω.ξ (Ω.O X)
 δ : |Ψs (P_:=P_) X| ≤ σ R
 fall(y:ℝ): X≤y→ Ω.w y ≤ Ω.w X
 tiny(y:ℝ): X≤y→ Tew.tiny R y ≤ Tew.tiny R X
 wide : 6≤ radiusB X
structure Credit (X:ℝ) :Prop where
 hp0 : 0<X
 fax : 8*W.z ≤ X
 period : 20*(A.μ+10) < (grainZ V W (Ntop P_) X) -- admission>=general? eq:core in Month
 earn : ∀ t:ℝ,X ≤ t → Past Ω t
include V in
lemma σpos : 0 < σ R:=by unfold σ; have he:= billx_T V; unfold ν_PS at he; linarith -- need include V
lemma ηpos : 0< ηD (A:=A):= mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left ..)) (by positivity) -- include Ω? not
lemma EMark {Z:ℝ→ℝ}(z:sizeK R.L 2 Z)(t:∀ i,0≤ Z i)(v:∀ᶠ i in atTop,∀ y,i≤y → Z y≤ Z i)(h:∀ᶠ i:ℝ in atTop,4*Tew.tiny R i≤ Z i)(u:ηD (A:=A) ≤ 1/4)(p:20*A.μ<R.L.val):∃ Ω:Thrift A,Ω.w=Z∧∀ᶠ i in atTop, Thrift.Credit Ω i:=by
 obtain ⟨D,ξ,q,Q,w,s,e,f⟩:= festival A z t h; let Ω:Thrift A := ⟨Z,D,ξ,fun i=>(q i).symm,u,p,Q,w,s,e⟩
 obtain ⟨i,p,t⟩:= glimp_T (R:=R); have h:∀ᶠ j in atTop, Thrift.Past Ω j:=by
    filter_upwards [f,v,eventually_ge_atTop i,w.spine_a.abs.eventually (ge_mem_nhds (show |(0:ℝ)|<σ R by rw [abs_zero]; exact σpos (V:=V))), Work.E01.radiusB_tendsto.eventually_ge_atTop 6] with j q w v h Y; exact ⟨q,h,w,fun x p=> ((t _ v).2.2 _ p).1, Y⟩ -- syntax t from glimp
 obtain ⟨T,t⟩:= eventually_atTop.mp h
 refine ⟨Ω,rfl,?_⟩; let Q:=20*(A.μ+10); filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (Q+1), eventually_ge_atTop T,eventually_gt_atTop (0:ℝ),eventually_ge_atTop (8*W.z)] with x F M N G; refine ⟨N,G,?_,fun i p=> t i (M.trans p)⟩
 unfold grainZ; have hk: (1+radiusB x) ≤ (100+Ntop P_)*(1+radiusB x):= Nat.le_mul_of_pos_left _ (by omega); unfold Q at F; omega
include Ω
lemma η_upper {u:ℝ}(p:0 ≤ u): A.meter u≤ u:= by apply le_trans (mul_le_mul_of_nonneg_right Ω.he p); linarith
end Thrift
end FitD
end YM.CF.Py.Kay
