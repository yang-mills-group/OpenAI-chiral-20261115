import YM.CF.DPress.Year.Scope
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
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
namespace Privilege
open Chess Wall Sermon Thrift RoomF Crib
open scoped YM.CF.BPress ComplexOrder
variable {F: RoomF J Λ M Δ}{D:Crib F n}{Z:Lore M B R A.μ}
 {Q:Source P_ J}{Y:StarPS n}{Z0:VestM M B R}
 {T: LedgerL D Z Y Z0}{Jp:ℕ→ℝ→ℝ}
 {ℓ k':ℕ}(G:Fixes Q D Z Y Z0 T Jp k)
open Wagon
open BPress (Bands) -- separate opens
open ScopeD
variable (p:Grip J ℓ k')(t:Told F)(v:Articles Z)
namespace Limit
local notation "N" i:max => cell M B R.L i
-- time index admitted when b+1 deeper than fixed level.
def Age (T:Source P_ J) (i n:ℕ):Prop:= i+(T.b+1)≤ n
lemma Age.side (Q:Source P_ J)(i:ℕ):∀ᶠ n:ℕ in atTop, Age Q i n:= eventually_ge_atTop _
variable (S:Chrono F Z)(Q) (Jp)
abbrev TruthX(i n:ℕ):= BPress.reading U (S.Truth n i) (F.Y i)
abbrev trueX(i n:ℕ)(F':Fixed.Test (cell M B R.L i)):= ‖TruthX S i n F'‖
abbrev εB (Λ:Thrift A) (T0:Source P_ J) (Δ:ΛFit P_ x)(M:Side)(i n:ℕ):= ScopeD.fee Λ Δ M i (n-T0.b-1)
lemma realD {S:Chrono F Z}(Q: Source P_ J)(n i:ℕ)(c:ℝ)(p:Age Q i n)(Y:S.Aux Q Jp n):∀ F': Fixed.Test (N i), Measurable F'→(∀ i,‖F' i‖≤ c)→ ‖BPress.reading U (Y.bot i) (F.Y i) F'-TruthX S i n F'‖≤ c* εB Λ Q Δ M i n:=fun f t v=>costs Y (by unfold Age at p; omega) c f t v -- tune can't shim Jp binder
include S
lemma err (i:ℕ): Tendsto (fun n:ℕ=> εB Λ Q Δ M i n) atTop (𝓝 0):=by
 let p:= Q.b; have hf(n:ℕ):εB Λ Q Δ M i n=Quant.CostP (Λ:=Λ) (Δ:=Δ) M i*Crib.μx Λ x (n-(p+1)) i:=by rw [εB,ScopeD.fee,show n-Q.b-1=n-(p+1) from (by unfold p; omega)]
 simp_rw [hf]; simpa using (Quant.poster (S.D 0) (i:=i) (p+1)).const_mul (Quant.CostP (Λ:=Λ) (Δ:=Δ) M i)
include Q
variable (pF:Source.Workshop Q Λ Jp x)
include v pF
-- These two assertions express the UV error used throughout -- every competitor; budgets buy any pre-uniform-in-n sup bound on tests; convergence only at M fixed. 
theorem αUV(i:ℕ)(c:ℝ) {ε:ℝ}(h:0<ε):∀ᶠ n:ℕ in atTop, Nonempty (S.Aux Q Jp n) ∧ Age Q i n ∧ ∀ Y:S.Aux Q Jp n,∀ f: Fixed.Test (N i), Measurable f→(∀ i, ‖f i‖≤c)→ ‖BPress.reading U (Y.bot i) (F.Y i) f-TruthX S i n f‖< ε:=by
 have ht:= (err Q S i).const_mul c; rw [mul_zero] at ht; filter_upwards [Age.side Q i,ht.eventually (gt_mem_nhds h)] with n p t; have hv:c*εB Λ Q Δ M i n< ε:= t; exact ⟨S.go Q Jp n (by unfold Age at p; omega) pF (stack_P v),p,fun Y f u w=> (realD Q (Jp:=Jp) n i c p Y f u w).trans_lt hv⟩ -- interface tune
end Limit
end Privilege
end FitD
end YM.CF.Py.Kay
#print axioms YM.CF.Py.Kay.FitD.Privilege.Limit.αUV
