import YM.CF.Py.Line
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
variable{B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a α:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W) (M:Side)(ht:T.q ≤ M.val)(l0:ℕ)
local notation "L'"=>R.L
abbrev bell_v: V.L.Last U W.C M l0:= W.arm (T.large.trans ht) l0
local notation "bell"=>bell_v V a p i N0 T M ht l0
variable (B0:ℕ→ℝ)
structure Due :Prop where
 unit:B0 0=x
 fee(j:ℕ):j<l0→ B0 j=B0 (j+1)+ (W.arm (T.large.trans ht) l0).move j
 space(j:ℕ):j≤l0→matchedX (hat R.L x j) (B0 j)
-- station post anchor X=_Mint exact. x chosen l. upper→lower uses irreversible ticket
abbrev hueR (j:ℕ):GramM (cell M B R.L j):=⟨T.a j,V.L.path (l0-j),K.top.clip,B0 j,(W.arm (T.large.trans ht) l0).Q j,0,0,0,0⟩
local notation "hF"=>hueR V a p i N0 T M ht l0 B0
-- enforce bare launch. congr defs
lemma hue_top: hueR V a p i N0 T M ht l0 B0 l0=Vale.launch V.L (B0 l0) (T.a l0) _:=by unfold hueR Vale.launch; rw [Gold.Last.top,Nat.sub_self]
-- bottom size certified.v=q; old Y from registry. specialize stage calendar.(clock)
variable (Y:Due V a p i N0 T M ht l0 B0)
variable {v w:ℕ}(A0:ℕ)
local notation "Xc"=> cell M B R.L
local notation "aptX"=> apt M B R.L
local notation "Px"=>V.L.op (l0-1-j) (kint M B R.L j)
structure Costume {n:Side}(X R:GramM n) :Prop where
 reset : ∃ F A v, R=PoleR X F A v
variable (c:GramM (cell M B R.L (A0+1)))(J:Costume (hueR V a p i N0 T M ht l0 B0 (A0+1)) c)
include T ht
lemma flat_v(j v:ℕ): N0*radiusB (hat R.L x j) ≤ (More (cell M B R.L j)).val:=by
 have he:= (T.clear ht v j).2.2; rw [(T.boot _).2.1] at he; exact ((Nat.mul_le_mul_left N0 (show radiusB _ ≤ 1+radiusB (hat R.L x j) from Nat.le_add_left ..)).trans he).trans (by change _ ≤ (cell M B R.L j).val*2; omega)
include J Y
lemma sized_s (p': A0<l0):StatV V (apt M B R.L A0) (V.L.mint (l0-1-A0) (kint M B R.L A0)) U W (hueR V a p i N0 T M ht l0 B0 A0) c (V.L.charge (l0-1-A0)) ((W.arm (T.large.trans ht) l0).shift A0) a (hat R.L x A0) p i:=by
 let J0:= l0-1-A0; let P:= V.L.op J0 (kint M B R.L A0); let G:= apt M B R.L A0; let t':= T.clear ht J0 A0; have hv:J0=l0-(A0+1):=by unfold J0; omega
 obtain ⟨F,K1,T0,Kq⟩:= J.reset; rw [Kq]
 let W':= W.arm (T.large.trans ht) l0; have ht':=T.boot A0; have hu:= T.boot (A0+1); have hp: T.q ≤ (cell M B R.L A0).val:= ht.trans (Vale.amplit ..)
 refine ⟨?_,T.roll _,W'.pass A0 p', W'.sound _,t'.2.1,ht'.2.2.1,hu.2.2.1,?_,?_,rfl,rfl,Y.fee A0 p', ?_,ht'.2.1,?_,hu.2.2.2.2⟩ -- power ; fee' crystal
 · exact Stake.punt_g V J0 _ G rfl _ (by have hh:=W.flag.trans (T.large.trans hp); change _≤ (cell M B R.L A0).val*2; omega) t'.1.size
 · exact congrArg V.L.path (show l0-A0=J0+1 by omega)
 · exact congrArg V.L.path hv.symm -- y.p
 · have he:= Y.space (A0+1) (by omega); rw [hat_succ] at he; exact he
 change (T.a _).B=_; rw [hu.2.1,hat_succ]; rfl
end YM.CF.Py
