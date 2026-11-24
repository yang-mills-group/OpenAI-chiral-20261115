import YM.CF.DPress.Yarn.Grant
import YM.CF.Paxos.Port
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
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
variable (Z: Lore M B R A.μ)
abbrev VestM(M B:Side)(R:Patch):= ∀ j:ℕ,LogH (cell M B R.L j)
structure LedgerL (D:Crib F n) (Z: Lore M B R A.μ)(Y:StarPS n)(Q:VestM M B R):Prop where
 neck : Q n=0
 step : ∀ i:ℕ,i<n→ Spell D Z i (b_T D Y (i+1)) 0 (Q (i+1)) (Q i)
 paid : ∀ i:ℕ,i≤n→ D.stipend_h i (Q i) (Tew.tiny R (hat R.L x i)) none
 balance : ∀ i:ℕ,i<n→ D.b_T Y (i+1)+toll D i-(Q i).δ= D.b_T Y i
abbrev vint (Y:StarPS n)(Q:VestM M B R)(j:ℕ):= render D j (Q j) (b_T D Y j)
namespace LedgerL
variable {Y: StarPS n}{Q:VestM M B R}(p:LedgerL D Z Y Q)
include p
lemma POST : Pull_P V C.w C.p C.i (Ntop P_) Δ M F.legal n D.β J C.q' C.h P_.Rs (Ψs (P_:=P_)) F.Y (D.vint Y Q) (fun i=>(Q i).r) (fun i=>(Q i).δ):=by
 let W(i):= D.vint Y Q i; have he(i:ℕ)(g:i<n):= ((p.step i g).core D Z (p.paid (i+1) g)).2; constructor
 · intro i h z v; have ht:= (p.step i h).step D Z z v; rw [p.balance i h,(Z i).origin (Δ.a i) z.1,Real.exp_zero,one_smul] at ht; exact ht.symm
 · intro i h; exact (he i h).1
 · intro i h; exact (he i h).2.1
 · exact fun _ _=>⟨rfl,rfl,rfl,rfl⟩
 · intro i g; exact (essentially D (Q i) _ _ none).2 (p.paid i g)
 · intro i g; exact D.variant _ g
 · intro i h; have hp:= p.balance i h; unfold Crib.toll at hp; change D.b_T Y _-_- (D.b_T Y _- _)= _; linarith
 · change _ + (∑ i∈Finset.range 0, θ₁ R Y i)= D.β 0; rw [range_zero,sum_empty,add_zero]
 · unfold vint render; rw [p.neck]; rfl
lemma offsets (i:ℕ)(g:i<n) : ‖Complex.exp (D.vint Y Q (i+1)).v‖*F.c_ps i≤ ‖Complex.exp (D.vint Y Q i).v‖:= ((p.step i g).core D Z (p.paid _ g)).2.2.2
lemma Bri : Brioche V C.w C.p C.i (Ntop P_) Δ M F.legal n D.β J C.q' C.h P_.Rs (Ψs (P_:=P_)) (vint D Y Q) F.Y (fun i=>(Q i).r) (fun i=>(Q i).δ):=by
 refine ⟨p.POST D Z,D.head,F.bloom.tint,F.bloom.pose,fun i g=>D.variant Y g,F.rocket,?_⟩; intro j h; have hp(i:ℕ)(g:i<n): partitionZ (vint D Y Q i) U (F.Y i) = partitionZ (vint D Y Q (i+1)) U (F.Y (i+1)):=pU V _ _ _ _ Δ M F.legal n _ D.head J C.q' C.h P_.Rs _ F.Y F.rocket (vint D Y Q) _ _ (p.POST D Z) F.bloom.tint i g
 let Yv(i):= partitionZ (vint D Y Q i) U (F.Y i); have he(i:ℕ)(v:j ≤ i)(w:i ≤ n): Yv j=Yv i:=by
    induction i,v using Nat.le_induction with
    | base=> rfl
    | succ i u ih=> exact (ih (by omega)).trans (hp i w)
 exact he n h le_rfl
end LedgerL
open Cap
lemma root : ∃ Y Q, LedgerL D Z Y Q:=by
 obtain ⟨y,u,p,h⟩:= officeT D Z; let F0(c:StarPS n)(i:ℕ):ℝ:=(y i c).δ; let H:Cap.Clk (fun i=>Thrift.σ R) (fun i=>1) F0 (fun i:StarPS n=>fun j=>0) (fun _=>True):=by
    constructor; swap; · exact fun i h t=> ⟨zero_lt_one,continuous_const,fun c=> norm_zero.trans_le zero_le_one⟩
    intro i N T; refine ⟨Thrift.σpos (V:=V),(p i (by omega)).1.β, fun c=> ((Spell.core D Z ((p (i+1) N).2 c) (h i N c)).2.2.1).trans ((le_abs_self _).trans ((F.epoch i).δ))⟩ -- fun in tactics
 obtain ⟨Z',f⟩:=Cap.sit _ _ _ _ H; refine ⟨Z',fun i=> y i Z',⟨congrFun u Z',fun i h'=>h i h' Z', fun i v=> (p i v).2 _,?_⟩⟩; intro i w; rw [D.τ_T, show θ₁ R Z' i=(y i Z').δ from (f i trivial w).1,add_sub_cancel_right]
end Crib
end FitD
end YM.CF.Py.Kay
