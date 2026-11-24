import SatinThinParliament
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
-- arithmetic delivery & Versions
local notation "XP" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s
/- Parliament finances. -/
variable {I:Type} [Fintype I] [LinearOrder I]
local notation:max "Rn" s:max=> slotFee P s
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
local notation "ΞM"=>List (Article I)
-- first downward power. `Loyalty` reports exact density on the SAME sharp tape.
variable (o:I→Site (side Y i f))
local notation "Ƶ" s:max=> morning Y i k s
abbrev mark_cost (s: ℕ)(G:Mark (side Y i s)):= markedRead G (S s) (morning Y i k s)
local notation "Πξ" p:max=>upRoot Y i p
local notation "Ξν" s:max =>nightSet Y i s (I:=I)
local notation "ΞV" s:max=> rideSet Y i s (I:=I)
local notation:max "flightY" p:max=>convoy Y i k p
local notation "µ" s:max=> city (Ω s)
variable {E:nightSet (I:=I) Y i f}{F:rideSet (I:=I) Y i f}
variable (p:f≤v)
local notation "ψξ"=> artwork Y i k E F
abbrev principal (p: f ≤ v) (b:ℝ)(o:Site (side Y i f)):= routeTip Y i k b v (upRoot Y i p o)
local notation "ϕ" b:max=> principal Y i k p b
local notation "δ" s:max=> mark_cost Y i k s
structure Loyalty (a:ℝ)(E: Key (Article I)→ RegBudget (side Y i f))(F:Key (Article I)→ ForceBudget (side Y i f)):Prop where
 sky (l:List I)(u:l.Nodup): Version (µ f) (artwork Y i k E F (l.map Prin))
 grant (l:List I)(u:l.Nodup) (b:Mark (side Y i f))(z:AtSupport false univ b): markedRead b (S f) (artwork Y i k E F (l.map Prin))= mark_cost Y i k v (convoy Y i k p b*(l.map (principal Y i k p a ∘ o)).prod)
-- init.
local notation "αξ"=> clothTable (XP f).p (slotFee P f) o
local notation "fee" t:max j:max=>feeArr Y i k t (o j)
lemma init_frame(l:List I)(u:l.Nodup): artwork Y i k αξ 0 (l.map Prin)=fun t:Orbit (side Y i f)=> (l.map (fun j=>fee t j)).prod • (morning Y i k f t):=by
 funext x; have hp(l:List I): ((l.map (Prin:I→ Ξ)).map (beforeCost o (slotFee P f) (XP f).p x.1))=l.map (fun j=> fee x j):=by rw [List.map_map,show (beforeCost o (slotFee P f) (RootBook Y i k f).p x.1)∘(Prin:I→ Ξ)=fun j=>fee x j from funext fun j=> fee_absent (X:=RootBook Y i k f) (p:=o) (q:=Rn f) x.1 j]; -- wildcard infer beforeCost? 
 refine (before_gate (XP f) o (slotFee P f) P.V P.U (S f) (l.map Prin) ?_ x).trans ((congrArg (fun t:List ℂ=> t.prod • (morning Y i k f x)) (hp l))); exact u.map fun _ _ t=>congrArg QuadClock.host t
lemma spare_version (l:List I){F: Orbit (side Y i f)→Phys (side Y i f)}(p:Version (µ f) F) : Version (µ f) (fun t:Orbit (side Y i f)=> (l.map (fun j=> fee t j)).prod • F t):=by
 -- iter
 induction l with
 | nil=> simpa using p -- implicit function ext
 | cons i' l ih=> simp only [List.map_cons,List.prod_cons,←smul_smul]; exact prodV (fee_safe Y i k (o i')) ih
lemma expense_frame(l:List I){F: Orbit (side Y i f)→Phys (side Y i f)}(A:Mark (side Y i f)):
 markedRead A (S f) (fun t=> (l.map (fun j=> fee t j)).prod • F t)= markedRead (A * (l.map (chamber Y i k ∘ o)).prod) (S f) F:=by
 induction l generalizing A with
 | nil=> simp
 | cons j l ih=> simp only [List.map_cons,List.prod_cons,←smul_smul]; let p(t:Orbit (Ω f)):= (l.map (fun j=> fee t j)).prod • F t
                 rw [show markedRead _ _ _= _ from ring_toll Y i k (o j) (α:=p) A]; unfold p; rw [ih,←mul_assoc]; rfl
lemma start_frame (u:(VO).kick≤k)(x:f≤Y.uv k): Loyalty Y i k o (Nat.le_refl f) 1 αξ 0:=by
 refine ⟨fun l q=>?_,fun l q A p=>?_ ⟩
 · rw [init_frame Y i k o l q]; exact spare_version Y i k o l (morning_safe Y i k u x)
 rw [init_frame Y i k o l q,expense_frame Y i k o,convoy,climbing_refl,show principal Y i k (Nat.le_refl f) 1=chamber Y i k from funext fun q=> by simp only [principal,upRoot,climbing_refl]; rfl]
#print axioms start_frame
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
