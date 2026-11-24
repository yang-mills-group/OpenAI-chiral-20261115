import SatinThinPremier
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
local notation "Πξ" p:max=>upRoot Y i p
local notation "Ξν" s:max =>nightSet Y i s (I:=I)
local notation "ΞV" s:max=> rideSet Y i s (I:=I)
local notation:max "flightY" p:max=>convoy Y i k p
local notation "µ" s:max=> city (Ω s)
variable {E:nightSet (I:=I) Y i f}{F:rideSet (I:=I) Y i f}
variable (p:f≤v)
local notation "ψξ"=> artwork Y i k E F
local notation "ϕ" b:max=> principal Y i k p b
local notation "δ" s:max=> mark_cost Y i k s
/- Mark family billed. Growth on the gap compensated relative to EVERY mark carried. -/
variable (b z t:ℝ) (j:I) (x:f≤r)(v':r ≤ v)
-- notation p f ≤v auto included if mention; prefer use trans explicitly. project `routeTip`: Rank z. principal `z` currently to use b param. Tilt `a=accum from r...`. 
noncomputable abbrev carried (o:Site (side Y i f)):= principal Y i k (le_trans x v') b o
noncomputable def extra_δ (o:Site (side Y i f)): Mark (side Y i v):=convoy Y i k v' (chamber Y i k (upRoot Y i x o))
def signalMark (b:ℝ)(x:f≤r)(v':r≤v) (z:ℝ)(o:Site (side Y i f)):Mark (side Y i v) := principal Y i k (le_trans x v') (b*z) o -- order conven
-- choose gap formula z • R' but inside dyadic rather than b*z vector; later simp. Γθ powers real. 
def gapMark (b:ℝ)(z:ℝ)(x:f≤r)(v':r≤v)(o:Site (side Y i f)):Mark (side Y i v):= (↑(zoomM L^(r-f)):ℂ) • ((z:ℂ) • principal Y i k (x.trans v') b o-extra_δ Y i k x v' o)
noncomputable def menuClock (q:Article I):Mark (side Y i v):=let x':= o (QuadClock.host q); if layer q=0 then (↑t:ℂ) • principal Y i k (x.trans v') b x' else gapMark Y i k (x:=x) (v':=v') b z x'
#print menuClock
local notation:max "H" b:max z:max t:max u:max p:max=> menuClock Y i k o b z t u p
local notation "g" x:max b:max z:max=> gapMark Y i k (x:=x) (v':=v') b z
local notation:max "qZ" b:max=> principal Y i k (le_trans x v') b
lemma menu0 : H b z t x v' (Prin j)= (↑t:ℂ) • qZ b (o j) := by unfold menuClock; simp only [show layer (Prin j)=0 from rfl,ite_true]; rfl
lemma menu1 : H b z t x v' (Astr j)= gapMark Y i k (x:=x) (v':=v') b z (o j) := by unfold menuClock; simp only [if_neg (show layer (Astr j)≠0 from by show (1:Fin 2)≠0; decide)]; rfl
-- Mark identity across a step.
variable (y:f<r)(U:Funds P.R.L)
local notation:max "Πκ" u:max=>menuClock Y i k (f:=f+1) (heel (Gξ f)∘ o) b z t u v'
local notation "Tξ" s:max=> (TicketM L U)
local notation "Dξ"=> re_p L (r-(f+1)) t z U.adjustment
#print gapMark
#check re_p
-- `appeal` requires imports; do point
lemma name_θ (q:Article I): TicketM L U (toPrin q) q • (Πκ y (toPrin q))+ TicketM L U (toGap q) q • (Πκ y (toGap q))= H b Dξ (U.ticket * t) y.le v' q :=by
 let d1:=U.adjustment; let u:=U.ticket; let d0:=zoomM L; let N:=r-(f+1); let DU:= re_p L N t z U.adjustment -- D conflict.
 let N':= side Y i v; let J:=Πκ y; let J':= H b Dξ (U.ticket*t) y.le v'; let T (i j:Article I):=TicketM L U i j; change (T _ q) • J (toPrin q)+T _ q • J _=J' q
 have he(j:I):principal Y i k (f:=f+1) (le_trans (show f+1≤r from y) v') b ((heel (Gξ f) ∘ o) j)=principal Y i k (le_trans y.le v') b (o j):= congrArg (routeTip Y i k b v) (climbing_step (X:=fun s=> Site (side Y i s)) (fun t=>heel (Vale.apt (Y.ir i) P.block P.R.L t)) (o j) (y.trans_le v')).symm
 refine art_fork (p:=fun q=> T (toPrin q) q • J (toPrin q)+T (toGap q) q • J (toGap q)=J' q) (fun j=>?_) (fun j=>?_) _
 · let p:= Prin j; unfold J J'; have hz:T (toGap p) p=0:=by change (↑(moveCost L U 1 0):ℂ)=_; rw [(move_zeroes L U).1,Complex.ofReal_zero]
   rw [hz,zero_smul,add_zero,show toPrin (phaseMark j 0)= Prin j from rfl,menu0,show phaseMark j 0=Prin j from rfl,menu0,he j,smul_smul]; push_cast; rfl
 let p:=Astr j; let Pj:=principal Y i k (le_trans y.le v') b (o j); let A:=extra_δ Y i k y.le v' (o j); change (↑(d0*d1):ℂ) • (Πκ y (Prin j))+ (d0:ℂ) • (Πκ y (Astr j))= H b Dξ (U.ticket * t) y.le v' (Astr j)
 rw [menu0,menu1,menu1]; unfold gapMark; rw [he j, show extra_δ Y i k (show f+1≤r from y) v' ((heel (Gξ f)∘ o) j)=A from congrArg (fun t=> convoy Y i k v' (chamber Y i k t)) (climbing_step (X:=fun m=> Site (side Y i m)) (fun m=> heel (Vale.apt (Y.ir i) P.block P.R.L m)) (o j) y).symm, show r-f=N+1 from by unfold N; omega]
 let w:= (DU:ℂ); have pp: d0^N*(DU:ℝ)= d0^N*z+d1*t:=by
    unfold DU re_p; change d0^N*(z+d1*t/d0^N)=_; have h:0<d0:= zoomM_p L; field_simp
 change (↑(d0*d1):ℂ) • ((t:ℂ) • Pj)+(d0:ℂ) • ((↑(d0^N):ℂ) • ((z:ℂ) • Pj-A))=(↑(d0^(N+1)):ℂ) • ((DU:ℂ) • Pj-A)
 let V:ℂ:=d0; have ht:(d0:ℂ)^N*(DU:ℂ)=(d0:ℂ)^N*z+(d1:ℂ)*t:=by exact_mod_cast pp
 push_cast; rw [pow_succ']; simp_rw [smul_sub, smul_smul]; -- coefficients tactic modules
 rw [mul_assoc ↑d0 _ (DU:ℂ),ht]; module
#print axioms name_θ
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
