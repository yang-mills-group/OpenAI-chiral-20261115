import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
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
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k:ℕ) {P' V: Side} {f r t v :ℕ}
local notation "B"=> P.block
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "X_" s:max=> RootBook Y i k s
local notation "µ" s:max=> city (Ω s)
variable {I J G:Type} [Fintype I] [Fintype J][LinearOrder I][LinearOrder J] [LinearOrder G]
variable (p:(Y.voyage i).kick≤ k)
local notation "ν"=> Y.uv k
local notation "θ"=> P.R.L
variable (w:I→G)(X: HousingJ Y i G)(K:G→Prop)(t:f ≤Y.uv k)(E: List I→Orbit (side Y i f)→ Phys (side Y i f))(A:I→Mark (side Y i (Y.uv k)))
variable {N:Side}
variable (σ:I→Seat (side Y i f))(R:I→I→ℂ)
variable (vP:κWork G (Seat (side Y i f)) w σ)
local notation "κ0"=> RevenueT Y i k
local notation "ƒ"=> convoy Y i k t
local notation "Gc"=> city (side Y i (Y.uv k))
abbrev safeJ {N:Side}:= PostSupport (M:=N) false univ
include p
lemma decid_JT (U:I→Mark (side Y i (Y.uv k)))(T:Finset I)(v:∀ i∈T,safeJ (U i)): κ0 (∑ i∈T,U i)= ∑ j∈T, κ0 (U j):= cost_sumJ Y i U T _ v (morning_safe Y i k p le_rfl)
omit p
lemma spunT (U:Mark (side Y i (Y.uv k)))(z:ℂ): κ0 (z • U)= z • κ0 U:=palm_scale ..
lemma cons_JT (U:I→ Mark (side Y i (Y.uv k)))(p: ∀ i,safeJ (U i))(S: List I): safeJ (S.map U).prod:= by induction S with | nil=> exact PostSupport.of (AtSupport.oneM _)| cons i l ih=> exact (p i).mulM ih
lemma twist0T (q:Entourage Y i k w X K t E A)(E':List I→ Orbit (side Y i f)→Phys (side Y i f))(g0:∀ l:List I,galaJ w l → E' l=ᵐ[city (side Y i f)] E l): Entourage Y i k w X K t E' A:=⟨q.stamped,fun l v=>(q.lease _ v).cong (g0 _ v).symm,fun l v _ _ u=> (read_version _ _ (g0 _ v)).trans (q.fare _ v _ _ u)⟩
local notation "V'"=>perturbJ Y i σ A R
variable (q0:Listos Y i w X K (Y.uv k) A)(B':Mark (side Y i (Y.uv k)))(hB:safeJ B')
-- all Word prices, no commutation
include p hB q0 vP
lemma ceilingK (L':List I): κ0 (B'*(L'.map V').prod) = Roots.snow σ R (fun l=>κ0 (B'*(l.map A).prod)) L':=by
 let G:= V'; have ht:= q0.perturb Y i k w X K A σ R vP -- tune dot
 induction L' generalizing B' with
 | nil=> rfl
 | cons j l ih=>
    rw [List.map_cons,List.prod_cons, ←mul_assoc]; change κ0 (B'*(∑ i'∈pipe_ζ σ j, R i' j • A i') * (l.map G).prod)=_; simp_rw [Finset.mul_sum,Finset.sum_mul, Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
    rw [decid_JT _ _ _ p,Roots.snow]; swap
    · intro i' v; exact (show safeJ (B'*A i'*(l.map G).prod) from (hB.mulM (q0.owns _)).mulM (cons_JT Y i k G ht.owns l)).smulM _
    refine sum_congr rfl fun i' v=> ?_
    rw [spunT]; refine congrArg (R i' j • ·) ?_; refine (ih (B'*A i') (hB.mulM (q0.owns _))).trans ?_; apply Roots.rer; intro t _; rw [List.map_cons,List.prod_cons,mul_assoc] -- vB
omit hB q0
lemma coast_J (p0:Entourage Y i k w X K t E A) : Entourage Y i k w X K t (turnoverJ Y i σ E R) V':=by
 have hp(L T:List I)(g:galaJ w L)(v:T.map σ=L.map σ):galaJ w T:=by unfold galaJ; rw [fondΩ Y i w σ vP T _ v]; exact g
 have h(L:List I)(p:galaJ w L)(T:List I)(g:T.map σ=L.map σ):=p0.lease T (hp _ _ p g)
 refine ⟨p0.stamped.perturb Y i k w X K A σ R vP,fun l v=> permit_S Y i σ R l _ (h _ v),fun l v C W T=>?_⟩
 obtain ⟨pW,tU⟩:=T
 let U:= convoy Y i k t W; have hc:safeJ U:=PostSupport.of (convoy_all Y i k p t le_rfl (tU.mono (subset_univ _)))
 rw[red_bill Y i σ R l E W tU.env (h l v),ceilingK Y i k p w X K A σ R vP p0.stamped U hc] -- order tune k
 apply Roots.rer; intro L' vL; exact p0.fare L' (hp _ _ v vL) C W ⟨by rw [fondΩ Y i w σ vP L' _ vL]; exact pW,tU⟩
#print axioms coast_J
#check Listos.perturb
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
