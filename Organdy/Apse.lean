-- adapt stars Ticket
import YM.SU5.Exchange.Seed.Circle
import SatinThinBeacon
import YM.SU5.Exchange.Seed.Ship
import YM.SU5.Exchange.Seed.Station
import SatinThinPoles
import YM.CF.Roots.Sort
import YM.SU5.Exchange.Seed.Zero
import YM.SU5.Exchange.Seed.Keys
import YM.SU5.Exchange.Seed.Marks
import YM.CF.Rive.New
import YM.CF.Song.Pads
import SatinThinTopic
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog
open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open Roots Py
open scoped YM.CF.Mew
-- high-Key entries together.W.pricing with only η of order reciprocal B
variable {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n) {t:ℕ}(p:Force_M P.B σ t)
variable (E:Key I→RegBudget n)(F:Key I→ForceBudget n)
variable (he:∀ X:Scree.Hub n,Hush σ X.val.2 (fun z=> E z X) ∧ ∀ u,River (fun z:Key I=> E z X u))
variable (hf:∀ X:Force n,Hush σ X.val.1.val.2 (fun z=> F z X) ∧ ∀ u,River (fun z:Key I=> F z X u))
variable (z:Key I) (c':ℝ)(hp:∀ i, ‖z i‖≤ c') (δ X:ℝ)(hc:1 ≤ c') (cv:2*c' ≤ Real.exp X) (hA:0 ≤ X)(hδ:0 ≤ δ) (hV:0 < h)
local notation "A₁"=> manySet σ
local notation "A₂"=> trueSet σ
local notation "Zξ"=> sigma δ P.B
local notation "pτ"=>P.supportExponent
private lemma reserved {J:Type}[DecidableEq J][Fintype J](f:J→ℝ)(x:J):
 ∑ i:J,(if i=x then 1 else (0:ℝ)) * f i=f x:=by rw [Finset.sum_eq_single x]; rw [if_pos rfl,one_mul]; intro b _ t; rw [if_neg t,zero_mul]; simp

def mixedForce (F:Key I→ForceBudget n)(z:Key I) : ForceBudget n:=∑ j∈manySet σ, pine j z • νΦK F j
include hf
lemma hushForce (j:Finset I) (i:Force n) (t:¬j⊆ sits_at σ i.val.1.val.2):
     νΦK F j i=0:=by
    have hr(t):= (hf t).2
    obtain ⟨x,p,v⟩:= Finset.not_subset.mp t
    let q:= (hf i).1; funext U; exact Neon.husht_B _ _ _ (show Hush σ i.val.1.val.2 (fun z=>F z i U) from fun a b t x p=>congrFun (q a b t x p) U) (hr i U) (Mew.Cue I j) x (fun s=>v (mem_filter.mpr ⟨mem_univ _,s⟩)) (by simpa [Mew.Cue] using p)
include hV
variable (K: Force n→ℝ)(t0:∀ z∈hill I, ∀ i, ForceB P i (F z i) h (K i))
include t0
lemma rateForce (s:Finset I) (j:Force n):ForceB P j (νΦK F s j) h (K j):=by
 let f(i j:Force n):ℝ:= if i=j then 1 else 0
 have hr(t):= (hf t).2
 have hW(z:Finset I)(i:Force n): ForceB P i (νΦK F z i) h (K i):=by
    obtain ⟨k,u,v⟩ := (insight_t F hV f (fun i j=>by unfold f; split <;> norm_num) (fun i=>⟨i,by unfold f; simp⟩) K (fun z e=>⟨⟨K,t0 z e,fun i=>(reserved K i).le⟩⟩) hr (Mew.Cue I z)).bit
    let s0:=u i; obtain ⟨t1,t2,t3,t4,t5,t6,y,t7,t8,t9⟩:=s0; exact ⟨t1,t2,t3,t4,t5,t6,y,t7,t8,t9.trans ((reserved k i).symm.trans_le (v i))⟩

 exact hW s j
include p hp hc cv hA hδ
lemma mixedService (u:∀ j:Seat n,(∑ i:Force n,giftK P (P.supportExponent+δ) i j*K i) ≤ a)(w:9*X*t ≤ (δ/2)*(P.B:ℝ)^2): Dark primeU (mixedForce σ F z) P h (sigma δ P.B*a):=by
 let f(i j:Force n):ℝ:= if i=j then 1 else 0
 have hr(t):= (hf t).2
 have hW(z:Finset I)(i:Force n): ForceB P i (νΦK F z i) h (K i):=by
    obtain ⟨k,u,v⟩ := (insight_t F hV f (fun i j=>by unfold f; split <;> norm_num) (fun i=>⟨i,by unfold f; simp⟩) K (fun z e=>⟨⟨K,t0 z e,fun i=>(reserved K i).le⟩⟩) hr (Mew.Cue I z)).bit
    let s0:=u i; obtain ⟨t1,t2,t3,t4,t5,t6,y,t7,t8,t9⟩:=s0; exact ⟨t1,t2,t3,t4,t5,t6,y,t7,t8,t9.trans ((reserved k i).symm.trans_le (v i))⟩
 have hpK(i:Force n):0 ≤ K i:= Roots.gradeQ _ _ (hW ∅ i) hV.le
 let wξ (i:Force n):= ((A₁).filter (·⊆ sits_at σ i.val.1.val.2))
 have hz(i:Force n)(j:Finset I)(l:j∈A₁)(w:j∉wξ i):νΦK F j i=0:=by
    have t:¬ j ⊆ sits_at σ i.val.1.val.2:= fun v=> w (mem_filter.mpr ⟨l,v⟩)
    obtain ⟨x,p,v⟩:= Finset.not_subset.mp t
    let q:= (hf i).1; funext U; exact Neon.husht_B _ _ _ (show Hush σ i.val.1.val.2 (fun z=>F z i U) from fun a b t x p=>congrFun (q a b t x p) U) (hr i U) (Mew.Cue I j) x (fun s=>v (mem_filter.mpr ⟨mem_univ _,s⟩)) (by simpa [Mew.Cue] using p)
 let uX(i:Force n):= (∑ j∈wξ i, ‖Mew.pine j z‖*K i)
 refine ⟨⟨uX,fun i=> ?_,fun j=>?_⟩,fun i p=>False.elim p⟩
 · unfold mixedForce; rw [Finset.sum_apply, ←sum_subset (filter_subset (fun i'=> i'⊆ sits_at σ i.val.1.val.2) (A₁)) (fun j l t=> ?_)]
   · exact dom_K_fin _ _ _ _ (fun j _=> dúe _ _ (hW j i) (Mew.pine j z))
   change Mew.pine j z • νΦK F j i=0; rw [hz i j l t,smul_zero]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (u j) (Real.exp_pos _).le); rw [mul_sum]; refine Finset.sum_le_sum (fun i _=> ?_)
 unfold giftK; split_ifs with g; swap; · simp
 unfold BudgetPoint.mass uX; rw [←sum_mul]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (stars σ t p i.val.1.val.2 j g z c' hp δ X hc cv hA hδ w) (hpK i)) (Real.exp_pos _).le).trans (le_of_eq ?_)
 unfold Trees.currency; rw [add_mul,Real.exp_add]; ring

omit p hp hc cv hA
lemma fixedService (u:∀ j:Seat n,(∑ i:Force n,giftK P (P.supportExponent+δ) i j*K i) ≤ a)
   (r:I): FixedF P h a (νΦK F {r}):=by
   let L(x:Force n):= if σ r∈ x.val.1.val.2 then K x else 0
   have hW(z:Finset I)(i:Force n): ForceB P i (νΦK F z i) h (K i):=rateForce σ F hf hV K t0 z i
   have hpK(i:Force n):0 ≤ K i:= Roots.gradeQ _ _ (hW ∅ i) hV.le
   refine ⟨L,fun i=>?_,le_trans ?_ (u (σ r))⟩
   · unfold L; split
     · exact hW _ _
     rename_i e
     rw [hushForce σ F hf _ _ (fun g=>e (mem_filter.mp (g (mem_singleton_self _))).2)]
     exact Vale.rinsed ..
   refine sum_le_sum fun i _=>?_
   unfold L giftK; split_ifs
   · exact le_mul_of_one_le_left (hpK i) (Real.one_le_exp
      (mul_nonneg (add_nonneg P.exponent_pos.le hδ) (Nat.cast_nonneg _)))
   rw [zero_mul]
end TreasuryFog
end YM.CF.Vow
