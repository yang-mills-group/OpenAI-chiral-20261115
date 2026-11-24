import YM.SU5.Exchange.Seed.Flow
import YM.CF.Stax.Render
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z b:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)} (T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> uChip z b r
variable (w:0≤h)(x:Orbit n)(p:FleetS P.threshold x.1)
variable (A:∀ X: Aura n,Fray P h δ X ∅ (K X ∅ X 1) (b X))
open PowerSeries
lemma Fray.zeroP (P:BudgetPoint)(L:ℝ)(d:ℕ)(X:Aura n)(D:Support (More n)):Fray P L d X D 0 0:=⟨Medal.zeroT,fun i p=>False.elim (p rfl)⟩
lemma Fray.addP {P:BudgetPoint}{h:ℝ}{d:ℕ}{X:Aura n}{D:Support (More n)}{F G:Copy n}{A B:ℝ}(p:Fray P h d X D F A)(q:Fray P h d X D G B): Fray P h d X D (F+G) (A+B):=by
 refine ⟨Medal.plus p.merit q.merit,fun i l=>?_⟩; by_cases t:F i=0
 · exact q.loaf i (fun x=>l (by simp [t,x]))
 exact p.loaf i t

-- adapted from Stax.fed: derivative barrier distinguishes two kernel costs.
include T w hF A
lemma Fray.shell (X:Aura n)(D:Support (More n))(u:D⊆ X.val)(i:ℕ): Fray P h δ X D (coeff i (Q X D)) (coeff i (N X D)):=by
 induction i using Nat.strong_induction_on generalizing X D with
 |h i ih=>
   cases i with
   |zero=> rw [Cadre.peg,uPeg]; exact hF _ _ u
   |succ i=>
    nth_rw 1 [Cadre.peel]
    rw [uRule,Cadre.sprig,Cadre.sprig,Cadre.pingT _ _ _ _ T.start,uCost]
    rw [show ∀ v:ℝ,((i:ℝ)+1)⁻¹ • v= ‖((i:ℝ)+1)⁻¹‖*v from fun v=> by rw [smul_eq_mul,Real.norm_of_nonneg (by positivity)]]
    apply Fray.smulF; rw [map_add,map_add,map_sum,map_sum]; apply Fray.addP
    · unfold Cadre.moss; split_ifs with p; · rw [map_zero,map_zero]; exact Fray.zeroP ..
      rw [coeff_C, coeff_C]; split; · rw [not_nonempty_iff_eq_empty.mp p]; exact A _
      exact Fray.zeroP ..
    apply Fray.sumP; intro Y _; rw [rils,rils]; apply Fray.sumP; intro G l; let q:= (mem_inter.mp l).1; have s: X.val=Y.val∪robe G:=((drum_p ..).mp q).2.2
    apply T.plays _ _ u _ (s ▸ subset_union_left); rw [coeff_prod,coeff_prod]; apply Fray.sumP; intro k v
    exact Fray.vert _ q _ _ (fun j t=>ih (k j) (Nat.lt_succ_of_le ((single_le_sum (fun k _=> Nat.zero_le _) t).trans_eq (mem_finsuppAntidiag.mp v).1)) _ _ inter_subset_right) w -- tune

def layerN (i:ℕ)(X:Aura n)(D:Support (More n)):Copy n:= ∑ m∈range (i+1),coeff m (Cadre.chip K F X D)
def paidLayers (i:ℕ)(X: Aura n)(D:Support (More n)):=∑ m∈range (i+1),coeff m (N X D)
lemma paidN (i:ℕ)(X:Aura n)(D:Support (More n))(u:D ⊆ X.val) : Fray P h δ X D (layerN F K i X D) (paidLayers r z b i X D):=
 Fray.sumP _ _ _ fun i _=>Fray.shell F r hF K z b T w A X D u i
omit hF T A w
lemma chargeLayers(i:ℕ) {W c t e s κ L G:ℝ}(B:Aura n→ℝ)(U:Timer (uChip z b r) z κ L W B s G c t e 1 b)(X:Seat n): nook ((roofL (paidLayers r z b i) κ)*loom_v L W B 1) X ≤ G:= by
 have hh:= U.book X 1 ⟨zero_le_one,le_rfl⟩ i; unfold serif seed_v bark mintL at hh; simp_rw [one_pow,one_mul] at hh; exact hh
-- lantern.Coeffs
local notation "Ωx"=> flags P.threshold x.1
local notation "Zq"=> cumQ F K x P
include hF T w p
open Sault
-- act derivative exact. requires at x:Orbit via Price.Act
lemma ledger_n (f:Wave (Dwell n)→L[ℂ] Wave (Single n))(U:FC (Single n))
 (u:∀ X: Wave (Dwell n),f (acts (∑ Y:Aura n,M x Y) X)=acts U (f X)) (i:ℕ) :
 f (Cadre.pose (hGas Ωx Zq) i)=acts ((i.factorial:ℂ)⁻¹ • U^i) (f (Cadre.pose (hGas Ωx Zq) 0)):=by
 apply Cadre.hart _ (fun i=>f (Cadre.pose _ i)) _ i; intro i
 have v:= Cadre.scion Ωx (camp ∘ fun i:Aura n=>i.val) (M x) Zq (ξz (P:=P) F K x) (tent F K x) (tryP F r hF K z T w x p) (fun i=> T.edge x i) (fun _ _ e=> Finset.disjoint_left.mpr fun {i} v y=>Finset.disjoint_left.mp e (mem_filter.mp v).2 (mem_filter.mp y).2) (cold F r hF K z T w x p) i
 dsimp only at v; rw [← u _,← v]
 -- coefficient derivative, adapts Cadre.radT
 let Y:= hGas Ωx Zq; let D:= coeff (i+1) Y
 have hp:(↑i+1:↥(Dough (Dwell n)))*D=(i+1:ℕ) • D:=by rw [nsmul_eq_mul]; push_cast; rfl
 unfold Cadre.pose; rw [coeff_derivative,mul_comm,hp]; change _=f (acts ((Dough _).val ((i+1:ℕ) • D)) (vacuum _)); rw [map_nsmul,←Nat.cast_smul_eq_nsmul ℂ,act_smul,map_smul]; push_cast; rfl
end YM.CF.Stax
