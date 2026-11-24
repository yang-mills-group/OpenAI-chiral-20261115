import GaugeFieldConstruction.Polter3
import GaugeFieldConstruction.BirthH3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
open XGarden.Shield
open Leaf
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e r h:ℝ} 
abbrev CanoeNX(o: Seat n)(μ:ℕ):= Lattice.halo μ ({o}:Support (More n))
local notation "SA"=>Support (More n)
variable (P:BudgetPoint)(g h w f:ℝ)
abbrev MicroShipNX {n:Side} (p:BudgetPoint)(u: Support (More n))(f: Pane n→ℂ) (a:ℝ): Prop:= 0≤a ∧ Envelope f ∧ LocalOn u f ∧∀ V, Allows p.order (f∘Shield.solo p.threshold V) 0 a
abbrev DonauNX (μ:ℕ)(p: BudgetPoint)(u: Seat n)(h:ℝ)(M: Paper n)(f:ℝ): Prop:= ∃ X:Wa n→ℝ,(∀ i,MicroShipNX p (CanoeNX u μ) (M i) (X i) ∧ (¬ DomainP (CanoeNX u μ) i → M i=0))∧ ∑ i:Wa n,papW n h i * X i ≤ f
lemma Donaul_liftNX {q:BudgetPoint}{μ:ℕ}{x:Seat n}{h:ℝ} {M:Paper n}{y:ℝ}(s:DonauNX μ q x h M y):TrackD q (CanoeNX x μ) h M y:=by refine ⟨s.choose,fun i => ⟨?_,(s.choose_spec.1 i).2⟩,s.choose_spec.2⟩; obtain ⟨p,r,g,u⟩:= (s.choose_spec.1 i).1; exact ⟨p,r,g,fun i _=>u i⟩
variable {μ:ℕ}
def countLZ (μ:ℕ)(o:Seat n)(c:SP3 n): Prop:=c.elim True (fun i=>¬Disjoint (CanoeNX o μ) i)
def clingMZ (μ:ℕ)(o:Seat n)(c:L3 n):Prop:= countLZ μ o c.1∧ countLZ μ o c.2
def pulledNX (μ k:ℕ)(o:Seat n)(z:L3 n):Hub n:= ⟨⟨o,CanoeNX o μ∪ (limbM k z.1 ∪ limbM k z.2)⟩, mem_union_left _ (Lattice.halo_subset _ _ (mem_singleton_self _))⟩
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
noncomputable def AdventureNX (P:BudgetPoint)(μ:ℕ)(o:Seat n)(p:L3 n)(Z:Paper n): Factor3 n where
 H:=pulledNX μ k o p
 issue D:= if clingMZ μ o p then fun W=> wax (αLines Z W.1) p (Elev F R k t D W) else 0
 raw W:= if clingMZ μ o p then wax (αLines Z W.1) p (fun S=>rawH F R S W) else 0
 pure:= false
lemma ψMesaNX (μ:ℕ) (k:ℕ)(o:Seat n)(p:L3 n)(H:Support (More n)→LeanV (Single n)→LeanV (Single n)→ℂ)(Z:ChartP n) (g:∀ i:Wa n,Z i ≠0 → DomainP (CanoeNX o μ) i)(h:∀ (S:Support (More n))(i j:LeanV (Single n)),H S i j ≠0→j∈ camp S): Fock.Sector (camp (pulledNX μ k o p).val.2) false (wax Z p H):=by
 apply Sector.sumS; intro i _; let L:= pulledNX μ k o p; by_cases s: Z i=0
 · rw [s,zero_smul]; exact Sector.zero _
 apply Sector.scale; have ht(b:Bool)(j:Single n)(u:aptK j∈ CanoeNX o μ): (b,j)∈camp L.val.2:= mem_filter.mpr ⟨mem_univ _, mem_union_left _ u⟩
 rcases i with _ | ⟨b,i,j⟩
 · change Sector _ false (if τPure p then 1 else 0); split; exact Sector.one; exact Sector.zero _
 have V:=g _ s
 exact (meal_γ k H _ (vS:=p.1) (subset_union_left.trans subset_union_right) (ht b _ V.1) (fun i=>h i _)).mul (meal_γ k H _ (vS:=p.2) (subset_union_right.trans subset_union_right) (ht (!b) _ V.2) (fun i=>h i _)) -- tune explicit h_bin
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
