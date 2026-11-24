import YM.CF.Scion.Blade
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel

open Cour Acorn Atala Reef MeasureTheory Jet
variable {N B:Side} (D e:ℝ) (J:Pride (mid N B)) (X Y:Seal (Site (Domain N B)))
variable (V:Tints N B e)
variable (W:∀ Y:Seal (Seat (mid N B)), Lend N B e Y)(x:Castle N B e X)(G:Ids (mid N B))
variable {j k:ℕ}{L:Side}{ho:Odd L.val}{P:Pricing j L ho (Thread j)}{q:Grasp P B e}
def stock (Y:Seal (Seat (mid N B))× Seal (Seat (mid N B))):FC (Single (mid N B)):= strokeC e X Y.1 V G x • hula W X x G {Y.2}
variable {a A' b c d w:ℝ}
local notation "N₀"=> CSide N B
lemma weill (h:Dyes D e J k V a w)(p:Grove (terr _) X)(hp:WordK J)(hq: ClearP J): ∑ Y,stock e X V W x G Y= hoopI X e J x • hula W X x G univ:=by
 unfold stock; rw [←tile D e J X V _ _ _ h p x G hp hq,Finset.sum_smul, Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; dsimp only; rw [←Finset.smul_sum]; congr 1
 let s:=Hive.chip X G; simp_rw [hols X W] -- tune implicit X first
 rw [sum_comm]; apply sum_congr rfl; intro j p; simp -- tune
variable {m:Male}{K:Aim (mid N B)}
lemma axis (s:Sweep (mid N B))(F:Seal (Seat (mid N B)) × Seal (Seat (mid N B)))(p:Vista q m K W k b c d a)(h:Grove (terr _) X)(hp:Injective (priorP G)) : stock e (actS s X) V W (pullT s x) (bun s G) (actS s F.1,actS s F.2)=teen s (stock e X V W x G F):=by
 unfold stock; dsimp only; rw [← show turnZ s {F.2}={actS s F.2} by simp [turnZ], shrew W _ h _ _ _ hp p,stampU e X F.1 V _ _ G (by cases h <;> simp) hp]; exact (lot_s ..).symm
lemma gauge_p (s: Seat (mid N B)→ E)(F: Seal (Seat (mid N B))× Seal (Seat (mid N B)))(p:Vista q m K W k b c d a)(h:Grove (terr _) X) : stock e X V W (pullF X s x) (threadG s G) F=Gaze s (stock e X V W x G F):=by unfold stock; rw [stepC,hub_u W _ h p]; exact (lot_s false false (tradew (mid N B) s) _ _).symm
end YM.CF.Scion
