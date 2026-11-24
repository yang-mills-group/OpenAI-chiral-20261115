import YM.CF.Bloom.Rudel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
variable {α:Type*}{m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z:ℝ}{P:Grasp Y B e}{hP:Pearl P}
lemma principal_min {G:Gauge}{a b c L:ℝ}(P:BudgetPoint)(X:PathData G)(Q:Clip)(hx:X.Bounds Q a c L)(hp:0≤b)(V:Config G N): -taxY N b P.threshold c L ≤ X.inChannels Q P b V:=by
 have he(s:Signed): -taxY N b P.threshold c L ≤ X.principal Q P b (pull s 0 V):=by
    let U:=pull s 0 V; obtain ⟨A,B⟩:= oath hx P U; unfold PathData.principal; have h(i:Face (Per N)):0 ≤ X.baseTerm Q P U i:=by
       unfold baseTerm; apply add_nonneg
       · unfold clipped; split; exact div_nonneg (mul_nonneg Q.quadratic_pos.le (sq_nonneg _)) (by positivity); exact mul_nonneg (mul_nonneg Q.tail_pos.le P.threshold_pos.le) (G.chord_nonneg _)
       split <;> positivity
    refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (sum_nonneg (fun i _=>h i)) (neg_le_of_abs_le A)) hp) (neg_le_of_abs_le B)); exact le_of_eq (by unfold taxY; ring)
 apply ((mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun i _=> he i)) (show 0≤ (Fintype.card Signed:ℝ)⁻¹ by positivity))).trans'; simp
variable {n:ℕ} -- m local? check
lemma bau_N (V:GramM (mid m B))(S:Loom (mid m B))(H:Roof _ u e n S)(s:Grasp Y B e)(hp:s.roundZ ≤ (mid m B).val)(K':Ledger R v η r C V)(hx:V.path.Bounds V.funds μ D L')(ht:0 ≤ r)(t:1 ≤ R)(hC:0 ≤ C)(hb:0≤V.beta)(y: Orbit (mid m B)): ‖recX s V S y‖≤ Real.exp (taxY (More (mid m B)) V.beta V.p.threshold D L')*Real.exp (flagT (mid m B) v η C):=by
 have hh:= (s.broadness _ hp V.J.M).projection (S y) (H.paid y)
 let A:=cab V s S y; let w:= past V y.1; have he:0 ≤ w:= (Real.exp_pos _).le; have hp':‖A‖=1:= (sea_g hp (S y) (H.paid y) V.J.M).2; have hu:‖beam V s S y‖ ≤ Real.exp (flagT (mid m B) v η C):=(spentS _ _ A).trans (by rw [hp',mul_one]; exact stout K' _ ht t hC hh)
 rw [porch,norm_smul]; exact mul_le_mul ((Real.norm_of_nonneg he).trans_le (Real.exp_le_exp.mpr (neg_le.mp (principal_min V.p V.path _ hx hb y.1)))) hu (norm_nonneg _) (Real.exp_pos _).le -- neg?
end YM.CF.Graph
