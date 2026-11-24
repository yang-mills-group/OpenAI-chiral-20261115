import YM.CF.Buffered.Admission
/-! Eventually-half admits Gaussian scalar gluing estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Alloy
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember Mint Mint.Roe Fock Dial Gall Advance Pastry MeasureTheory Push.SectorMeasure
open Ballad Crust
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H L':ℝ}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
lemma tepid : ∀ᶠ i in atTop, 0 < Graph.angle (I i) ∧ Graph.angle (I i)/2 ≤ Grid.globe (More (NP i)) (I i).path (I i).funds (I i).p (I i).beta ((I i).p.threshold/2) := by
 have he:= Mint.tc Z.path.rank; let F(i):= flagT (NP i) (V i) (θ i) C; have ht: Gray (lum x) F:= Z.path.mark Z.vol C Z.dark (Gray.thin he Z.loc.shrinks)
 let A(i):=Real.exp (-(kinetic (More (NP i)) (I i).p L' (L i) (I i).beta w)); let f(i):= drip (I i) P
 have hv:Tendsto (fun i=> A i/f i) atTop (𝓝 0):= by simpa only [F,neg_add_cancel,zero_sub] using (seals D Z ht.neg).shrinks
 filter_upwards [Roe.touch D Z,Z.support,Z.tend.eventually_ge_atTop k,Z.path.infl,hv.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2))] with i ⟨u,p⟩ ⟨X',J,gx,hQ,w',v⟩ hn ht hi
 refine ⟨u,?_⟩; have hk:= D.plan (N i) (Nat.cast_le.mp hn); have ha : f i ≤ Graph.angle (I i):=by
    apply mul_le_of_le_one_right u.le (_:Kea.angel (N i) P (I i).J.M≤1)
    apply (norm_inner_le_norm _ _).trans; rw [(tickB _).2,(sea_g hk.1 (Kea.tax _) (tax_guard _ _ _ D.eP.le) _).2]; simp
 have hh:A i ≤ Graph.angle (I i)/2:= by change A i / f i ≤ _ at hi; have hp:0<f i:=p; linarith [(div_le_iff₀ hp).1 hi]
 have hg:= floor_loss (N:=More (NP i)) gx (I i).p ht.2.1.le hQ; rw [globe_price gx] at hg; change _ ≤ A i at hg; linarith
end YM.CF.Buffered.Alloy
#print axioms YM.CF.Buffered.Alloy.tepid
