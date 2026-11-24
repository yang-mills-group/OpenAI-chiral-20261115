import YM.CF.Graph.Dash
import YM.Gauge.Size
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
variable {G:Gauge}{n:Side}{h v a k C L W:ℝ}{R:PathData G}{F:RG.Clip}{i:ℕ}
def stone (G:Gauge)(n:Side)(x:ℝ): Set (Config G n):= Set.univ.pi (fun _=>G.shell x)
lemma stoneH(V:Config G n)(h:V∈stone G n k)(i:Face (Per n))(s:Signed): G.chord (faceValue (pull s 0 V) i) ≤ 4*k:=by
 have ht(j:Walk)(y:Site n): G.chord (travel V y j) ≤ j.length*k:=by
    induction j generalizing y with
    | nil=> simp [travel]
    | cons a x ih=>
      rw [travel, List.length_cons, Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm _ k]; refine (G.chord_triangle _ _).trans (add_le_add ?_ (ih _)); unfold Step.read; split; rw [G.chord_inv]; exact h _ (Set.mem_univ _); exact h _ (Set.mem_univ _)
 rw [faceValue,travel_pull]; refine (ht _ _).trans_eq ?_; simp [square]
lemma stones(G:Gauge)(n:Side)(k:ℝ):MeasurableSet (stone G n k):= MeasurableSet.univ_pi (fun i=>G.shell_meas k) -- tune
-- any period
lemma rife (P:BudgetPoint)(V:Config G n)(g:V∈ stone G n k)(u:4*k≤ P.threshold) : flags P.threshold V=∅:=by
 apply Finset.eq_empty_iff_forall_notMem.mpr; intro i p; obtain ⟨v,h,t⟩:= (flags_spec ..).1 p; exact t.not_ge (by have he:=stoneH (G:=G) _ g v 1; simpa using (he.trans u))
lemma pea (W:R.Bounds F a C L)(V: Config G n)(e:∀ i:Face (Per n), G.chord (faceValue V i) ≤ k)(u:0≤k)(t:Face (Per n)): ‖R.ell V t‖ ≤ C*k:=by
 obtain ⟨A,h,H⟩:= W.rows t.2; have hp:= h.mul_right k; have ht(i): ‖R.ellTerms t i V‖ ≤ (|(R.row t.2 i).1| *Real.exp (a*(R.row t.2 i).2.length))*k:=by rw [ellTerms,norm_smul,Work.F03.atSite_path,G.norm_adjoint]; refine mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg W.width.le (by positivity)))) ((G.curvature_norm _).trans (e _)) (norm_nonneg _) (A _)
 have he:= Summable.of_nonneg_of_le (fun i=>norm_nonneg _) ht hp; exact (norm_tsum_le_tsum_norm he).trans ((he.tsum_mono hp ht).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right H u))
def goldY(t u k C:ℝ):ℝ:= u*t^2/2+(C*t)^2/2 -- k threshold redundant.
def stoutY (N:Side)(β t u k C L:ℝ):ℝ:= β*(Fintype.card (Face (Per N))*goldY t u k C) +taxY N β k C L
lemma money (W:R.Bounds F a C L)(p:BudgetPoint)(V:Config G n)(u:V∈ stone G n k)(l:F.direct ≤ h)(t:4*k≤ p.threshold)(e:0≤k)(b:0≤v)(c:0≤C): R.inChannels F p v V ≤ stoutY n v (4*k) h p.threshold C L :=by
 let Z:= stoutY n v (4*k) h p.threshold C L
 have he(i:Signed): R.principal F p v (pull i 0 V) ≤ Z:=by
    let U:=pull i 0 V
    let L':= goldY (4*k) h p.threshold C; have hu(q:Face (Per n)): R.baseTerm F p U q ≤ L':=by
       have hg(q:Face (Per n)): G.chord (faceValue U q) ≤4*k:= stoneH V u q i
       unfold baseTerm clipped; rw [if_pos ((hg q).trans t)]; refine add_le_add ?_ ?_
       · apply div_le_div_of_nonneg_right _ (by positivity); have ht:=G.chord_nonneg (faceValue U q); exact mul_le_mul l (pow_le_pow_left₀ ht (hg q) _) (sq_nonneg _) (F.quadratic_pos.le.trans l)
       split; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (pea W U hg (by positivity) q) 2) (by positivity); positivity
    obtain ⟨A,B⟩:=oath W p U; unfold Z stoutY taxY PathData.principal; refine (add_le_add (mul_le_mul_of_nonneg_left (add_le_add ((sum_le_sum (g:=fun _=>L') (fun i _=>hu i)).trans_eq (c:=Fintype.card (Face (Per n))*L')  ?_) (le_of_abs_le A)) b) (le_of_abs_le B)).trans_eq (by unfold L'; ring); simp -- tune eq trans_eq b name
 unfold inChannels; refine (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> he i)) (by positivity)).trans_eq ?_; simp [Z]
end YM.CF.Graph
