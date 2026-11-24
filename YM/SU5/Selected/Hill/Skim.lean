import YM.SU5.Selected.Hill.Valse
import YM.CF.Graph.Dash
import YM.Push.FREE_RESOLVENT.AffineGap
/-! The price upper on ONE frame, through partition on prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Box
open Function Filter Finset Lattice Tree Wilson RG Exterior Pressure Work.F03 Work.E01 Precision MeasureTheory Next.Rank.Spindle Push Work.F02 CF.Graph
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{r:Side}{B R:ℕ}{e t:ℝ}{U:Config G n}{s:Signed}
variable {W:PathData G}{C:Clip}{σ X D θ:ℝ}
variable (V:(columbia r n).Slice G)(w:U=(columbia r n).drape V)(L:Rules G)
variable {P:BudgetPoint} (h: W.Bounds C σ X D)
def lesson(r:Side)(S: Lots n)(B:ℕ): Lots n:=univ.filter fun i=> Light r S B i.1
abbrev daily (C:Clip)(t:ℝ):= C.linear*t^2
def pulse (W:PathData G)(C:Clip)(E:Lots n)(R:ℕ)(v:fieldDir G n 1):=∑ i∈ E,pansy W R C i v
lemma living(C:Clip)(P:BudgetPoint)(U:Config G n)(x:Plane n): 0≤W.baseTerm C P U x:=by
 have h := C.quadratic_pos; have u:= C.tail_pos; have v:= P.threshold_pos; have hx:=G.chord_nonneg (faceValue U x); unfold PathData.baseTerm PathData.clipped; split_ifs <;> positivity [G.chord_nonneg]
lemma pays (x:Plane n)(p:x∈ menu U P.threshold): daily C P.threshold ≤ W.baseTerm C P U x:=by
 unfold PathData.baseTerm; obtain u:= (mem_filter.mp (show x∈ menu U P.threshold from p)).2; apply (le_add_of_nonneg_right ?_).trans'; · rw [PathData.clipped,if_neg u.not_ge]; unfold daily; rw [sq,←mul_assoc]; exact mul_le_mul_of_nonneg_left u.le (mul_nonneg C.tail_pos.le P.threshold_pos.le)
 split <;> positivity
include V w h
lemma abridge {m:ℕ}(z:4*r.val*P.threshold≤e)(he:e ≤ L.c)(h₁: m+2≤ B)(k: 2≤ P.threshold * Real.exp ((m:ℝ)/C.relaxation))(h₂:7 ≤ B)(h₀:2*R+3≤B)(hz:0<θ){v:ℝ}(p:0≤v): let M:=menu U P.threshold; let N:= lesson r M B;
 v*((1-θ)*pulse W C N R (scrim U)/2+ (M.card:ℝ)*daily C P.threshold)- (v* (Fintype.card (Plane n))* vault_fee C L X θ e σ R /2+ taxY n v P.threshold X D) ≤ W.principal C P v U:=by
 intro M N
 let F:= Fintype.card (Plane n); let W':= vault_fee C L X θ e σ R; have hv:0 ≤ W' :=by unfold W' vault_fee; positivity [C.quadratic_pos]
 let φ:= W.baseTerm C P U; have hp: Disjoint M N:=Finset.disjoint_left.mpr (fun _ v q=>(mem_filter.mp (show _∈ N from q)).2.2 _ v rfl)
 have hx:(N.card:ℝ)*W' ≤ (F:ℝ)*W':=mul_le_mul_of_nonneg_right (Nat.cast_le.mpr N.card_le_univ) hv; let u:=pulse W C N R (scrim U); let Q:=∑ x,φ x
 have ht:(1-θ)*u/2+ (M.card:ℝ)*daily C P.threshold-(F:ℝ)*W'/2 ≤ Q:=by
    have h₁: ((1-θ)*u-(N.card:ℝ)*W')/2 ≤ ∑ x∈N,φ x:=by
       unfold u pulse; rw [mul_sum, show (↑N.card:ℝ)*W'= ∑ _x∈ N,W' from (by simp only [sum_const,nsmul_eq_mul]),←sum_sub_distrib,sum_div]; refine sum_le_sum fun i ξ=>?_ ; have hA:Light r M B (affine 1 0 i.1):=by simpa [affine] using (mem_filter.mp ξ).2
       obtain p:= rubric V w L h i hA z he h₁ k h₂ h₀ hz; rw [FreeResolvent.Affine.pull_id,Lattice.pull_id] at p; exact p
    have h₂ : (M.card:ℝ)*daily C P.threshold ≤ ∑ x∈ M,φ x:=by refine le_trans ?_ (sum_le_sum fun i v=> show _ ≤ φ i from pays (C:=C) (U:=U) (P:=P) i v); simp
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ (M∪N)) (fun _ _ _=>living ..)); rw [sum_union hp]; linarith
 unfold PathData.principal; obtain ⟨A,D'⟩:=oath h P U; apply (add_le_add (mul_le_mul_of_nonneg_left (add_le_add ht (neg_le_of_abs_le A)) p) (neg_le_of_abs_le D')).trans'; unfold taxY; apply Eq.le; ring -- tune let terms
end YM.Hill.Box
#print axioms YM.Hill.Box.abridge
