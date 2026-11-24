import Finch.Mask
import YM.SU5.Interaction.Source.Reduction
import YM.CF.BPress.Pine.Reel

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered StressExchange

variable {I:Type} [LinearOrder I] [Fintype I]
def bookValue (X:Op I):ℝ:= ∑ i,∑ j, ‖X i j‖

lemma trace_book (X:Op I) : ‖Matrix.trace X‖ ≤ bookValue X:= by
 unfold Matrix.trace
 refine le_trans (norm_sum_le ..) (sum_le_sum fun i _=>?_)
 exact single_le_sum (fun j _=>norm_nonneg (X i j)) (mem_univ i)

lemma dg_book [Nonempty I] (X:Op I) : ‖dg X‖ ≤ bookValue X :=by
 unfold dg dyad; refine le_trans (norm_sum_le ..) (sum_le_sum fun i _=>le_trans (norm_sum_le ..) (sum_le_sum fun j _=>?_)); rw [norm_smul]; apply mul_le_of_le_one_right (norm_nonneg _)
 refine le_trans (norm_mul_le ..) (mul_le_one₀ (BPress.Pine.cost_put _) (norm_nonneg _) ?_); rw [takeF,norm_star]; exact BPress.Pine.cost_put _
lemma book_left (X:Op I)(S:Finset I) : bookValue (cutM S*X) ≤ bookValue X:=by
 unfold bookValue; refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_; rw [cutM,Matrix.diagonal_mul]; split <;> simp [norm_nonneg]
lemma book_right (X:Op I)(S:Finset I) : bookValue (X*cutM S) ≤ bookValue X:=by
 unfold bookValue; refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_; rw [cutM,Matrix.mul_diagonal]; split <;> simp [norm_nonneg]
lemma pre_book [Nonempty I] (X:Op I)(S:Finset I): ‖preJ (cutM S) X‖ ≤ 2*bookValue X:=by
 unfold preJ; rw [←dim_cut,two_mul]; refine le_trans (norm_add_le ..) (add_le_add ?_ ( (dg_book _).trans ((book_right ..).trans (book_left ..))))
 rw [norm_smul,norm_one,mul_one]; exact (trace_book _).trans (book_left ..)

variable {N:Side}{P:SOp N}{o:Seat N}{a b c d v:ℝ}{p:BudgetPoint}{k r:ℕ}
variable {A:Scree.Loom N}(h:Roof N b d r A)(u:0<d)(X:Trunk o P k a v d)
lemma soakBook (X:Soak o P a v d) (ha:0≤a) (x:Openc (More N) d): bookValue (P x.val) ≤ v:=by
 obtain ⟨F,T,f,t,z,g⟩:=X; refine le_trans ?_ z
 rw [g]; unfold bookValue; simp_rw [Matrix.sum_apply]
 let E:= ∑ i:Single N, ∑ j:Single N,∑ S:Sa N,T S i j
 have r: (∑ i:Single N, ∑ j:Single N, ‖∑ S:Sa N, F S x i j‖) ≤ E:=
    sum_le_sum fun i _=>sum_le_sum fun j _=>
     (norm_sum_le ..).trans (sum_le_sum fun S _=> ((f S).expo ..).bounded x)
 refine r.trans ?_; unfold E; simp_rw [sum_comm (t:=(univ:Finset (Sa N))) (s:=(univ:Finset (Single N)))]
 refine sum_le_sum fun i _=> le_mul_of_one_le_left (sum_nonneg fun j _=>sum_nonneg fun k _=>(f i).nonn j k) ?_
 exact Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))
include h u X
lemma book_ink (V:Pane N)(p:BudgetPoint)(ha:0≤a) : bookValue (markMatrix A p o P V)≤ v:=by
 by_cases q:pingS p.threshold (halo p.B {o}) V
 · unfold markMatrix; rw [Set.indicator_of_mem (show V∈_ from q)]; exact soakBook X.pay ha (roller u h (V,Classical.arbitrary _))
 rw [ink_away _ q]; simpa [bookValue] using soakCostNN X.pay
end YM.CF.Swell
