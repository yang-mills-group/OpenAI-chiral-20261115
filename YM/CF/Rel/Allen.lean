import YM.CF.Rel.Minder
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
variable {s:SpotG G (m+1)}{X:ShowM G m}{Q:SpotG G (m+1)→noteG G m}{k:Site n}
-- sum charges. compact sizes Trace.Lens. cap cast norm.
def bite(i: Dent n G m)(X:ShowM G m):ℝ:= match i with|⟨s,j,d,b,p,a⟩=> ‖B (X s j) p d b‖
lemma sting_x (k:Site n) (j:Fin (m+1))(a:Axis): ‖sting k j a‖=1:=by unfold sting; split; exact legX ..; rw [norm_one]
lemma rubR (D:Dent n G m): ‖rub X k D‖≤ bite D X:=by rcases D with ⟨s,i,d,b,p,a⟩; unfold rub bite; simp only [norm_mul,sting_x,mul_one]; exact mul_le_of_le_one_left (norm_nonneg _) (Stationary.norm_left ..)
-- explicit card dan
abbrev capMult(G:Gauge)(m:ℕ):ℝ:= Fintype.card (SpotG G (m+1) × Fin (m+1) × TypeFace 3 × CurRun (m+1)×Axis)
abbrev qMult(G:Gauge)(m:ℕ):ℝ:=Fintype.card (SpotG G (m+1)×CurRun (m+1))
lemma tokenC(h:∀ i j,Braid.Board l A (X i j))(hr:2*l<n.val): (∑ i:Dent n G m, bite i X) ≤ capMult G m*A:=by
 unfold Dent; simp_rw [Fintype.sum_prod_type]; rw [← show ∑ _u:SpotG G (m+1)× Fin (m+1)× TypeFace 3 × CurRun (m+1)×Axis,A=capMult G m*A from by simp [capMult]]; simp_rw [Fintype.sum_prod_type]
 refine sum_le_sum fun s _=>sum_le_sum fun i _=>?_ ; rw [sum_comm]; refine sum_le_sum fun b _=>?_ ; rw [sum_comm]; refine sum_le_sum fun p _=>?_ ; rw [sum_comm]; exact sum_le_sum fun a _=>(reports (h s i b p) hr).1
lemma tokenY(h:∀ i j,Braid.Pond l A (Q i j))(hr:2*l<n.val): (∑ i:Qind n G m,‖hue Q i‖) ≤ qMult G m*A:=by
 unfold Qind; rw [← show ∑ _ : SpotG G (m+1)×CurRun (m+1),A=qMult G m*A from by simp [qMult]]; simp_rw [Fintype.sum_prod_type]
 refine sum_le_sum fun s _=>?_ ; rw [sum_comm]; exact sum_le_sum fun p _=> (reports (h s p) hr).1
lemma clock_s (d:DialT n m)(i:Fin (m+1))(a:Axis) (he:d∈ketch l n m) (p:CurRun (m+1)): diskP 0 (d+reedU i a) p ∈ Pots 0 (l+1) (m+1):=by
 rw [shade_p]; intro j; rw [diskG]; cases j using Fin.cases with
 | zero => simp [fillSpot]
 | succ j=>
     have hx: separation 0 (d j)≤ l:=(ketch_p ..).mp he j
     change separation 0 (_:Site n) ≤ _; simp only [fillSpot,Fin.cases_succ,Pi.add_apply]
     apply (separation_triangle _ (d j) _).trans; apply (Nat.add_le_add hx _); induction i using Fin.cases with
      | zero=> simp only [reedU, Fin.cases_zero]; exact Font.small _ (Lattice.negDir a)
      | succ i=> simp only [reedU,Fin.cases_succ,Pi.single_apply]; split; exact Font.small _ (Lattice.posDir a); simp
lemma poly_x {W:KitM G n (m+1)} (f:ℕ→ℝ)(F:∀(u:ℕ){n:Side}(o:Site n)(P:Disk n (m+1)),P∈Pots o u (m+1)→∀ z:Delph G (m+1), Trade z→CakeF (fans o P z) o (tile u) r 1 (‖z‖*f u))(h:nerve 0 l W)(hp:∀ i,Trade (W i))(hh:∑ i,‖W i‖ ≤ C)(hr: m+1 ≤ r)(ha:0 ≤ f l):
 Travel k r (m+1) (l+tile l) (l+tile l) 1 (C*f l) (intoX W k):=by
 let L:=l+tile l
 let g(i:Disk n (m+1)):=stroll k (-(i 0).1) (fans 0 i (W i))-fans 0 i (W i); have hv(i):Travel k r (m+1) L L 1 (‖W i‖*f l) (g i):=by
    by_cases hl:i∈Pots 0 l (m+1)
    · have he:= F l 0 i hl (W i) (hp i); apply Travel.single he _ (l:=l) _ (show l+tile l≤ L from le_rfl) (mul_nonneg (norm_nonneg _) ha); rotate_left
      · have hv:=shade_p.mp hl 0; apply le_trans (le_of_eq ?_) hv; have hv:= separation_translate (-(i 0).1) (0:Site n) ((i 0).1); rw [neg_add_cancel,zero_add] at hv; rw [separation_comm 0 (-(i 0).1)]; exact hv.symm
      exact (asideF ((he.ledger 0 (by simp)).smooth.of_le (by exact_mod_cast hr)) _ (fans_p 0 i (W i))).1
    unfold g; rw [h i hl,show fans 0 i (0:Delph G (m+1))=0 from rfl,zero_a, sub_self,norm_zero,zero_mul]; exact Travel.stilt le_rfl le_rfl
 apply (Travel.sigma univ g _ zero_lt_one hr (fun i _=> hv i)).up _ le_rfl le_rfl le_rfl le_rfl; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hh ha
end YM.CF.Rel
