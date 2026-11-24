import YM.CF.Swell.Pod
import YM.CF.Swell.Ink
import YM.CF.Hove.Bird
import YM.CF.Leaf.Wren
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open SU Prism Tap Levier Thera Moto Oath Font
variable {N B m:Side} {a b c d e:ℝ}
-- Raw.Ph.Volume fourteen actual open stencil.
variable (P:Op (Single N))(x y o:Site N)(U:Pal)
variable (p q:Rock N)(L:SOp N)(k l:ℕ)(d:ℝ)(h:0<d)(u:d≤1)(X:Op (Single N))
variable (F:Moto.Fit o k l b X)(vX:Branded o X)
include F vX
lemma door_X(h:boxM X p q≠0) : (Λrod p q).length ≤ 16*l ∧ node o∈χrod p q:=by
 obtain ⟨i,j,P⟩ : ∃ i j:SU.Slot, X (p,i) (q,j)≠0:=by by_contra! ht; exact h (Matrix.ext fun i j=>ht i j)
 have hx:= separation_triangle (node p.1) (node o) (node q.1); have hp:=(F.2.2 (p,i) (q,j) P); change _≤_ ∧ _≤_ at hp
 have he:separation (node p.1) (node q.1) ≤4*l:=by
    rw [separation_comm (node p.1) (node o),ζdist o p.1,ζdist o q.1] at hx; change separation o p.1≤ _∧ separation o q.1≤ l at hp -- order wrong
    omega
 refine ⟨(Font.short ..).trans (by omega),?_⟩ -- omega relation?
 obtain h|h := (vX _ _ P).2.2
 · rw [← show p.1=o from h]; exact Tulip.trace_source ..
 rw [←show q.1=o from h]; exact (show stop (node p.1) (Λrod p q)=node q.1 from stopH ..) ▸ trace_last (node p.1) (Λrod p q)
omit F vX
lemma cute : ∑ p:Rock N, ∑ q:Rock N,‖boxM X p q‖ ≤ Haro.horn*paid_M o X k:=by
 let G(x y:Rock N):ℝ:=∑ i:SU.Slot,∑ j:SU.Slot,‖X (x,i) (y,j)‖;
 have hP(i j): ‖boxM X i j‖ ≤ Haro.horn* G i j:=soft 1 _ (sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _) (fun x y=>(single_le_sum (fun j (_:j∈(univ:Finset SU.Slot))=> norm_nonneg (_:ℂ)) (mem_univ y)).trans (single_le_sum (fun i (_:i∈(univ:Finset SU.Slot))=>sum_nonneg (fun j _=> norm_nonneg (_:ℂ))) (mem_univ x)))
 refine le_trans (sum_le_sum fun i _=> sum_le_sum fun j _=> hP i j) ?_; simp_rw [←mul_sum]; apply mul_le_mul_of_nonneg_left; swap; exact zero_le_one.trans Haro.p0
 unfold G paid_M paidX; conv_rhs=> rw [Fintype.sum_prod_type]
 simp_rw [Fintype.sum_prod_type (α₂:=SU.Slot)]; apply sum_le_sum; intro i _; rw [sum_comm]; exact sum_le_sum fun j _=>sum_le_sum fun k _=>sum_le_sum fun l _=> le_mul_of_one_le_left (norm_nonneg _) ((le_add_of_nonneg_right (zero_le_one.trans (nook_l ..))).trans' (nook_l ..))
include h u F vX
lemma ρcoat (s:0 ≤ a): Soak (node o) (ρlens X) a (νt a d (16*l)*(Haro.horn*b)) d:=by
 let M(p q:Rock N):= κfare p q d (boxM X p q); let V(p q:Rock N):= Tulip.reed p q (M p q); let W:=νt a d (16*l); have ht: 0 ≤ W:=by unfold W νt; positivity
 have hf(p q:Rock N)(l':boxM X p q=0): V p q=0:=by unfold V M; rw [l']; funext i j; simp [Tulip.reed, κfare]
 refine arm_v (o:=node o) (fun j:Rock N×Rock N=> χrod j.1 j.2) _ (fun j=>V j.1 j.2) (fun j=>Ωg j.1 j.2 d h u X F.2.1) ?_ ?_ (fun i=>?_ ) -- tuning.
 · have hh:=cute o k X -- tune order
   apply le_trans _ (mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left F.1 (zero_le_one.trans Haro.p0))) ht); rw [Fintype.sum_prod_type,mul_sum]; apply sum_le_sum; intro p _; rw [mul_sum]; apply sum_le_sum; intro q _; by_cases hx:boxM X p q=0; · change rent a (χrod p q)* ledgerV (V p q)≤ W*_; rw [hf _ _ hx,hx,norm_zero]; simp [ledgerV]
   have he:= (door_X o p q k l X F vX hx).1
   let n:ℕ:=(Λrod p q).length; let s':ℝ:= Real.exp (a*((16*l+1:ℕ):ℝ)); have hz:rent a (χrod p q)≤ s':=Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((trace_k ..).trans (Nat.add_le_add_right he _))) s)
   rw [show ledgerV (V p q)=(Fintype.card SU.Slot:ℝ)^2*M p q from box_phi p q p]
   apply le_trans (mul_le_mul_of_nonneg_right hz (mul_nonneg (sq_nonneg _) (show 0 ≤ M p q from (by unfold M κfare; positivity))))
   change s'* ((Fintype.card SU.Slot:ℝ)^2*((n+1:ℝ)*(1+d)^n* ‖boxM X p q‖)) ≤ W* _; unfold W νt; calc
    _ ≤ s'*((Fintype.card SU.Slot:ℝ)^2*((↑(16*l:ℕ)+1:ℝ)*(1+d)^(16*l) * ‖boxM X p q‖)) :=by gcongr; linarith
    _ = _:=by unfold s'; ring
 · intro p v; apply hf; by_contra t; exact v ((door_X o p.1 p.2 k l X F vX t).2)
 rw [Fintype.sum_prod_type]
omit F vX
lemma ρprobe (X:Dome)(g:Noble X)(p:0≤a): Soak (node o) (ρlens (spring_V X o)) a (νt a d 16*(Haro.horn*chipZ k ‖X‖)) d:=ρcoat o k 1 d h u _ (beam_l o _ X g) (tap_Ψ _ X g) p -- tune X include F/vX drop later
end YM.CF.Swell
