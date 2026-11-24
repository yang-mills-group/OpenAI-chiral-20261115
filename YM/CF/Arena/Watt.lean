import YM.CF.Arena.Pier
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open Jet Rel Stationary Push.Loops
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
section Hess
lemma flaw_sum (x:InputZ G n): (∑ i:Body 1 n × G.ColorIndex,(x i.1 i.2) • flaw G i.1 i.2)=x:=by
 ext b j; rw [Finset.sum_apply,WithLp.ofLp_sum,Finset.sum_apply,Finset.sum_eq_single (b,j)]; change x b j * flaw G b j b j=x b j; simp [flaw,jewelG]
 intro a _ h; rcases a with ⟨c,g⟩; change x c g * flaw G c g b j=0; unfold flaw; by_cases p:b=c
 · subst c; rw [Pi.single_eq_same]; have he:g≠j:=fun hp=> h (by rw [hp]); simp [jewelG,Ne.symm he]
 rw [Pi.single_eq_of_ne p]; simp
 simp
lemma basisK {o:Site n}{F:SpaceX G n} (h:Atom F o r)(ht:ContDiffAt ℝ (l:ℕ∞ω) (satX F) 0) (p:0 ≤ A)(hp:∀ k:Fin l → Body 1 n× G.ColorIndex, ‖cake l (satX F) (fun i=> flaw G (k i).1 (k i).2)‖≤ A) : ‖cake l (satX F)‖ ≤ (plot r * Fintype.card (TypeFace 1 × G.ColorIndex):ℕ)^l*A:=by -- cast
 apply Planned.AtomRegular.op_le_of_unit (by positivity) -- tune
 intro V HV; let X:= cake l (satX F); let O(i:Fin l)(k:Body 1 n × G.ColorIndex):= V i k.1 k.2 • flaw G k.1 k.2; let P(i:Fin l→ Body 1 n × G.ColorIndex):=X (fun j=>O j (i j)); -- suffix type
 have hh(i:Fin l): V i=∑ j,O i j:=(flaw_sum _).symm
 let z:= (pavilion r o ×ˢ (Finset.univ:Finset (TypeFace 1))) ×ˢ (Finset.univ:Finset G.ColorIndex); let T:= scope n z l; let K:=plot r* Fintype.card (TypeFace 1×G.ColorIndex)
 have hZ : T.card ≤ K^l:=by unfold T; rw [careC]; unfold z; rw [card_product,card_product,card_univ,card_univ]; refine pow_le_pow_left₀ (by omega) ?_ _; unfold K; rw [Fintype.card_prod,←mul_assoc]; gcongr; exact pay_v _
 have heZ(W:Fin l→ _): P W=(∏ i:Fin l,V i (W i).1 (W i).2) • X (fun i=>flaw G (W i).1 (W i).2):= ContinuousMultilinearMap.map_smul_univ ..
 change ‖X V‖ ≤ _; conv_lhs=> rw [show V=_ from funext hh, ContinuousMultilinearMap.map_sum]
 change ‖∑ i,P i‖ ≤ _; rw [← sum_subset (subset_univ T) (fun j _ he=>?_)]
 · apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun _=> A) _).trans
   · rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ p
     exact_mod_cast hZ
   intro i t; rw [heZ,norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) (hp i); rw [Real.norm_eq_abs,abs_prod]; refine prod_le_one (fun _ _=>abs_nonneg _) (fun j _=>?_); exact ((Real.norm_eq_abs _).symm.trans_le (PiLp.norm_apply_le _ _)).trans ((norm_le_pi_norm ..).trans (HV j))
 simp only [T,scope,z,Fintype.mem_piFinset,mem_product,mem_univ,and_true,theatre,not_forall,not_le] at he; obtain ⟨i,hp⟩:=he; rw [heZ]; change _= _; rw [show X _=0 from scatter (fun i=>(j i).1) (fun i=>(j i).2) h ht i hp,smul_zero] -- metavars
end Hess
end YM.CF.Arena
