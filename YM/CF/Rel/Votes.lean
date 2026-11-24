import YM.CF.Rel.Allen
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
variable (f:ℕ→ℝ)(F:∀ (l:ℕ){n:Side}(o:Site n)(P:Disk n (m+1)), P∈Pots o l (m+1)→∀ z: Delph G (m+1), Trade z→ CakeF (fans o P z) o (tile l) r 1 (‖z‖*f l))
 {k:Site n}(h:∀ i,0≤f i){X:ShowM G m}{Q:SpotG G (m+1)→noteG G m}
include F h
lemma polY (hp:∀ i j, Braid.Board l A (X i j))(hr:2*l<n.val)(hl:m+1 ≤ r): Travel k r (m+1) (tile (l+1)+1) (tile (l+1)+1) 1 (capMult G m*A*f (l+1)) (intoY X k):=by
 let R:=tile (l+1)+1; let T' (d:Dent n G m):=bite d X*f (l+1); let V(i:Dent n G m):= potsC X k i; have hh(D):Travel k r (m+1) R R 1 (T' D) (stroll k (cape k D) (V D)-V D):=by
    obtain ⟨s,i,d,b,p,a⟩:=D; let D:Dent n G m:=(s,i,d,b,p,a)
    by_cases hv: d∈ketch l n m
    · 
      have ht: seedsV D∈Pots 0 (l+1) (m+1):= clock_s _ _ _ hv _; have hx:= F (l+1) 0 _ ht (rope (silica s)) (Rope (silica s)); have hV:(separation 0 (cape k D)) ≤ 1:=by change separation 0 (palm k i a)≤1; unfold palm; split; exact ((show separation 0 (Lattice.step a:Site n) ≤ 1 from by simpa using Font.small (0:Site n) (posDir a)) ); simp
      have hK := hx.pay (rub X k D); let C:=‖rub X k D‖ * (‖rope (silica s)‖ * f (l+1)); have hL: C≤ T' D:= mul_le_mul (rubR D) (mul_le_of_le_one_left (h _) ((rope_h _).trans (ston _))) (mul_nonneg (norm_nonneg _) (h _)) (norm_nonneg _)
      have he: ‖(0:InputZ G n)‖<1:=by simp
      apply (Travel.single hK (i:=cape k D) _ hV (show 1+tile (l+1) ≤ R by unfold R; omega) (hK.ledger 0 he).nonneg).up hL le_rfl le_rfl le_rfl le_rfl; exact (asideF ((hK.ledger 0 he).smooth.of_le (by exact_mod_cast hl)) _ (trot_p X k D)).1 -- tune
    have hu: B (X s i) p d b=0:= (reports (hp s i b p) hr).2.1 d hv; have he: V D=0:=by unfold V potsC; rw [show rub X k D=0 from by simp only [D,rub,hu,mul_zero],zero_smul];
    change Travel _ _ _ _ _ _ (‖B (X s i) p d b‖*_) (stroll k _ (V D)-V D); rw [he, hu,norm_zero,zero_mul,zero_a, sub_self]; exact Travel.stilt le_rfl le_rfl
 refine (Travel.sigma univ _ T' zero_lt_one hl fun i _=> hh i).up ?_ le_rfl le_rfl le_rfl le_rfl; unfold T'; rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (tokenC hp hr) (h _)
lemma paceQ (hq:∀ i j,Pond l A (Q i j))(hr:2*l<n.val)(hj:m+1 ≤ r): CakeF (intoQ (n:=n) Q) 0 (tile l) r 1 (qMult G m*A*f l) ∧ cFoot (m+1) (satX (intoQ (n:=n) Q)):=by
 have he : CakeF (intoQ (n:=n) Q) 0 (tile l) r 1 (qMult G m*A*f l):=by
    unfold intoQ; apply (CakeF.sigmaH (a:=fun i=> ‖hue Q i‖*f l) _ (fun i _=>?_)).under le_rfl le_rfl (by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (tokenY hq hr) (h _))
    obtain ⟨s,d,p⟩:=i; by_cases hv:d∈ketch l n m
    · let L:=rope (silica s); have ht:diskP 0 d p ∈Pots 0 l (m+1):=by
        rw [shade_p]; intro j; rw [diskG]; induction j using Fin.cases
        · simp [fillSpot]
        simp only [fillSpot, Fin.cases_succ]; exact (ketch_p ..).mp hv _
      exact ((F l 0 _ ht L (Rope (silica s))).pay (hue Q (s,d,p))).under le_rfl le_rfl (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (h _) ((rope_h (silica s)).trans (ston s))) (norm_nonneg _)) -- tune
    unfold ValueQ; rw [show hue Q (s,d,p)=0 from (reports (hq s p) hr).2.1 _ hv,zero_smul,norm_zero,zero_mul]; exact CakeF.zeroP le_rfl
 have hx:=he.ledger 0 (by simp); exact ⟨he,(asideF (hx.smooth.of_le (by exact_mod_cast hj)) _ (prism.sumZ _ _ _ (fun i _=>dab_p Q _))).1⟩ -- tune
end YM.CF.Rel
