import YM.CF.BProof.Fig.Mire
import YM.CF.BProof.Fig.Sight

/-! Holes on subwindows. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Fig
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma nup{j:ℕ}(h:1≤j)(w:ℕ)(e:0<w): ∃ d:ℝ, 0<d ∧ ∀ (N:Side)(i:Axis)(u:Bool)(M:Male)(S:Support N), Shut w i S → let V:=bandCut S u; d • V ≤ V*(if u then (spar j M (1:Bkg (More N))) else 1-spar j M 1)*V:=by
 obtain ⟨c,g,X⟩:= sweep h; have hP:0<(w:ℝ)^2:=by exact pow_pos (by exact_mod_cast e) _
 let d:=c/(w:ℝ)^2; refine ⟨d,div_pos g hP,?_⟩; intro N i u M S t V; let P:= bandCut (univ:Support N) u
 let Z:=if u then spar j M (1:Bkg (More N)) else 1-spar j M 1; have he: P*V=V:= cutMono ..; have hs:IsStarProjection P:=cutM_idp _; have ht:IsStarProjection V:=cutM_idp _; have hf:V*P=V:=by nth_rw 1 [← ht.isSelfAdjoint.star_eq]; rw [←hs.isSelfAdjoint.star_eq, ← star_mul, he,ht.isSelfAdjoint.star_eq]
 have hl:= star_left_conjugate_le_conjugate (X N i u M) V; let D:=axisShift N i-1; let L:=star D*D; change star V*(c • (P*L*P))*V ≤ star V*(P*Z*P)*V at hl; rw [ht.isSelfAdjoint,Algebra.mul_smul_comm,Algebra.smul_mul_assoc] at hl
 have hb(A:Op (Single N)): V*(P*A*P)*V= V*A*V:=by rw [←mul_assoc,←mul_assoc,hf,mul_assoc (V*A) P,he]
 exact le_trans (smul_le_smul_of_nonneg_left (show V ≤ (w:ℝ)^2 • (V*L*V) from drain i u S w t) (div_pos g hP).le) (by rw [smul_smul,show d*(w:ℝ)^2=c from div_mul_cancel₀ _ hP.ne']; rw [hb,hb] at hl; exact hl)
end YM.CF.BProof.Fig
