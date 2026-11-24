import YM.CF.BProof.Stave.Iso
import YM.CF.Spire.Jot
/-! With the FiniteGaugeData charge bit ON. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Filter Topology Set NormedSpace -- Matrix
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators ComplexConjugate Classical
variable {I J K:Type*}[Fintype I][fJ:Fintype J][Fintype K]
section
def blink (A:Matrix I J ℂ):Matrix I J ℂ:=A.map star
omit [Fintype I] [Fintype J]
@[simp] lemma blink_R (A:Matrix I J ℂ)(i j): blink A i j=star (A i j):=rfl
lemma blink_apply (g:SU.E): blink (SU.fund g)= SU.fund (Spire.polarT true g):=rfl
@[simp] lemma blink_blink (A:Matrix I J ℂ): blink (blink A)=A:=by ext; simp only [blink_R,star_star]
lemma blink_turn(A:Matrix I J ℂ): blink (Aᴴ)=(blink A)ᴴ:=rfl
lemma blink_smul(A:Matrix I J ℂ)(c:ℝ): blink (c • A)=c • blink A:=by ext; simp
@[simp] lemma blink_zero : blink (0:Matrix I J ℂ)=0:=by ext; simp
@[simp] lemma blink_one [DecidableEq I]: blink (1:Matrix I I ℂ)=1:= by ext i j :1; by_cases h:i=j <;> simp [h, Matrix.one_apply]
lemma blink_sub(A B:Matrix I J ℂ): blink (A-B)=blink A-blink B:=by ext; simp
include fJ
omit [Fintype K] in
lemma blink_mul(A:Matrix I J ℂ)(B:Matrix J K ℂ): blink (A*B)= blink A*blink B:=by change (A*B).map (starRingEnd ℂ)=_; exact Matrix.map_mul
omit [Fintype J]
lemma blink_roll(A:plate I)(g:SU.E): blink (roll A g)=roll (blink A) (Spire.polarT true g):=by rw [roll,roll,blink_mul,blink_apply]
end
lemma blink_norm(A:Matrix I J ℂ): ‖blink A‖=‖A‖:=by simp only [Matrix.frobenius_norm_def,blink_R,norm_star]
@[simp] lemma blink_dist(A B:Matrix I J ℂ):dist (blink A) (blink B)=dist A B:=by rw [dist_eq_norm,← blink_sub,blink_norm,dist_eq_norm]
lemma isometry_blink:Isometry (@blink I J):=Isometry.of_dist_eq blink_dist
lemma king_blink{A:plate I}(h:A∈ King I):blink A∈ King I:=by change (blink A)ᴴ*(blink A)= 1; rw [← blink_turn,← blink_mul,show Aᴴ*A=1 from h]; exact blink_one
lemma Like.blink {A B:plate I}{d:ℝ}(h:Like d A B):Like d (blink A) (blink B):=by
 obtain ⟨u,h⟩:=h; exact ⟨Spire.polarT true u,by rw [← blink_roll, blink_dist]; exact h⟩
end YM.CF.BProof.Mesh.Stave
