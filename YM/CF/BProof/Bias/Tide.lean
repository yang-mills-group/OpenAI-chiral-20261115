import YM.CF.BProof.Fig.Sight
import YM.CF.BProof.Bias.Range
/-! Fiber sector calculus; X-range over Mark halves driven by Z. Use finite FiniteGaugeData
momenta including their exact half-odd shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev Globe (N:Side) := Site N → Op SpinIdx
abbrev relic (F:Globe N):= Fig.liftA (paint F)
def air (N:Side): UNI (Single N):= liftA.tone (overU N SpinIdx)
abbrev fsite(i:Single N):= i.1.1
def plane(F:Globe N): Op (Single N):= liftA (jump (Equiv.refl _) F)
lemma relic_plane(F: Globe N): relic F = twist (air N) (plane F):= liftA.twists ..
lemma relic_zero : relic (0: Globe N)=0:=by
 rw [relic_plane]; unfold plane; rw [show jump _ _ = (0:Op (Page N)) from ?_]; swap; · ext i j; simp [jump_apply] -- tune
 rw [show liftA (0:Op (Page N))=0 from ?_,map_zero]; ext; simp [liftA]
lemma relic_one : relic (1:Globe N)=1:=by exact (congrArg liftA paint_one).trans liftA.one
lemma relic_mul (F H: Globe N): relic F * relic H=relic (F*H):=by rw [← liftA.prod, paint_mul]; rfl
lemma relic_sub (F H: Globe N): relic F - relic H=relic (F-H):=by rw [← liftA.sub, paint_sub]; rfl
lemma relic_add (F H: Globe N): relic F+relic H= relic (F+H) := by rw [←eq_sub_iff_add_eq,relic_sub,add_sub_cancel_right] -- tune
lemma relic_star (F:Globe N): star (relic F)= relic (star F):=by rw [← liftA.ast, paint_ast]; rfl
lemma relic_r (F:Globe N)(c:ℝ) : c • relic F= relic (c • F):=by rw [← liftA.smr, paint_smr]; rfl
lemma relic_mono(F G: Globe N)(h:∀ i,F i≤ G i) : relic F ≤ relic G:= liftA.mono (paint_mono h)
lemma relic_up {F: Globe N}{b:ℝ}(p:0≤b)(h:∀ i, ‖F i‖ ≤b): ‖relic F‖≤b := by
 rw [←sq_le_sq₀ (norm_nonneg _) p]; let A:= relic F; have he: ‖star A*A‖≤ b^2:= betweenNorm (sq_nonneg _) (star_mul_self_nonneg _) (by unfold A; rw [relic_star,relic_mul,← relic_one,relic_r]; exact relic_mono _ _ (fun i=> (sized _).trans (smul_le_smul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg (F i)) (h i) 2) (zero_le_one' (Op SpinIdx)))))
 simpa only [CStarRing.norm_star_mul_self,A,pow_two] using he
lemma relic_scalar(F: Globe N)(v:ℂ): v • relic F=relic (v • F):=by
 rw [relic_plane,relic_plane,twist_formula,twist_formula]; rw [← Algebra.smul_mul_assoc,← Algebra.mul_smul_comm] -- tune direction
 congr 2; ext ⟨x,a⟩ ⟨y,b⟩; simp [liftA,plane,jump_apply]; split <;> first| ring|simp
lemma relic_shift (i:Axis) : axisShift N i=relic (fun z=> phase (pm z i) • 1):=by rw [axisShift,cookHop]
-- spectral cuts
abbrev thinK(S:Finset (Site N)): Globe N:=fun i=> if i∈ S then 1 else 0
def modality (S:Finset (Site N)) :=relic (thinK S)
lemma plane_thin (S:Finset (Site N)): plane (thinK S)=cutM (univ.filter fun i=>fsite i∈S):=by
 ext ⟨⟨x,b⟩,a⟩ ⟨⟨y,c⟩,l⟩; by_cases h:x=y <;> by_cases t:b=c<;> by_cases g:a=l<;> by_cases u:y∈S <;> simp [u,cutM,liftA,plane,jump_apply,thinK,h,t,g,Matrix.one_apply,fsite] -- tune
lemma mode_p (S:Finset (Site N)) : IsStarProjection (modality S):=by
 constructor; · unfold IsIdempotentElem modality; rw [relic_mul]; apply congrArg; funext i; by_cases h:i∈S <;> simp [thinK,h] -- tune
 unfold IsSelfAdjoint modality; rw [relic_star]; apply congrArg; funext i; by_cases h:i∈S <;> simp [thinK,h]
lemma mode_o :modality (univ:Finset (Site N))=1:=by unfold modality; rw [show thinK (univ:Finset (Site N))=1 from funext (fun i => if_pos (mem_univ i)), relic_one]
lemma mode_e:modality (∅:Finset (Site N))=0:=by unfold modality; rw [show thinK (∅:Finset (Site N))=0 from funext (fun i=> if_neg (notMem_empty i)),relic_zero]
lemma mode_comm (S:Finset (Site N))(F:Globe N): Commute (modality S) (relic F):=by unfold Commute SemiconjBy modality; rw [relic_mul,relic_mul]; apply congrArg; funext i; by_cases h:i∈S <;> simp [thinK,h]
lemma mode_inter (S T:Finset (Site N)): modality S*modality T=modality (S∩T):=by unfold modality; rw [relic_mul]; apply congrArg; funext i; by_cases g:i∈S<;> by_cases h:i∈ T <;> simp [thinK,g,h]
lemma mode_sub {S T:Finset (Site N)}(h:S⊆T):modality T*modality S=modality S:=by rw [mode_inter,inter_eq_right.mpr h]
lemma relic_sum (I:Type)[Fintype I][DecidableEq I](s:Finset I)(F:I→Globe N): ∑ i∈s,relic (F i)=relic (∑ i∈s,F i) := by
 induction s using Finset.induction_on with
 | empty=>simp [relic_zero]
 | @insert i s g ih=> rw [sum_insert g,sum_insert g,ih,relic_add]
end YM.CF.BProof.Bias
