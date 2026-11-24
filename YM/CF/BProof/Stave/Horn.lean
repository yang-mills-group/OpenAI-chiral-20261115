import YM.CF.BProof.Stave.Bire
import Mathlib.Data.Matrix.ColumnRowPartitioned
/-! Add disjoint ranges to squeeze in phony frames with Lip germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Metric Filter Topology Finset Sim Extension
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {I J:Type*}[Fintype I][Fintype J]
abbrev Pad(I:Type*) := I ⊕ Fin 5
def lower(A:plate I):plate (Pad I):= Matrix.fromRows A 0
lemma beanH(A:plate I)(B:plate J): (Matrix.fromRows A B)ᴴ *(Matrix.fromRows A B)=Aᴴ*A+Bᴴ*B:=by rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mul_fromRows]
lemma lower_norm(A:plate I): ‖lower A‖=‖A‖:=by rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),size_R,size_R,lower,beanH,Matrix.mul_zero,add_zero]
omit [Fintype I] in
lemma lower_sub(A B:plate I):lower A-lower B=lower (A-B):=by ext i j : 1; cases i <;> simp [lower]
@[simp] lemma lower_dist(A B:plate I): dist (lower A) (lower B)=dist A B:=by rw [dist_eq_norm,lower_sub,lower_norm,dist_eq_norm]
omit [Fintype I] in
lemma roll_lower(A:plate I)(u:SU.E): roll (lower A) u=lower (roll A u):=by rw [roll,lower,Matrix.fromRows_mul,Matrix.zero_mul]; rfl
omit [Fintype I] in
lemma blink_lower(A:plate I): blink (lower A)=lower (blink A):=by ext i j:1; cases i <;> simp [lower]
lemma Like.pad {d:ℝ}{A B:plate I}(h:Like d A B):Like d (lower A) (lower B):= ⟨h.choose,by rw [roll_lower,lower_dist]; exact h.choose_spec⟩
lemma king_lower {A:plate I} (h:A∈ King I):lower A∈ King (Pad I):=by change (Matrix.fromRows A (0:plate (Fin 5)))ᴴ*(Matrix.fromRows A (0:plate (Fin 5)))=1; rw [beanH,Matrix.mul_zero,add_zero]; exact h
lemma plat_c : Continuous (Function.uncurry (@Matrix.fromRows ℂ I J (Fin 5))) := by
 apply continuous_matrix; intro i j; cases i with
 | inl i=> change Continuous fun p:plate I×plate J=> p.1 i j; fun_prop
 | inr i=> change Continuous fun p:plate I×plate J=> p.2 i j; fun_prop
lemma row_price(A B:plate I)(C:plate (Fin 5)) : dist (Matrix.fromRows A C) (Matrix.fromRows B C)=dist A B:=by
 rw [dist_eq_norm,dist_eq_norm,show Matrix.fromRows A C-Matrix.fromRows B C=lower (A-B) from by ext i j :1; cases i <;> simp [lower],lower_norm]

def firmant (v:ℝ):=Real.sqrt (1-v^2)
lemma light (v:ℝ)(h:0≤v)(g:v≤1): firmant v^2+v^2=1:=by rw [firmant,Real.sq_sqrt (by nlinarith)]; ring
lemma firm_c :Continuous firmant := by unfold firmant; fun_prop
def taperL (B:plate I)(v:ℝ):plate (Pad I):= Matrix.fromRows (v • B) ((firmant v) • 1)
lemma king_taper {A:plate I}(h:A∈ King I){v:ℝ}(g:0≤v)(t:v≤1) : taperL A v∈ King _ := by
 change (taperL A v)ᴴ*taperL A v=1; unfold taperL -- first maybe no
 rw [beanH]; simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, Matrix.smul_mul, Matrix.mul_smul, show Aᴴ*A=1 from h, mul_one, smul_smul, ← add_smul]; rw [add_comm,←sq,←sq,light v g t,one_smul]
lemma king_back(I:Type*)[Fintype I]: Matrix.fromRows (0:plate I) (1:plate (Fin 5))∈ King _:=by
 simp only [King,Set.mem_setOf_eq]; rw [beanH]; simp
omit [Fintype I] in
lemma blink_prev(A:plate I)(v:ℝ): taperL (blink A) v=blink (taperL A v):=by unfold taperL; nth_rw 2 [blink]; rw [Matrix.fromRows_map]; change _=Matrix.fromRows (blink (v • A)) (blink (firmant v • (1:plate (Fin 5)))); rw [blink_smul,blink_smul,blink_one]

end YM.CF.BProof.Mesh.Stave
