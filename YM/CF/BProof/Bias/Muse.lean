import YM.CF.BProof.Bias.Chord
import YM.CF.BProof.Bias.Node
/-! Use phase modulation directly, no choice of anticut. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{v:ℂ}(x y:Site N)
-- only time changes
abbrev disp := ζ (y 0)/ζ (x 0)
lemma disp_ne(p:Per N): ζ p≠0:=Complex.exp_ne_zero _
lemma disp_z (p:Per N):‖ζ p‖=1:= Complex.norm_exp_ofReal_mul_I _
lemma disp_pr : (disp x y)^N.val=1:=by unfold disp; rw [div_pow, show (ζ _)^N.val= -1 from ?_,show (ζ _)^N.val= -1 from ?_]; simp; all_goals unfold ζ; rw [wind_eq,wind_p] -- tune
lemma disp_u : ‖disp x y‖=1:=by unfold disp; rw [norm_div,disp_z,disp_z,div_one]
def pianist := twang (N:=N) (disp x y) (disp_u x y) ht
lemma assist (p:v^N.val=1)(u:‖v‖=1)(i:Axis): let C:=twang v u (N:=N) ht; let f:= if i=0 then v else (1:ℂ); axisShift N i*C.val=f • C.val*axisShift N i:=by
 intro C f; let J:= axisShift N i; ext a b; rw [Algebra.smul_mul_assoc]; unfold C twang; simp only [Matrix.smul_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]; rw [axis_shift i a]; dsimp only; split
 next t=>
   have ht: ht b=ht a+(step i:Site N) 0:=by unfold ht fsite; rw [← t]; rfl
   rw [ht,pitched_add v p]; have he:pitch v ((step i:Site N) 0)=f:=by
     have hf:pitch v (1:Per N)=v:=by simpa using pitched v p 1
     by_cases s:i=0; simp [s,f,hf]; simp [f,step,Ne.symm s,pitch,s]
   rw [he,smul_eq_mul]; ring
 simp
lemma vesper (p:∀ i:Axis,i≠0→x i=y i)(i:Axis): (pianist x y).val * bird x i = bird y i*(pianist x y).val:=by
 let V:=pianist x y; apply modal_bridge i (x i) (y i) V (assist (disp_pr x y) (disp_u x y) i); by_cases s:i=0; rw [if_pos s,s,disp,div_mul_cancel₀ _ (disp_ne _)]; rw [if_neg s,one_mul,p i s]
lemma count (p:∀ i:Axis,i≠0→x i=y i): (pianist x y).val * mode_s x = mode_s y*(pianist x y).val := by
 let V:=(pianist x y).val; have he :=vesper x y p; rw [←bird_l,←bird_l]; let A i:= bird x i; let B i:=bird y i; exact ((((show SemiconjBy V (A 0) (B 0) from he 0).mul_right (show SemiconjBy V (A 1) (B 1) from he 1)).mul_right (show SemiconjBy V (A 2) (B 2) from he 2)).mul_right (show SemiconjBy V (A 3) (B 3) from he 3)) -- parentheses?
lemma disp_l (M:Male)(h:1≤j)(p:∀ i:Axis,i≠0→x i=y i)(w:Per N)(t:x 1=w): ‖zag j M x‖- ‖zag j M y‖ ≤ ‖wiggle (pianist x y) (AngleZ j M w)‖ :=by
 let A:=AngleZ j M w; let T:=mode_s x; let W:=pianist x y; have h1:‖W.val*A*T‖= ‖zag j M x‖:=by rw [mul_assoc,CStarRing.norm_coe_unitary_mul,node_kin M x w ((labelled ..).2 t)]; exact node_zag M h x
 have h2:‖A*W.val*T‖= ‖zag j M y‖:=by rw [mul_assoc,count x y p,← mul_assoc,CStarRing.norm_mul_coe_unitary,node_kin M y w ((labelled ..).2 ((p 1 (by decide)).symm.trans t))]; exact node_zag M h y
 let U:=wiggle W A; have hp: ‖W.val*A*T-A*W.val*T‖= ‖U*T‖:=by rw [norm_sub_rev]; unfold U wiggle; rw [sub_mul]
 rw [← h1, ← h2]; exact (norm_sub_norm_le ..).trans (hp.trans_le ((norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((mode_p ..).norm_le _))))
lemma disp_pitch : ‖disp x y-1‖≤‖pm y 0-pm x 0‖:=by
 let S (t:ℝ):=phase t; let a:= pm y 0; let b:= pm x 0; rw [show disp x y=S (a-b) from (by change phase a / phase b= _; unfold S phase; rw [Complex.ofReal_sub,sub_mul,Complex.exp_sub])]; unfold S phase; rw [mul_comm (↑(a-b):ℂ)]; exact Real.norm_exp_I_mul_ofReal_sub_one_le
end YM.CF.BProof.Bias
