import YM.CF.BPress.Lute.Fifth
/- finite certificate swings for dictionary blocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Finset Filter NormedSpace InnerProductSpace SU SU.Pair Spin Spin.Paint Lattice Fock Complex
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
local notation "π"=>Real.pi
namespace Tile
variable {θ δ l k a b x y:ℝ} (g:Counts θ δ l k a b)
abbrev Two := Fin 2
abbrev chip (x y:ℝ):Op Two:= !![(x:ℂ),(y:ℂ); (y:ℂ),-(x:ℂ)]
lemma in_chip (x y:ℝ): (chip x y)ᵀ=chip x y ∧ star (chip x y)=chip x y:=by constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [chip]
lemma unit_chip (h:x*x+y*y=1): chip x y∈unitary (Op Two)∧ (chip x y).det= -1:=by
 have he:(x:ℂ)*x+(y:ℂ)*y=1:= by exact_mod_cast h
 refine ⟨?_, by rw [chip,Matrix.det_fin_two_of]; linear_combination -he⟩; constructor <;> rw [(in_chip x y).2] <;> ext i j <;> fin_cases i <;> fin_cases j <;> first|exact he|norm_num [chip,Matrix.mul_apply,Two, Fin.sum_univ_succ, Matrix.one_apply]; all_goals first|linear_combination he|ring

abbrev levy (θ:ℝ): Op Two:= Matrix.diagonal ![χ (-2*θ),χ θ]
lemma levy_κ(θ:ℝ): levy θ ∈unitary (Op Two):=by
 let f:Two→ℝ:=![-2*θ,θ]; have he: (fun i=>χ (f i))=![χ (-2*θ),χ θ]:=by funext i; fin_cases i <;> rfl
 unfold levy; rw [←he]; exact Sods.mojo f
-- relative matrix = B^z star B
abbrev board (θ x y:ℝ):=levy θ*chip x y* (levy θ)ᵀ*star (chip x y)
lemma κ_board(h:x*x+y*y=1)(θ:ℝ):board θ x y∈unitary (Op Two):= (unitary _).mul_mem ((unitary _).mul_mem ((unitary _).mul_mem (levy_κ θ) (unit_chip h).1) (by rw [levy,Matrix.diagonal_transpose]; exact levy_κ _)) (star (⟨_,(unit_chip h).1⟩: UNI Two)).property
lemma phases_val (θ:ℝ): χ (-2*θ)*χ θ=χ (-θ) ∧ χ (-2*θ)*χ (-2*θ)=χ (-4*θ) ∧ χ θ * χ θ=χ (2*θ):=by simp_rw [← χ_add]; simp only [show (-2:ℝ)*θ+θ= -θ from by ring,show (-2:ℝ)*θ+-2*θ= -4*θ from by ring,show 2*θ=θ+θ from two_mul θ,true_and]
lemma trace_board(θ x y:ℝ) : (board θ x y).trace=(x:ℂ)*(x:ℂ)*(χ (-4*θ)+χ (2*θ))+2*y*(y:ℂ)*χ (-θ) := by -- tune .
 unfold board; rw [(in_chip ..).2, levy,Matrix.diagonal_transpose]; simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ, Two]; norm_num [-neg_mul,chip,Matrix.diagonal_apply]; obtain ⟨u,v,w⟩:=phases_val θ; rw [←u,←v,← w]; ring
lemma det_board(θ:ℝ)(h:x*x+y*y=1): (board θ x y).det=χ (-θ)*χ (-θ):=by
 unfold board; rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_mul, Matrix.det_transpose,(in_chip ..).2,(unit_chip h).2]; have u:(levy θ).det=χ (-θ):= by rw [Matrix.det_diagonal]; simpa [Two,Fin.prod_univ_succ] using (phases_val θ).1
 rw [u]; ring
include g
lemma peak : Swing (board θ 0 1) ((-2:ℝ)*θ):= by
 rw [show (-2:ℝ)*θ= -θ+-θ by ring]; apply Swing.second (κ_board (by norm_num) _) _ _ (by rw [abs_neg]; exact g.wing) (by rw [abs_neg]; exact g.wing) _ (det_board θ (by norm_num)); rw [trace_board]; norm_num; ring
lemma west : Swing (board θ 1 0) (l+k):=by
 apply Swing.second (κ_board (by norm_num) _) _ _ g.left g.right; · rw [trace_board,g.dTen,g.dF]; norm_num
 rw [det_board θ (by norm_num),g.dTen,g.dF,←χ_add,←χ_add]; congr 1; ring
abbrev m:ℝ:= Real.sqrt (1/2)
omit g
lemma m_sq:m*m=(1/2:ℝ):=Real.mul_self_sqrt (by norm_num)
include g
lemma amid : Swing (board θ m m) (a+b):=by
 have h:m*m+m*m=1:=by rw [m_sq]; norm_num; -- tune indent
 apply Swing.second (κ_board h _) _ _ g.mix_p g.mix_q; swap
 · rw [det_board θ h,g.rock,g.wind,← χ_add,← χ_add]; congr 1; ring
 rw [trace_board,g.rock,g.wind,sub_eq_add_neg,χ_add,χ_add, ←mul_add, sumχ,g.mix];
 obtain ⟨p,q,r⟩:=phases_val θ; have hx:(m:ℂ)*m=1/2:=by rw [← Complex.ofReal_mul,m_sq]; norm_num
 rw [mul_assoc (_:ℂ) (_:ℂ) (m:ℂ), hx, show (χ (-4*θ)+χ (2*θ))=χ (-θ)* (2*(Real.cos (3*θ):ℂ)) from ?_]; push_cast; ring -- tune assoc
 rw [← sumχ, mul_add,←χ_add, ←χ_add, show -θ+- (3*θ)= -4*θ by ring,show -θ+3*θ= 2*θ by ring, _root_.add_comm]; -- tune
end Tile
end YM.CF.BPress.Lute
