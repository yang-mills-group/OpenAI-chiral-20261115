import YM.CF.Floe.Bay
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable{N:Side}{a b c:ℝ}
lemma col_n(x:E):‖color matter x‖=1:= CStarRing.norm_of_mem_unitary (color_mem ..)
lemma lift_n(x:Vect)(k:‖x‖=1):‖localPair x‖=1:= CStarRing.norm_of_mem_unitary (localPair_mem _ k)
lemma vow_p(x:H0)(b):‖vow x b‖=‖x‖:=by cases b <;>simp [vow]
lemma sold_a (x y:BayP N)(i j):‖x.1 i j-y.1 i j‖≤‖x-y‖:=le_trans (norm_le_pi_norm ((x-y).1 i) j) ((norm_le_pi_norm (x-y).1 i).trans (norm_fst_le _))
lemma sold_b (x y:BayP N)(b i j):‖x.2 b i j-y.2 b i j‖≤‖x-y‖:=le_trans (norm_le_pi_norm ((x-y).2 b i) j) ((norm_le_pi_norm ((x-y).2 b) i).trans ((norm_le_pi_norm (x-y).2 b).trans (norm_snd_le _)))
lemma check_a (x:BayP N)(h:x∈Kelp N a)(i j):‖x.1 i j‖≤1+a:=by obtain ⟨u,h⟩:=kelp_m.mp h; have he:‖(skin u.val).1 i j‖=1:= (vow_p ..).trans (col_n _); exact (norm_le_norm_sub_add (x.1 i j) ((skin u.val).1 i j)).trans ((add_le_add ((sold_a ..).trans h.le) he.le).trans (add_comm ..).le)
lemma check_b (x:BayP N)(h:x∈Kelp N a)(b i j):‖x.2 b i j‖≤1+a:=by obtain ⟨u,h⟩:=kelp_m.mp h; have he:‖(skin u.val).2 b i j‖=1:=(vow_p ..).trans (lift_n _ (u.property.unit b i)); exact (norm_le_norm_sub_add _ _).trans ((add_le_add ((sold_b x (skin u.val) b i j).trans h.le) he.le).trans (add_comm ..).le)
local notation "D" => Kelp N a
local notation "M" => Model N
variable(Z:Site N)
def uhl(i:Axis)(b:BayP N)(x:Site N):H0:= seam Z x i • (b.1 (node x,i) true*b.1 (node x+step i,i) true)
abbrev upx(i:Axis)(b:BayP N):Op (Model N):=jump (advance i) (uhl Z i b)
lemma uhl_g(i:Axis)(x:Site N)(g:Geometry N)(b:BayP N): uhl Z i (carryP g b) x* (αp (g (node (advance i x)))).val= (αp (g (node x))).val*uhl Z i b x:=by
 let s:=αp (g (node x)); let t:= αp (g (node x+step i)); let v:= αp (g (node x+step i+step i)); let V:= b.1 (node x,i) true; let K:= b.1 (node x+step i,i) true; unfold uhl; rw [show advance i x=x+step i from rfl, Cube.after,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
 apply congrArg; change (s.val*V*star t.val)*(t.val*K*star v.val)*v.val=s.val*(V*K); simp only [mul_assoc]; rw [v.property.1,mul_one, ←mul_assoc (star t.val),t.property.1,one_mul]
lemma upx_g(i:Axis):Inter (varp (N:=N) (a:=a)) varp (fun x:D=>upx Z i x.val):=by
 intro g x; change _* _= _*_ -- tune
 change upx Z i (carryP g x.val)* (conjG matter (g ∘ node (N:=N))).val=_ * upx Z i x.val
 unfold upx; simp only [conjG,varp,sigK]; simp only [jump_mul,Equiv.refl_trans,Equiv.trans_refl]; apply congrArg; funext k; exact uhl_g ..
#check Crown.sheet
