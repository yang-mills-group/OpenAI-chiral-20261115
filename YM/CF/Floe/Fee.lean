import YM.CF.Floe.H
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c:ℝ}
local notation "D" => Kelp N a
local notation "M"=> Model N
variable (Z:Site N)(i:Axis)
lemma ik(x y:D)(S:Seal (Site (More N))){r: Edges (More N)}(p:r∈leaks S):‖x.val.1 r true-y.val.1 r true‖≤ ku.eval S x y:=by
 unfold ku; dsimp only; apply le_trans (norm_le_pi_norm (x.val.1 r - y.val.1 r) true); exact le_trans (single_le_sum (f:=fun r=>‖x.val.1 r-y.val.1 r‖) (fun _ _=>norm_nonneg _) p) (le_add_of_nonneg_right (by positivity))
lemma rate_a (x y:D) (t:a≤1) (W: Site N) : let S:=bay (terr _) (node W) 2; ‖uhl Z i x.val W-uhl Z i y.val W‖≤4* ku.eval S x y:=by
 intro S; unfold uhl; rw [←smul_sub,norm_smul,seam_norm,one_mul]; let f(x:D)(b: Edges (More N)):= x.val.1 b true; let r:= (node W,i); let w:Edges (More N):=(node W+step i,i); have hz(x:D)(r): ‖f x r‖≤2:= le_trans (check_a _ x.property ..) (by linarith)
 let Δ:=ku.eval S x y; have he(b: Edges (More N))(p:b∈leaks S): ‖f x b-f y b‖≤ Δ:=ik x y S p
 have p : r∈ leaks S:=mem_filter.mpr ⟨mem_univ _,(bay_mem _).mpr (by change separation (node W) (node W)≤_; simp), (bay_mem _).mpr ((oneTouch ..).trans (by omega))⟩; have h:w∈ leaks S:=mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.2,(bay_mem _).mpr (by change separation (node W) (node W+step i+step i) ≤ _; rw [←after]; exact detour W i)⟩; have hv:0≤Δ:=ku.pos ..
 change ‖f x r*f x w-f y r*f y w‖≤_; rw [show f x r*f x w-f y r*f y w=(f x r-f y r)*f x w+f y r*(f x w-f y w) from by rw [sub_mul,mul_sub]; abel]; apply (norm_add_le ..).trans
 exact (add_le_add ((norm_mul_le ..).trans (mul_le_mul (he _ p) (hz ..) (norm_nonneg _) hv)) ((norm_mul_le ..).trans (mul_le_mul (hz ..) (he _ h) (norm_nonneg _) (by norm_num)))).trans_eq (by change Δ*2+2*Δ=4*Δ; ring)
lemma toll_A(x:D)(t:a≤1):‖upx Z i x.val‖≤4:=by
 refine jump_bound _ _ (by norm_num) fun j=>?_ ; have he(v): ‖x.val.1 v true‖ ≤2:=(check_a _ x.property ..).trans (by linarith) -- metavars
 rw [uhl,norm_smul,seam_norm,one_mul]; exact (norm_mul_le ..).trans ((mul_le_mul (he _) (he _) (norm_nonneg _) (by norm_num)).trans (by norm_num))
lemma ah :Continuous (upx Z i):=(jump_cont _).comp (continuous_pi fun j=>by unfold uhl; fun_prop)
lemma uh(i' j':Model N) : Differentiable ℂ (fun x:BayP N=> upx Z i x i' j'):=by
 unfold upx; simp only [jump_apply]; split
 · unfold uhl; -- matrix elem
   simp only [Matrix.smul_apply,Matrix.mul_apply,smul_eq_mul]
   fun_prop
 exact differentiable_const _
lemma ζq : 0 ≤ quota:= (by linarith [Tenant.quota_bound])
-- use one ambient domain
lemma payroll (t:a≤1): Crown (badge D) (varp (a:=a) (N:=N)) varp 1 (fee 1 4 2) (fun x:D=>upx Z i x.val):=by
 refine Crown.sheet (F:=fun x:D=>upx Z i x.val) (ku_cap N a) ζq zero_le_one (upx_g Z i) ((ah ..).comp continuous_subtype_val) (show 0 ≤ (4:ℝ) from by norm_num) 2 (fun j k=>honors D _ ((uh Z i j k).differentiableOn)) (fun x j k p=>?_ ) (fun i' k x=> (norm_entry ..).trans (toll_A _ _ x t)) (fun j k x y=>?_) -- tune
 · have he:advance i j.1≠k.1:=fun e=>p.not_ge (show separation (node j.1) (node k.1) ≤2 from (by rw [←e]; exact detour ..)); simp [upx,jump_apply, he]
 simp only [upx,jump_apply]; split; next h => exact (norm_entry (uhl Z i _ _-uhl Z i _ _) j.2 k.2).trans (rate_a Z i x y t j.1)
 simp only [sub_self,norm_zero]; exact mul_nonneg (by norm_num) (ku.pos ..)
end YM.CF.Floe
