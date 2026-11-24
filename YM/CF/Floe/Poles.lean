import YM.CF.Floe.Fee
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 16000
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a:ℝ}
local notation "D" => Kelp N a
local notation "M"=> Model N
local notation "S"=>varp (a:=a) (N:=N)
variable(i:Bool)
def mark (i:Bool)(x:BayP N):Op (Model N):=jump (Equiv.refl _) fun k=> x.2 i k true
lemma krp : Inter (varp (a:=a) (N:=N)) ((varp (a:=a) (N:=N)).reverseV) (fun x:D=> mark i x.val):=by
 intro g y; let A:=conjG matter (g ∘ node (N:=N)); change mark i (carryP g y.val)*(cc A.val)=A.val * _; simp only [A,conjG,mark,jump_cc,jump_mul,Equiv.refl_trans]; apply congrArg; funext x; let v:=αp (g (node x)); let z:=ccU v; let X:=y.val.2 i x true
 change (v.val * X* star z.val)* z.val = _ ; rw [mul_assoc,z.property.1,mul_one]; rfl
lemma mark_rate(x y:D)(z:Site N)(X:Seal (Site (More N)))(p:z∈news X):‖x.val.2 i z true-y.val.2 i z true‖ ≤ ku.eval X x y:=by
 let T(j:Bool)(w: Site N):ℝ:= ‖x.val.2 j w-y.val.2 j w‖; have hp(j w):0≤T j w:=norm_nonneg _; calc
 _ ≤ T i z := norm_le_pi_norm (x.val.2 i z-y.val.2 i z) true
 _ ≤ ∑ j∈news X,T i j:=single_le_sum (fun j _=>hp i j) p
 _ ≤ _:= (single_le_sum (f:=fun b=> ∑ j∈news X,T b j) (fun i _=> sum_nonneg (fun j _=> hp i j)) (mem_univ i)).trans (le_add_of_nonneg_left (sum_nonneg (s:=leaks X) (f:=fun i=>‖x.val.1 i-y.val.1 i‖) fun _ _=> norm_nonneg _))
lemma markC: Continuous (mark (N:=N) i):=(jump_cont _).comp (continuous_pi fun j=>by fun_prop)
lemma markV(j k: M): Differentiable ℂ fun x:BayP N=> mark i x j k:=by
 unfold mark; simp only [jump_apply]; split; swap; exact differentiable_const _
 fun_prop
lemma mark_t (t:a≤1): Crown (badge D) (varp (a:=a) (N:=N)) ((varp (a:=a) (N:=N)).reverseV) 1 (fee 1 2 0) (fun x:D=>mark i x.val):=by
 refine Crown.sheet (F:= fun x:D=>mark i x.val) (ku_cap N a) ζq zero_le_one (krp i) ((markC ..).comp continuous_subtype_val) (by norm_num: (0:ℝ)≤ 2) 0 (fun j k=>honors D _ ((markV i j k).differentiableOn)) ?_ ?_ ?_
 · intro x j k h; have he: j.1 ≠ k.1:= by intro hj; change 0<separation (node j.1) (node k.1) at h; rw [hj,separation_self] at h; omega
   simp [mark,jump_apply,he]
 · intro j k x; unfold mark; rw [jump_apply]; split; swap; simp
   next w => exact (norm_entry (x.val.2 i j.1 true) _ _).trans ((check_b _ x.property ..).trans (by linarith))
 intro j k x y; let X:= bay (terr (More N)) (node j.1) 0; have he:0 ≤ ku.eval X x y:= ku.pos ..; unfold mark; simp only [jump_apply]; split
 · exact (norm_entry (x.val.2 i j.1 true-y.val.2 i j.1 true) j.2 k.2).trans ((mark_rate i x y j.1 X (by unfold X; simp [news,terr])).trans (by change _≤ 2*ku.eval X x y; linarith))
 rw [sub_self,norm_zero]; exact mul_nonneg (by norm_num) he
lemma staticF (A:Op SpinIdx): Crown (badge D) S S 1 (fee 1 ‖A ⊗ₖ (1:Op Slot)‖ 0) (fun _:D=>spin N Slot A):=by
 let T:=spin N Slot A; refine Crown.sheet (ku_cap N a) ζq zero_le_one ?_ continuous_const (norm_nonneg _) 0 ((badge D).base _) ?_ ?_ ?_
 · intro g x; let Y:=conjG matter (g ∘ node (N:=N)); exact ((congrArg (· * Y.val) (twist_spin (N:=N) matter (g ∘ node) A)).symm.trans (twist_product ..))
 · intro x j k h; have he: j.1 ≠ k.1:= by intro hj; change 0<separation (node j.1) (node k.1) at h; rw [hj,separation_self] at h; omega
   simp [spin, jump_apply, he]
 · intro i j x; exact (norm_entry ..).trans (jump_bound _ _ (norm_nonneg _) (fun _=>le_rfl))
 intro i j x y; simp only [sub_self,norm_zero]; exact mul_nonneg (norm_nonneg _) (ku.pos ..)
end YM.CF.Floe
