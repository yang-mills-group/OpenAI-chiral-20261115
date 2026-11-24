import YM.CF.Floe.Wake
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable{N:Side}{a b d:ℝ}
def Kelp(N:Side)(a:ℝ):Set (BayP N):= ⋃ i:Own N, ball (skin i.val) a
lemma kelp_o : IsOpen (Kelp N a):= isOpen_iUnion (fun _=> isOpen_ball)
lemma kelp_m {h:BayP N}: h∈Kelp N a ↔ ∃ i: Own N, ‖h-skin i.val‖ < a:=by simp_rw [Kelp,Set.mem_iUnion,mem_ball, dist_eq_norm]
lemma cut_i(g: Geometry N) {x:BayP N}(h:x∈Kelp N a):carryP g x∈Kelp N a:=by
 obtain ⟨Y,t⟩:=kelp_m.mp h; refine kelp_m.mpr ⟨toss g Y,?_⟩; rw [show skin (toss g Y).val= carryP g _ from (scene ..).symm,thinP]; exact t
lemma cut_j {x:BayP N}(h:x∈Kelp N a)(p:a ≤ b):x∈Kelp N b:=by obtain ⟨i,g⟩:=kelp_m.mp h; exact kelp_m.mpr ⟨i,g.trans_le p⟩
abbrev uθ(i:Own N)(p:0<a):Kelp N a:=⟨skin i.val,kelp_m.mpr ⟨i,by simpa⟩⟩
def ku : Stage (Site (More N)) (Model N) ↥(Kelp N a) (Geometry N) where
 F:=Tenant.terr _
 home:=carrier N
 drive g x:=⟨carryP g x.val,cut_i g x.property⟩
 eval S x y:= (∑ i∈leaks S, ‖x.val.1 i - y.val.1 i‖)+∑ b:Bool,∑ i∈news S, ‖x.val.2 b i-y.val.2 b i‖
 pos S x y:= by positivity
 includeV h x y:= by -- inspect
   exact add_le_add (sum_le_sum_of_subset_of_nonneg (fun i u=>mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp u).2.1,h (mem_filter.mp u).2.2⟩) (fun _ _ _=>norm_nonneg _)) (sum_le_sum fun i _=>sum_le_sum_of_subset_of_nonneg (fun i u=>mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp u).2⟩) (fun _ _ _=> norm_nonneg _))
local notation "L_"=> ku (a:=a) (N:=N)
def varp:Tag (ku (a:=a) (N:=N)):=⟨(sigK N).run,(sigK N).keeps⟩
lemma ku_cap(N:Side)(a:ℝ):Capacity (ku (a:=a) (N:=N)) quota:=norm_care (Y:=Unit) _ rfl rfl -- args
lemma vow_fee(x y:H0):‖vow x-vow y‖= ‖x-y‖:=by
 have he (b:Bool): ‖(vow x-vow y) b‖=‖x-y‖:=by change ‖vow x _-vow y _‖=_; cases b <;> simp [vow, ←star_sub]
 apply le_antisymm; · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=>(he _).le
 exact ((he true).symm.le).trans (norm_le_pi_norm (vow x-vow y) _)
lemma moment (s:Seal (Site (More N))) (x y:Own N)(p:0<a): (ku (a:=a) (N:=N)).eval s (uθ x p) (uθ y p)=(slotK N).eval s x y:=by dsimp only [ku,uθ,slotK,skin,Tenant.vacancy]; simp_rw [vow_fee]
end YM.CF.Floe
