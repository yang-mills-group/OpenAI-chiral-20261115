import YM.CF.BProof.Radar.Spine
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
-- within scale s
abbrev Bary:ℕ:= 1152
lemma bary_age : Bary = 3 * Crop.Native.kSize:=by
 let X:Signed≃ (Equiv.Perm Axis×(Axis→Bool)):=⟨fun x=>(x.perm,x.flip), fun x=> ⟨x.1,x.2⟩, fun _=>rfl,fun _=>rfl⟩; unfold Bary Crop.Native.kSize; rw [Fintype.card_congr X]; norm_num [Fintype.card_perm,Axis,Nat.factorial]
abbrev Halo :ℕ:= 4*(Bary+1) -- s multiple
abbrev King:= 4*(Halo+1)
abbrev SmallN(s:ℕ)(n:Side):Prop:=4*((4*(King*s))+50)<n.val -- avoid dimension collapse.Terrain
local notation "KS"=>King
lemma incrementX(x:Site n)(i:Axis):|(lift x i:ℝ)|≤ pdist x:=by rw [← Int.cast_abs,←Nat.cast_natAbs, Nat.cast_le]; exact component_le ..
lemma quick{s n}(x:Site n)(K:Cover)(h:x=wrap n K)(p:K∈shell (2*(KS*s)))(m:SmallN s n):lift x= K:=by rw [h]; exact shell_recover (show 2*(2*(KS*s))<_ from lt_trans (b:=4*(4*(King*s)+50)) (by omega) m) p
lemma rel_turn (e:Signed)(x y z': Site n)(p:separation x y ≤ 2*(KS*s)) (t:SmallN s n): lift (facet e z' x-facet e z' y) = e.act (lift (x-y)):=by
 apply quick (s:=s) _ _ _ _ t
 · rw [facet_apply,facet_apply,← wrap_signed, wrap_lift, add_sub_add_left_eq_sub, Signed.act_sub]
 exact (shell_signed ..).2 (shell_hits _ p)
lemma rel_sum (x y z': Site n)(h: separation x y ≤ KS*s)(p: separation y z' ≤ KS*s)(m:SmallN s n):lift (x-z')=lift (x-y)+ lift (y-z'):=by
 apply quick (s:=s) _ _ _ _ m; · rw [map_add,wrap_lift,wrap_lift]; abel
 apply (shell_in ..).2; intro i; have ht:=component_le (x-y) i; have he:=component_le (y-z') i; change (lift (x-y) i+lift (y-z') i).natAbs≤_; unfold separation at *; omega

def sizeD(s:ℕ)(x y:Site n):ℝ:=∑ i:Axis,(lift (x-y) i:ℝ)^2/(s:ℝ)^2
lemma size_pos (x y:Site n) : 0 ≤ sizeD s x y:=by unfold sizeD; positivity
lemma size_zero(x:Site n):sizeD s x x=0:=by simp [sizeD,lift]
lemma reor(e:Signed)(x y z': Site n)(p:separation x y≤ 2*(KS*s))(t:SmallN s n): sizeD s (facet e z' x) (facet e z' y)= sizeD s x y :=by
 unfold sizeD; rw [rel_turn e _ _ _ p t,← Equiv.sum_comp e.perm]; simp_rw [Signed.act_at]; apply sum_congr rfl; intro i _; split <;> simp_all
-- Lips on prices at points.Candidates for learner.Prices no flags.
lemma power_le{x y:Site n}{C:ℕ}(p:separation x y ≤ C*s) : sizeD s x y ≤ 4*(C:ℝ)^2:=by
 let N:=pdist (x-y); have he(i:Axis) : |(lift (x-y) i :ℝ)| ≤ C*(s:ℝ):=(incrementX ..).trans (by exact_mod_cast p)
 refine (sum_le_sum (g:=fun _=>(C:ℝ)^2) (fun i _=>?_)).trans_eq (by simp [Axis]); rcases eq_or_ne s 0 with h|h; subst s; simp -- may solved tune
 apply (div_le_iff₀ (show 0< (s:ℝ)^2 by positivity)).mpr; rw [← mul_pow]; nlinarith only [he i,show 0 ≤ |(lift (x-y) i :ℝ)| from abs_nonneg _,sq_abs (lift (x-y) i :ℝ)]
lemma rank_soon{x y:Site n}{C:ℕ}(h:0<s)(p:sizeD s x y≤ (C:ℝ)^2):separation x y≤ C*s:=by
 unfold separation; refine Finset.sup_le ?_; intro i _; have hs:=single_le_sum (s:=univ) (fun b _=>(show 0≤(lift (x-y) b:ℝ)^2/(s:ℝ)^2 by positivity)) (mem_univ i); unfold sizeD at p; have he:= (div_le_iff₀ (show 0<(s:ℝ)^2 by positivity)).1 (hs.trans p); have hk: |(lift (x-y) i:ℝ)| ≤ C*(s:ℝ):=by rw [← sq_le_sq₀ (by positivity :0 ≤ |(lift (x-y) i :ℝ)|) (by positivity : 0 ≤ ↑C*(s:ℝ)),sq_abs,mul_pow]; exact he
 apply (Nat.cast_le (α:=ℝ)).mp; rw [Nat.cast_natAbs,Int.cast_abs,Nat.cast_mul]; exact hk
end YM.CF.BProof.Mesh.Nerve
