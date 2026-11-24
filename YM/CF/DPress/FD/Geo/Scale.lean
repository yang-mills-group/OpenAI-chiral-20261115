import YM.CF.DPress.FD.Mesh.Happy
import YM.Work.E01
/-! Finite dependent local mesh. Use jittered boxes (multiplicity ≤5), with
 max-simplex grid memberships in place of Euclidean Delaunay. Dimension and scaled
 Lipschitz bounds are as in the mesh proof.

 Packing and compatible box widths. All relative to separated net points. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {l:ℕ} {i j:Site n}
namespace Geo
abbrev pole (i j:Site n) := lift (j-i)
abbrev s10 (l:ℕ):=10*l
abbrev close (l:ℕ)(i j:Site n):Prop:= separation i j ≤ s10 l
lemma pitch(x y:Site n)(i:Axis) : (pole x y i).natAbs≤separation x y:= (component_le ..).trans ((separation_comm x y).symm.le)
lemma hurt {S:ℕ}(U:Cover)(p:U∈ box S)(t: 2*S<n.val): lift (wrap n U)=U:=by rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩; obtain ⟨x,y⟩:=box_test.mp p; have v:=x i; have r:=y i; omega -- binder T removed
lemma gift {S:ℕ}{i j:Site n}(p:separation i j≤ S):pole i j∈ box S:=by
 have q(t:Axis): (pole i j t).natAbs≤ S:= (pitch i j t).trans p; rw [box_test]; constructor <;> intro t <;> have u:= q t<;> omega -- constructor reduc?
lemma pole_s(p:close l i j)(t:2*s10 l<n.val)(s:Signed)(x:Site n): pole (aura s x i) (aura s x j)= s.act (pole i j):=by
 have ht:wrap n (s.act (pole i j))=aura s x j-aura s x i:=by change wrap n _ = s.act j+x - (s.act i+x); rw [←wrap_signed,pole,wrap_lift,Signed.act_sub]; abel
 unfold pole; have hh:=(hurt (s.act (pole i j)) (show _∈ box (s10 l) from (box_covariant (s10 l) s) ▸ mem_image_of_mem _ (gift p)) t); rw [ht] at hh; exact hh
lemma pocket {S T:ℕ}{i j k: Site n}(p:separation i j≤ S)(q:separation i k≤ T)(t:2*(S+T)<n.val):pole j k=pole i k-pole i j:=by
 let U:= pole i k-pole i j; have hx:∀ i', (U i').natAbs≤ S+T:=by intro v; have hv:=(pitch i j v).trans p; have hz:=(pitch i k v).trans q; unfold U; rw [Pi.sub_apply]; omega
 have hp: U∈ box (S+T):=box_test.mpr (by constructor<;> intro i<;> have t:=hx i<;>omega); have he:wrap n U=k-j:=by unfold U pole; rw [_root_.map_sub,wrap_lift,wrap_lift]; abel
 unfold pole; have hg:= hurt U hp t; rw [he] at hg; exact hg
lemma poleV {i j:Site n}{l:ℕ}(t:close l i j)(q:2*s10 l<n.val):pole j i= -pole i j:=by
 have hv:=pocket t ((separation_self i).le) (by simpa using q); rwa [show pole i i=0 from ?_,zero_sub] at hv
 funext s; simp [pole,lift]
-- packing bound via lifted relative coordinates
abbrev pack (K:ℕ):ℕ:= (box K).card
abbrev Lonely (D:Support n)(l:ℕ):Prop:=∀ i∈ D,∀ j∈D,i≠j→l<separation i j
private def codeX (l:ℕ)(i j:Site n):Cover:=fun t=> pole i j t / (l:ℤ)
private lemma codeP {l r:ℕ}(t:0<l){i j:Site n}(p:separation i j≤ r*l): codeX l i j∈ box r:=by
 have hl:0<(l:ℤ):=by exact_mod_cast t
 rw [box_test]; constructor <;> intro u <;> have he:= (pitch i j u).trans p <;> unfold codeX
 · refine (Int.le_ediv_iff_mul_le hl).2 ?_; rw [neg_mul]; rw [← Nat.cast_mul]; omega
 apply Int.ediv_le_of_le_mul hl; rw [← Nat.cast_mul]; omega
private lemma q_cast {a b v:ℤ}(t: 0<v)(p:a/v=b/v) : a-b≤ v:=by
 have he:=(Int.ediv_lt_iff_lt_mul t).1 (show a/v<a/v+1 by omega); have hx:=(Int.le_ediv_iff_mul_le t).1 (p.le); rw [add_mul,one_mul] at he; omega -- fix variable
lemma bill (l r:ℕ)(t:0<l)(D: Support n)(v: Lonely D l)(i:Site n): (D∩cell n i (r*l)).card ≤ pack r:=by
 let S:= D∩cell n i (r*l); let f:=codeX l i; have h:S.image f⊆ box r:=by intro a u; obtain ⟨x,s,rfl⟩:=mem_image.mp u; exact codeP t ((cellP ..).1 (mem_inter.mp s).2)
 have hl:0<(l:ℤ):=by exact_mod_cast t
 refine Eq.trans_le (card_image_of_injOn (show Set.InjOn f S from ?_)).symm (card_le_card h)
 intro a p b q x; by_contra u; let y:=pole i a - pole i b; apply not_le.mpr (v a (mem_inter.mp p).1 b (mem_inter.mp q).1 u); have hy:wrap n y=a-b:=by unfold y pole; rw [_root_.map_sub,wrap_lift,wrap_lift]; abel
 unfold separation; rw [←hy]; apply Work.E01.pdist_wrap_le (n:=n); rw [box_test]; constructor <;> intro j <;> have hh:codeX l i a j=codeX l i b j:=congrFun x j <;> unfold codeX at hh
 · have ht:= q_cast hl hh.symm; unfold y; rw [Pi.sub_apply]; omega
 exact q_cast hl hh
lemma loneL {X Y:Support n}(p:Lonely X l)(t:Y⊆ X): Lonely Y l:=fun i v j q=> p i (t v) j (t q)
end Geo
end YM.CF.DPress.FD
