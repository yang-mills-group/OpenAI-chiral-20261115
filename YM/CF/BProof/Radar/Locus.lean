import YM.CF.BProof.Radar.Slim
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {A B U V:Type*}{n: Side}{p l d o r:ℕ}
-- net notation
abbrev crowd (f:Field n A Prop)(i:A): Support n:=univ.filter (f i)
abbrev Spotty (f:Field n A Prop)(l r:ℕ):Prop:= ∀ i:A,Sparse (crowd f i) separation l ∧ ∀ x:Site n,x∈ halo r (crowd f i)
namespace Crop
variable (l)

def plant (f: Field n A (Fin p)) : ℕ→Field n A Prop
 | 0=> fun _ _=>False
 | k+1=> fun i x=> plant f k i x ∨ ((f i x).val=k ∧ x∉halo l (crowd (plant f k) i)) -- implicit l? used recursive tune
lemma plantP (f: Field n A (Fin p))(k:ℕ):Uses f (plant l f k) (k*l):=by
 induction k with
 | zero=> intro x y z H; rfl
 | succ k ih=>
   rw [show (k+1)*l=l+k*l by ring]; intro x j v t; have hp(x')(u:separation x x' ≤ l):plant l f k j x'= plant l f k v x':=ih x' j v (t.reduce (corner (l:=k*l) x x' u)); have hs:f j x=f v x:= t (halo_subset _ _ (mem_singleton_self x)); simp only [plant]; rw [hp x (by simp), hs]; suffices x∈halo l (crowd (plant l f k) j) ↔ x∈halo l (crowd (plant l f k) v) by rw [this]
   simp_rw [halo_spec,crowd,mem_filter,mem_univ,true_and]; apply exists_congr; intro i; by_cases w:separation i x≤l; rw [hp _ (separation_comm .. ▸ w)]; simp [w]
-- invariant under any isometry, hence translations. rotation not yet
lemma tent (f:Field n A (Fin p))(Q:Perm (Site n))(g:∀ x y,separation (Q x) (Q y)=separation x y)(E:Perm A)(u:Transforms Q f E)(k:ℕ): Transforms Q (plant l f k) E:=by
 induction k with | zero=> intro i j; rfl| succ k ih=>
   intro x y; simp only [plant]; rw [u x y,ih x y]; suffices y∈halo l (crowd (plant l f k) (E x)) ↔ Q y∈halo l (crowd (plant l f k) x) by rw [this]
   simp_rw [halo_spec,crowd,mem_filter,mem_univ,true_and,show ∀ a, plant l f k (E x) a= _ from ih x]; constructor; rintro ⟨v,t,p⟩; exact ⟨Q v,t,(g ..).trans_le p⟩; rintro ⟨v,t,p⟩; obtain ⟨v,rfl⟩:=Q.surjective v; exact ⟨v,t,(g ..) ▸ p⟩
lemma heaven (f:Field n A (Fin p))(h:OrderC f l): Spotty (plant l f p) l l:=by
 intro i; have hM(k:ℕ): Sparse (crowd (plant l f k) i) separation l ∧ ∀ x:Site n,(f i x).val<k→ x∈halo l (crowd (plant l f k) i) :=by
    induction k with
    | zero=> refine ⟨?_,fun x p=>by omega⟩; intro x hx; simp [crowd,plant] at hx
    | succ k ih=>
       let X:=crowd (plant l f k) i; let Y:=crowd (plant l f (k+1)) i; have hh(x):x∈Y ↔ x∈X ∨ ((f i x).val=k ∧x∉halo l X):=by simp only [X,Y,crowd,mem_filter,mem_univ,true_and]; rfl -- tune
       have H:X⊆Y:=fun x u=> (hh x).mpr (Or.inl u)
       constructor
       · intro x hx y hy e; by_contra! t; rcases (hh x).mp hx with a|⟨p,v⟩ <;> rcases (hh y).mp hy with b|⟨q,w⟩; exact t.not_gt (ih.1 _ a _ b e); exact w (halo_spec.mpr ⟨x,a,t⟩); exact v (halo_spec.mpr ⟨_,b,separation_comm .. ▸ t⟩); exact h x y e t i (Fin.ext (p.trans q.symm))
       intro x u; by_cases z:x∈halo l X; exact Corona.halo_mono le_rfl H z; by_cases t:(f i x).val<k; exact (z (ih.2 _ t)).elim; exact halo_subset _ _ ((hh x).mpr (.inr ⟨by omega,z⟩))
 exact ⟨(hM p).1,fun x=>(hM p).2 _ (f i x).2⟩

namespace Native
abbrev kSize :ℕ:= Fintype.card Signed
local notation "pθ"=> grSize l
abbrev seed(l:ℕ)(n:Side): Field n (Together l n) Prop:= plant l (marked (grass l n)) (grSize l)
theorem haveP (n:Side)(p:2*l<n.val): Spotty (seed l n) l l ∧ SplitK n (seed l n) (pθ*l + (0+l+0) + pθ*l) ∧∀ x:Site n,Moves (Equiv.addLeft x) (seed l n) :=by
 have h:=grass_span p; have hx:=order0 (grass_age p); refine ⟨heaven l _ hx,Uses.epoch (plantP l _ _) (Uses.epoch (aware0 _) h),fun x=>?_⟩; obtain ⟨E,H⟩:=move0 (grass l n) _ (grass_moves x); exact ⟨E, tent l _ _ (fun i j=> by change separation (x+i) (x+j)=_; rw [add_comm x i,add_comm x j,separation_translate]) _ H _⟩ -- tune names Mesh.marked collides Teta inside import
end Native
end Crop
end YM.CF.BProof.Mesh
