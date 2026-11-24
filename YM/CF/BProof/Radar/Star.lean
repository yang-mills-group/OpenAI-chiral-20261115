import YM.CF.BProof.Radar.Dial
import YM.Corona.Fill
import YM.Lattice.Support
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {A B I U V:Type*}{n: Side}{p d k l m:ℕ}
abbrev Field(s:Side)(A:Type*)(V:Type*) := A→Site s→V
def Sparse(M:Finset I)(d:I→I→ℕ)(l:ℕ):Prop:=∀ x∈M,∀ y∈M,x≠y→ d x y>l
abbrev SplitK (s:Side)(f:Field s A V)(k:ℕ) :=∀ a b:Finset (Site s), (∀ i∈a,∀ j∈b,k<separation i j) → Pen a b f
namespace SplitK
variable {f:Field n A V}
lemma star(u:SplitK n f k)(v:k≤l): SplitK n f l:=fun i j g=>u _ _ (fun x hx y hy=>lt_of_le_of_lt v (g x hx y hy))
lemma bearing(e:Perm (Site n))(h:SplitK n f k)(p:∀ i j,separation (e i) (e j)=separation i j): SplitK n (fun x i=>f x (e i)) k:=by
 intro a b t; apply pen_walk (h (a.map e.toEmbedding) (b.map e.toEmbedding) (by intro i hi j hj; obtain ⟨x,u,rfl⟩:=mem_map.mp hi; obtain ⟨y,v,rfl⟩:=mem_map.mp hj; exact p x y ▸ t x u y v)); all_goals exact fun x y h i p=> h (mem_map_of_mem e.toEmbedding p)
lemma product{g:Field n B U}(t:SplitK n f k)(u:SplitK n g k): SplitK n (fun z:A×B=>fun i=>(f z.1 i,g z.2 i)) k:=fun a b p=> pen_prod (t a b p) (u a b p)
lemma array(J:Type*){U V:J→Type*}(f:∀ i,Field n (U i) (V i))(p:∀ i,SplitK n (f i) k): SplitK n (fun x:(∀ i,U i) => fun y : Site n=> fun i=> f i (x i) y) k:=fun a b u=> pen_array J f (fun i=>p i a b u)
lemma fresh(A:Type*) (s:Side) (k:ℕ) :SplitK s (fun f:Site s→A=>f) k:=fun a b v=>pen_seed (Finset.disjoint_left.mpr fun i p q=> by have ht:=v i p i q; simp at ht)
end SplitK
-- motion under permutation.Deformation equiv variant later.
abbrev Transforms(e:Perm (Site n))(F:Field n A V)(E:Perm A):=∀ f i,F (E f) i= F f (e i)
def facet(s:Signed)(x:Site n): Perm (Site n):= s.actEquiv.toEquiv.trans (Equiv.addLeft x)
@[simp] lemma facet_apply(s:Signed)(x i:Site n):facet s x i=x+s.act i:=rfl
lemma facet_sym(s:Signed)(x i:Site n):(facet s x).symm i=s⁻¹.act (-x+i):=rfl
lemma facet_keeps(s:Signed)(x i j:Site n):separation (facet s x i) (facet s x j)=separation i j:=by simp only [facet_apply,add_comm x,separation_translate,separation_signed]
abbrev Moves(e:Perm (Site n))(f:Field n A V):= ∃ E, Transforms e f E
def Sym(f:Field n A V):Prop:= ∀ s:Signed,∀ i:Site n,Moves (facet s i) f
lemma Transforms.prod{f:Field n A U}{g:Field n B V}{e:Perm (Site n)}{E F}(p:Transforms e f E)(v:Transforms e g F):Transforms e (fun z:A×B=>fun y=>(f z.1 y,g z.2 y)) (Equiv.prodCongr E F):= fun i j=> congrArg₂ Prod.mk (p i.1 j) (v i.2 j)
lemma Sym.prod{f:Field n A U}{g:Field n B V}(p:Sym f)(v:Sym g): Sym (fun z:A×B=>fun y=>(f z.1 y,g z.2 y)):=by intro s i; obtain ⟨E,p⟩:=p s i; obtain ⟨F,v⟩:=v s i; exact ⟨_,Transforms.prod p v⟩
lemma Sym.rain (U:Type*) (s:Side): Sym (n:=s) (fun i:Site s→U=>i):=fun s i=>⟨Equiv.arrowCongr (facet s i).symm (Equiv.refl U),fun _ _=> rfl⟩ -- facet parameters
-- frame covariance & range.Stencil
abbrev region(n:Side)(u:Site n)(l:ℕ):Support n:= halo l {u}
@[simp] lemma reg_in(x y:Site n):y∈region n x k↔ separation x y ≤ k:= by simp [region,halo_spec]
lemma fine (y:Support n)(l:ℕ)(i:Site n)(u:i∈y):region n i l ⊆ halo l y:=fun j p=> halo_spec.mpr ⟨i,u,reg_in ..|>.mp p⟩
lemma corner(x y:Site n)(p:separation x y≤ k):region n y l ⊆ region n x (k+l):=fun i v=>reg_in ..|>.2 ((separation_triangle ..).trans (Nat.add_le_add p (reg_in ..|>.mp v)))
-- local maps on field, with transform by lifting same E.S.Sign sizes.Rate n.
abbrev Uses(f:Field n A U)(g:Field n A V)(l:ℕ):=∀ x:Site n,∀ y z:A,Matches (region n x l) (f y) (f z) → g y x=g z x
abbrev Loyal(f:Field n A U)(g:Field n A V):=∀ s i E,Transforms (facet s i) f E→Transforms (facet s i) g E
section
variable {f : Field n A U}{g:Field n A V}{x:Site n}{t: Uses f g l}
lemma Uses.self: Uses f f l:=fun _ _ _ p=> p (halo_subset l _ (mem_singleton_self _))
lemma Uses.localL (t:Uses f g l)(u:l ≤ k): Uses f g k:=fun i j x h=>t i j x (h.reduce (Corona.halo_mono u (Subset.refl _)))
lemma Uses.many (t:Uses f g l){x y:A}(V:Support n)(p:Matches (halo l V) (f x) (f y)):Matches V (g x) (g y):=fun i h=> t i x y (p.reduce (fine _ _ i h))
lemma Uses.epoch(t:Uses f g l)(u:SplitK n f k): SplitK n g (l+k+l):=fun a b v=> pen_walk (u (halo l a) (halo l b) (by
 intro i hi j hj; obtain ⟨x,hx,U⟩:=halo_spec.mp hi; obtain ⟨y,hy,V'⟩:=halo_spec.mp hj; have ht:=v x hx y hy; have he:= separation_triangle x i y; have hp:=separation_triangle i j y; rw [separation_comm y j] at V'; omega)) _ _ (fun _ _ p=>t.many _ p) (fun _ _ p=>t.many _ p)
variable {𝓧:Field n A B}
lemma Uses.comm(t:Uses f g l)(u:Uses f 𝓧 l):Uses f (fun i j=>(g i j,𝓧 i j)) l:=fun i y z p=> Prod.ext (t i y z p) (u i y z p)
lemma Uses.thenL(t:Uses f g l)(u:Uses g 𝓧 k):Uses f 𝓧 (k+l):=fun i y z p=>u i y z (fun j w=>t j y z (p.reduce (corner i j ((reg_in ..).1 w))))
lemma Loyal.keep(t:Loyal f g)(u:Sym f):Sym g:=by intro s i; obtain ⟨E,h⟩:=u s i; exact ⟨E,t _ _ _ h⟩
lemma Loyal.meet(t:Loyal f g)(u:Loyal f 𝓧):Loyal f (fun i u=>(g i u,𝓧 i u)):=fun i s E p x v=>congrArg₂ Prod.mk (t i s E p x v) (u i s E p x v)
end
end YM.CF.BProof.Mesh
