import YM.CF.BProof.Radar.Star
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {n:Side}{A B I U V:Type*}{l r d k:ℕ}
open Tetra Wrap
-- fixed pallet family independent n
abbrev shell(l:ℕ):Finset Cover:= Icc (fun _=>- (l:ℤ)) (fun _=>l)
def Drives (l:ℕ):= ((shell l).erase 0 : Finset Cover) -- value not type
lemma shell_in (x:Cover)(l:ℕ): x∈shell l ↔ ∀ i,(x i).natAbs ≤ l:=by
 rw [shell,mem_Icc]; constructor
 · rintro ⟨t,w⟩ i; specialize t i; specialize w i; dsimp only at t w; omega
 intro p; exact ⟨fun i=>by specialize p i; dsimp only; omega,fun i=>by specialize p i; dsimp only; omega⟩
lemma shell_start(l:ℕ): (0: Cover)∈shell l:=(shell_in ..).2 (by simp)
lemma shell_recover (u:2*l<n.val){v:Cover}(h:v∈shell l):lift (Lattice.wrap n v)=v:=by rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩; have he:=(shell_in ..).1 h i; omega
lemma shell_skip (u:2*l<n.val)(v:Drives l):wrap n (v:Cover)≠0:=by intro h; have he:= shell_recover u (Finset.mem_of_mem_erase v.property); rw [h] at he; exact (Finset.mem_erase.mp v.property).1 (he.symm.trans (by ext i; simp [lift]))
lemma shell_weight (v:Cover)(h:v∈shell l):pdist (wrap n v) ≤ l:=Finset.sup_le fun i _=> (Corona.lap (n:=n) v i).trans ((shell_in ..).1 h i)
lemma shell_hits(x:Site n)(h:pdist x ≤ l): lift x∈shell l := (shell_in ..).2 (fun i=> (component_le ..).trans h)
lemma shell_signed(x:Cover)(s:Signed):s.act x∈shell l ↔ x∈shell l:=by
 have he (x:Cover)(s:Signed)(p:x∈shell l):s.act x∈shell l:=(shell_in ..).2 (fun i=>by obtain ⟨j,rfl⟩:=s.perm.surjective i; rw [Signed.act_at]; split <;> simpa using (shell_in ..).1 p j); exact ⟨fun p=>by simpa using he _ s⁻¹ p,he x s⟩

abbrev Together (l:ℕ)(n:Side):= ∀ i:Drives l,Hill (Lattice.wrap n i.val)
lemma together (h:2*l<n.val):Nonempty (Together l n):=by haveI(v:Drives l):Nonempty (Hill (Lattice.wrap n v.val)):= pull_n _ (shell_skip h v); infer_instance
abbrev TurfL(l:ℕ):= Drives l→ Tone
def grass(l:ℕ)(n:Side)(x:Together l n)(i:Site n):TurfL l:=fun v=> pallet (Lattice.wrap n v.val) (x v) i
local notation "gθ"=> (grass l n)
lemma grass_span (h:2*l<n.val) : SplitK n (grass l n) l:=by
 apply SplitK.array; intro i a b p; let v:= wrap n i.val; have ht(y): separation (y+v) y≤l:= (le_of_eq (show separation (y+v) y = pdist v from by unfold separation; rw [add_sub_cancel_left])).trans (shell_weight _ (Finset.mem_of_mem_erase i.property)); apply known v (shell_skip h i) (Finset.disjoint_left.mpr fun i x y=>by have t:=p i x i y; simp at t)
 · intro i x y; exact (p i x (i+v) y).not_ge (separation_comm .. ▸ ht i)
 intro i x y; exact (p _ y i x).not_ge (ht i)
abbrev OrderC (f:Field n A V)(l:ℕ):=∀ x y:Site n,x≠y→ separation x y≤ l→∀ w,f w x≠f w y
lemma grass_age (h:2*l<n.val) : OrderC (grass l n) l:=by
 intro x y u v w p; let z:=y-x; let k:=lift z; have hv:wrap n k=z:=wrap_lift _; have hk:k∈Drives l:=
    mem_erase.mpr ⟨fun Q=>sub_ne_zero.mpr (Ne.symm u) (show z=0 from hv.symm.trans (Q ▸ map_zero _)), shell_hits z ((separation_comm ..) ▸ v : separation y x ≤ l)⟩ -- tune
 let j:Drives l:=⟨k,hk⟩; apply proper (wrap n k) (shell_skip h j) (w j) x; have he:=congrFun p j; change pallet (wrap n k) _ x=pallet (wrap n k) _ y at he; rw [he,show x+wrap n k=y by rw [hv]; unfold z; abel] -- rewriting v changes w type! tune
lemma grass_moves (i: Site n) : Moves (Equiv.addLeft i) (grass l n):=by choose E p using fun v:Drives l=> city (Lattice.wrap n v.val) i; exact ⟨Equiv.piCongrRight E,fun x a=> funext (fun j=>p j _ _)⟩
-- ordinal const equivalent
abbrev grSize(l:ℕ) := Fintype.card (TurfL l)
def marked (f:Field n A V)[Fintype V] (a:A)(x:Site n):Fin (Fintype.card V):= Fintype.equivFin V (f a x)
lemma order0 {f:Field n A V}[Fintype V](p:OrderC f l): OrderC (marked f) l:= fun x y u v w h=> p x y u v w ((Fintype.equivFin _).injective h)
lemma aware0(f:Field n A V)[Fintype V]:Uses f (marked f) l:=fun i x y p=>congrArg (Fintype.equivFin V) ((Uses.self (l:=l)) i x y p)
lemma move0(f:Field n A V)[Fintype V](e)(p:Moves e f):Moves e (marked f):=by obtain ⟨E,h⟩:= p; exact ⟨E,fun x i=> congrArg _ (h x i)⟩
lemma sym0(f:Field n A V)[Fintype V](t:Sym f): Sym (marked f):=fun i x=> move0 f _ (t i x)
end YM.CF.BProof.Mesh
