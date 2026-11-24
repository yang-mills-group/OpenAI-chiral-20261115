import YM.CF.BProof.Moment.Priced
import YM.CF.BProof.Grid.Bill

/- Range of a field-valued matrix entry, on either Column or micro supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Prox
open Function Filter Finset Lattice Relation -- Micro through import?
open scoped Topology BigOperators Classical

variable {A:Type*}
abbrev Zone (N:A→A→ℕ→Prop)(S:Finset A)(k:ℕ)(x y:A) := ReflTransGen (fun i j=> i∈S ∧ j∈S ∧ N i j k) x y
def Cohere (N:A→A→ℕ→Prop)(S:Finset A)(k:ℕ): Prop := ∀ x∈ S, ∀ y∈ S, Zone N S k x y

structure Base (A:Type*) [Fintype A] where
 N : A→ A→ℕ→Prop
 dim : ℕ
 start (x k) : N x x k
 symm {x y k}: N x y k→ N y x k
 mono {x y k r}: k≤ r → N x y k→ N x y r
 triangle {x y z r u}: N x y r → N y z u → N x z (r+u)
 dia {S:Finset A}(h: Cohere N S 1) {x y:A} (hx:x∈ S)(hy:y∈S) : N x y S.card
 size (x:A)(k:ℕ) : (Finset.univ.filter (fun y=> N x y k)).card≤ (2*k+1)^dim
 solid (x:A)(k:ℕ) : Cohere N (Finset.univ.filter (fun y=> N x y k)) 1
namespace Base
variable [Fintype A](B:Base A)(x y:A)(k:ℕ)
def ball := Finset.univ.filter (fun y=>B.N x y k)
abbrev Reach (x y:A) := B.N x y k
@[simp] lemma ball_m : y∈B.ball x k ↔ B.N x y k:= by simp [ball]
lemma resides : x∈B.ball x k:= (B.ball_m ..).2 (B.start x k)
lemma shares {y}(h:y∈B.ball x k)(u:ℕ) : B.ball y u⊆ B.ball x (k+u):= fun _ t=> (B.ball_m ..).2 (B.triangle ((B.ball_m ..).1 h) ((B.ball_m ..).1 t))
lemma ball_le (u:ℕ)(h:k≤u): B.ball x k⊆B.ball x u:= fun p hp=> (B.ball_m ..).2 (B.mono h ((B.ball_m ..).1 hp))
abbrev C (S:Finset A):= Cohere B.N S 1
lemma atom [DecidableEq A] : B.C {x}:=by intro i hi j hj; rw [Finset.mem_singleton.mp hi,Finset.mem_singleton.mp hj]
lemma rel [DecidableEq A]{S T:Finset A} (p:B.C S)(q:B.C T)(hx:x∈S)(u:x∈T) : B.C (S∪ T):=by
 have hp(y)(hy:y∈ S ∪ T): Zone B.N (S∪T) 1 x y:=by
   rcases mem_union.mp hy with h|h
   · exact ReflTransGen.mono (fun _ _ ⟨hi,hj,k⟩=>⟨mem_union_left _ hi, mem_union_left _ hj,k⟩) x y (p _ hx _ h)
   exact ReflTransGen.mono (fun _ _ ⟨hi,hj,k⟩=>⟨mem_union_right _ hi,mem_union_right _ hj,k⟩) x y (q _ u _ h)
 have h (y z:A)(H: Zone B.N (S∪T) 1 y z): Zone B.N (S∪T) 1 z y:=by induction H with |refl=> exact .refl|tail _ p ih=>exact .head ⟨p.2.1,p.1,B.symm p.2.2⟩ ih
 intro i hi j hj; exact (h x i (hp i hi)).trans (hp j hj)
lemma pair {S:Finset A}(H:B.C S)(hx:x∈S): S⊆B.ball x S.card:=fun i hi=> (B.ball_m ..).2 (B.dia H hx hi)
end Base
-- Grid instance, maybe disconnected layer `Product I`. use lemma Grid collar Loc. Need `Grid.diameter` via visits.
variable {n:ℕ}{s:Fin n→Side}
theorem diameter {D:Grid.Sites s}(H: Grid.Conn D 1){x y:Grid.Vertex s}(hx:x∈D)(hy:y∈ D): Grid.dist x y≤D.card:= by
 let h:=Grid.dist x y; change h≤_; refine le_trans (card_range h ▸ (card_le_card (t:= D.image (Grid.dist x)) (fun i (u:i∈ Finset.range h)=>?_))) card_image_le; obtain ⟨z,a,v⟩:= Grid.visits_all D H x y hx hy i (mem_range.mp u).le; exact mem_image.mpr ⟨z,a,v⟩
theorem ballGrid (k:ℕ)(x: Grid.Vertex s) {_ : DecidablePred (fun y=> Grid.dist x y≤k)} : Grid.collar ({x}: Finset _) k=Finset.univ.filter (fun y=> Grid.dist x y ≤k):=by ext; simp [Grid.dist_symm x]
theorem collar_solid (k:ℕ)(x: Grid.Vertex s): Grid.Conn (Grid.collar ({x}: Finset _) k) 1 := by
 let S:= Grid.collar ({x}:Finset _) k; have he(u: Grid.Vertex s): u∈S ↔ Grid.dist x u≤k:=by simp only [S,ballGrid,Finset.mem_filter,true_and,mem_univ]
 have H(y)(h:y∈S): Grid.PathIn S 1 x y:= by
    obtain ⟨T,p,q,v,-,f⟩:= Grid.attach x y k ((he y).1 h); exact Grid.path_mono (fun i hi=>(he i).2 (f i hi)) le_rfl (v _ p _ q)
 intro i hi j hj; exact (Grid.sym (H i hi)).trans (H j hj)

def gridBase (s:Fin n→Side) : Base (Grid.Vertex s) where
 N x y k:= Grid.dist x y≤k
 dim:= n
 start x k:=by simp
 symm h:= (Grid.dist_symm ..).trans_le h
 mono k h := h.trans k
 triangle h p:= (Grid.triangle ..).trans (Nat.add_le_add h p)
 size x k:= by erw [← ballGrid k x]; exact (Grid.collar_volume ..).trans_eq (by simp)
 solid x k:= by erw [← ballGrid k x]; exact collar_solid _ _ -- tune
 dia h _ _ hx hy:=diameter h hx hy
end YM.CF.BProof.Prox
