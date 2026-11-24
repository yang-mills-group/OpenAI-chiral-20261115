import YM.CF.BProof.Radar.Plex
import YM.CF.BProof.Radar.March
/- cluster finite-permutation choice. Fields indexed after hue can use value nat even if auxiliary perm dimension includes all torus sites. Cost bound via cluster Vale.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard
open scoped BigOperators Classical
variable {n: Side}{A B:Type*}
namespace Cat
open Rows
variable {S:Support n}{l k r d:ℕ}{x y:Site n}
-- unique score for site in cluster.Stamp natural
def roll (P:March n)(S:Support n)(i:Site n):ℕ := if h:i∈S then (P S ⟨i,h⟩).val else 0
def tag (l r:ℕ)(S:Support n)(P:March n)(i:Site n):ℕ:= roll P (component S l r i) i
lemma tagged_w(P:March n) {x:Site n}: tag l r S P x=(P (component S l r x) ⟨x,warm ..⟩).val:=dif_pos (show x∈component S l r x from warm ..)
lemma tag_age(h:Vale S l r)(P:March n)(p:x∈ S):tag l r S P x<r:=by rw [tagged_w]; exact lt_of_lt_of_le (Fin.isLt _) (h.charge _ _ p)
lemma related (t:Vale S l r)(h:x∈ S)(u:y∈component S l r x)(e:x≠y)(P:March n): tag l r S P x≠tag l r S P y:=by
 intro f; unfold tag at f; rw [connected _ _ t h u,roll,roll,dif_pos (show x∈component S l r x from warm ..),dif_pos u] at f; exact e (congrArg Subtype.val ((P _).injective (Fin.ext f)))
lemma has0 (t:Vale S l r) (p:x∈S)(P:March n) : ∃ y∈component S l r x,tag l r S P y=0:=by
 let Z:=component S l r x; have hv:0< Z.card:= Finset.card_pos.mpr ⟨x,warm ..⟩; obtain ⟨⟨y,hy⟩,h⟩:= (P Z).surjective ⟨0,hv⟩; refine ⟨y,hy,?_⟩; unfold tag roll; rw [connected S l t p hy,dif_pos hy,h]
lemma tag_turn (X:March n)(e:Perm (Site n))(f:∀ i j,separation (e i) (e j)=separation i j){S T:Support n}(p:∀ i,i∈ S↔e i∈ T) (x:Site n) : tag l r S (tumble e X) x= tag l r T X (e x):=by
 rw [tagged_w,tagged_w]; apply tumbles; exact (home S l e _ x p f r).symm
lemma tag_match (X:March n)(x:Site n)(l r:ℕ)(S:Support n): tag l r S (order (r*l) x X) x= tag l r S X x:=by
 rw [tagged_w,tagged_w]; unfold Rows.order; rw [if_pos ⟨warm ..,fun i p=>reg_in ..|>.mpr (size _ _ _ _ _ p)⟩]
lemma tags_p {X Y:March n}{x:Site n}(l r:ℕ){S T:Support n}(p:∀ y:Site n, separation x y ≤ r*l → (y∈ S ↔ y∈ T))(h:col n (r*l) X x=col n (r*l) Y x) : tag l r S X x= tag l r T Y x :=by
 rw [← tag_match X x, ← tag_match Y x, tag,tag, (show component S l r x=component T l r x from shore S l T x r p),(show order (r*l) x X=order (r*l) x Y from h)] -- tune col abbrev
end Cat
end YM.CF.BProof.Mesh
