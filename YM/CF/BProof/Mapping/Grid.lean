import YM.CF.BProof.Grid.Bill
import YM.CF.BProof.Site.Interval
import YM.CF.BProof.Prox.Base

/- wrappable time assignment and dome block compression. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Lattice Finset Function Filter Grid Circle Cube Relation
open scoped Topology BigOperators Classical
variable {s c : Side}(g: Ratio c s)
namespace Posts
variable (a x y:Per s) (k:ℕ)
lemma carry (i:Per c)(p t:ℕ): native g a i (p*g.count.val+t)=native g a (i+p) t:=by unfold native origin; rw [base_add, base_nat]; push_cast; ring
-- along k times ⇒ owner moves by at most k.
lemma castδ (i:Per s) (k:ℕ):Circle.δ i (i+k) ≤ k:= by
 unfold Circle.δ; rw [Cube.d_sym]; unfold Cube.delta1; rw [add_sub_cancel_left]; simpa using Grid.cast_lap (N:=s) (x:=(k:ℤ)) -- tune implicit argument and casts
lemma further (h:along x y≤ k*g.count.val):Circle.δ (owner g a x) (owner g a y) ≤ k:=by
 let t:=stamp g a x; let i:=owner g a x
 let q:=t.val+along x y; let H:=g.count.val; let p:=q/H; let d:=q%H; have he:0<H:=g.count.property; have hd:d<H:=Nat.mod_lt _ he; have hx:y=native g a i q:=by
   nth_rw 1 [←add_along x y]; unfold q; rw [native,Nat.cast_add,← add_assoc,← native,native_stamp]
 have hg:p*H+d=q:= by unfold p d; rw [mul_comm (q/H),Nat.div_add_mod q H] -- add mod
 have hv: p≤ k:= Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul he).2 (by have ht:=t.isLt; change t.val+along x y < (k+1)*H; rw [Nat.add_mul,one_mul]; change t.val < H at ht; change along x y≤k*H at h; omega))
 have hh:owner g a y=i+p:=by rw [hx,←hg,carry,owner_native g _ _ hd]
 rw [hh]; exact le_trans (castδ i p) hv -- tune break newline
lemma post_lip (h:δ x y≤k*g.count.val):δ (owner g a x) (owner g a y)≤ k:= by
 rcases (δle x _ y).1 h with h|h; exact further g a x y k h; unfold Circle.δ; rw [Cube.d_sym]; exact further g a y x k h
lemma house_lip (h:δ x y≤k*g.count.val):δ (block g x) (block g y)≤k:=by simpa [owner,off] using post_lip g 0 x y k h
lemma elder_lip {n:ℕ}(x y:Cubic n s)(k:ℕ)(h:Grid.dist x y≤ k*g.count.val): Grid.dist (elder g x) (elder g y)≤ k:= Grid.dist_le.mpr fun i=> house_lip g _ _ k (Grid.dist_le.mp h i)
lemma elder_close {n:ℕ}(x y:Cubic n s)(k:ℕ)(p:Grid.dist (elder g x) (elder g y)≤ k): Grid.dist x y≤(k+2)*g.count.val:=by
 let X:= grow g (elder g x); let Y:= grow g (elder g y); let t:=g.count.val; have hp : Grid.dist X Y≤k*t:= (reach ..).trans_le (Nat.mul_le_mul_right _ p); have hx:= Grid.close g y; have hy:Grid.dist X Y≤k*g.count.val:=hp; exact (Grid.triangle x X y).trans ((Nat.add_le_add (Grid.close g x) ((Grid.triangle X Y y).trans (Nat.add_le_add hy ((Grid.dist_symm Y y).trans_le hx)))).trans (le_of_eq (by ring)))
-- fiber size for Elder across torus
lemma elder_count {n:ℕ}(x:Cubic n c): (univ.filter fun i:Cubic n s=> elder g i=x).card ≤ g.count.val^n:=by
 let S:=univ.filter fun i:Cubic n s=> elder g i=x; let W(i:Cubic n s)(k:Fin n):= part g (i k); let t:=g.count.val
 apply le_trans (b:=Fintype.card (Fin n→ Fin t)); refine (le_of_eq ((card_image_iff (f:=W) (s:=S)).mpr ?_).symm).trans (card_le_card (subset_univ _)); intro i h j k e; replace h:elder g i=x:= (mem_filter.mp h).2; replace k:elder g j=x:= (mem_filter.mp k).2
 ext p; have he(h:Cubic n s):h p=base g (elder g h p)+(W h p).val:=(glue_block ..).symm; rw [he i,h,he j,k,e]; simp [t]
end Posts
section
/-! compression lemma dependent multi dim. packing variant gives linear estimate, Io hop.-/
variable {n m:ℕ} {s: Fin n→Side} {f:Fin m→Side}(P:Vertex s→Vertex f)(t:Side)(h:∀ k x y, Grid.dist x y ≤ k*t.val → Grid.dist (P x) (P y)≤ k)
lemma trail (S:Sites s)(k:ℕ)(p:Conn S 1)(u:∀ x y,Grid.dist (s:=s) x y≤1→ Grid.dist (P x) (P y)≤k) : Conn (S.image P) k:=by
 intro x hx y hy; obtain ⟨i,t,rfl⟩:= mem_image.mp hx; obtain ⟨j,v,rfl⟩:=mem_image.mp hy; exact ReflTransGen.lift P (fun x y hp=> ⟨mem_image_of_mem _ hp.1,mem_image_of_mem _ hp.2.1,u x y hp.2.2⟩) i j (p i t j v)
include h
lemma compression_conn (S:Sites s)(p:Conn S 1): Conn (S.image P) 1:= trail P S 1 p (fun x y u=> h 1 x y (u.trans (by rw [one_mul]; exact t.property)))
lemma compression (S:Sites s)(r:ℕ)(p:Conn S 1) : (Grid.collar (S.image P) r).card*t.val ≤ (2*(r+2)+1)^m*(S.card+t.val):=by
 obtain ⟨X,hX,hp,q⟩:=Grid.packing S p t.val; let Q:=Grid.collar (X.image P) (r+2)
 have hx : Grid.collar (S.image P) r⊆ Q:=by
   intro x hx; obtain ⟨y,H,g⟩ := Grid.collar_mem.mp hx; obtain ⟨v, hv,rfl⟩:=mem_image.mp H; obtain ⟨z,hx,u⟩:= Grid.collar_mem.mp (q hv); exact Grid.nearby g (Grid.collar_mem.mpr ⟨_,mem_image_of_mem _ hx,h 2 v z u⟩)
 apply (Nat.mul_le_mul_right _ ((card_le_card hx).trans (Grid.collar_volume ..))).trans; let M:=(2*(r+2)+1)^m; change (X.image P).card*M*_ ≤ _; rw [mul_comm (X.image P).card,mul_assoc]; exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _ card_image_le).trans hp) -- syntax ∀ placeholder tune
end
-- compression explicit from posts
variable {k:ℕ}
lemma elders (S:Finset (Cubic k s)) (h:Conn S 1): Conn (S.image (elder g)) 1:= compression_conn (elder g) g.count (fun k x y=> Posts.elder_lip g x y k) S h -- tune x unused remove
lemma port_card (S:Finset (Cubic k s)) (h:Conn S 1)(r:ℕ): (Grid.collar (S.image (elder g)) r).card*g.count.val ≤ (2*(r+2)+1)^k*(S.card+g.count.val):= compression (elder g) g.count (fun k x y=> Posts.elder_lip g x y k) S r h
end YM.CF.BProof.Mapping
