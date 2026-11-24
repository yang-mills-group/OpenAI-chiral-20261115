import YM.CF.BProof.Prox.Base

/- Optional layers for tangential supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Prox
open Function Filter Finset Lattice Relation
open scoped Topology BigOperators Classical
variable {A I : Type*}[Fintype A][Fintype I]

namespace Base
variable (I)(B: Base A)
def lon (x y:I×A)(k:ℕ) := x.1=y.1∧ B.N x.2 y.2 k
variable {I}
private lemma lon_filter (x:I×A)(k:ℕ) {_ : DecidablePred (fun y=>B.lon I x y k)} : univ.filter (fun y=> B.lon I x y k)= {x.1} ×ˢ B.ball x.2 k:=by ext ⟨i,j⟩; simp [lon,eq_comm,and_comm]
lemma lonball (x:I×A)(k:ℕ) : Cohere (B.lon I) ({x.1} ×ˢ B.ball x.2 k) 1 := by
 intro i hi j hj; rcases x with ⟨x,b⟩; rcases i with ⟨i,a⟩; rcases j with ⟨j,a'⟩; simp only [mem_product,mem_singleton] at hi hj; rcases hi with ⟨rfl,hi⟩; rcases hj with ⟨rfl,hj⟩; exact ReflTransGen.lift (fun y:A=>(j,y)) (fun l r ⟨h,g,e⟩=> ⟨mem_product.mpr ⟨mem_singleton_self _,h⟩,mem_product.mpr ⟨mem_singleton_self _,g⟩,rfl,e⟩) _ _ (B.solid b k _ hi _ hj)
lemma alone {x y:I×A}{k:ℕ}{S:Finset (I×A)}(h:Zone (B.lon I) S k x y) : x.1=y.1 := by induction h with|refl=>rfl|tail _ p ih=> exact ih.trans p.2.2.1
lemma line_dia {S:Finset (I×A)}(h:Cohere (B.lon I) S 1){x y:I× A} (p:x∈ S)(v:y∈ S) : lon I B x y S.card :=by
 let T:= S.image Prod.snd
 have ht:B.C T:=by intro o hx u hu; obtain ⟨x,hx',rfl⟩:=mem_image.mp hx; obtain ⟨y,hy,rfl⟩:=mem_image.mp hu; exact ReflTransGen.lift Prod.snd (fun a b ⟨p,q,r⟩=> ⟨mem_image_of_mem _ p,mem_image_of_mem _ q,r.2⟩) x y (h _ hx' _ hy)
 exact ⟨alone B (h _ p _ v),B.mono Finset.card_image_le (B.dia ht (mem_image_of_mem _ p) (mem_image_of_mem _ v))⟩
variable (I)
def layer : Base (I×A) where
 N:= B.lon I
 dim:=B.dim
 start x k:=⟨rfl,B.start x.2 k⟩
 symm h:=⟨h.1.symm,B.symm h.2⟩
 mono h u := ⟨u.1,B.mono h u.2⟩
 triangle h p:= ⟨h.1.trans p.1,B.triangle h.2 p.2⟩
 dia h _ _ hx hy:= B.line_dia h hx hy
 solid x k:= by erw [lon_filter]; exact B.lonball x k
 size x k:= by erw [lon_filter]; rw [card_product,card_singleton,one_mul]; exact B.size x.2 k
end Base
namespace Base
variable (B:Base A)
structure Index (B:Base A) (I:Type*) [Fintype I] where
 port:I→ A
 roof:ℕ
 caps (x:A): (univ.filter (fun i=> port i=x)).card ≤ roof
namespace Index
variable {B} (F:B.Index I)
lemma vent (S:Finset A): (univ.filter (fun x=> F.port x∈ S)).card≤ S.card*F.roof:=by
 apply le_trans (card_le_card (t:= S.biUnion fun i=> univ.filter (fun x=> F.port x=i)) (fun x h=> mem_biUnion.mpr ⟨F.port x,(mem_filter.mp h).2,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)); exact Finset.card_biUnion_le.trans ((Finset.sum_le_sum (fun x h=> F.caps x)).trans (by simp))
lemma vent_ball (x:A)(k:ℕ): (univ.filter (fun y=>F.port y ∈ B.ball x k)).card ≤ (2*k+1)^B.dim *F.roof:= (F.vent _).trans (by gcongr; exact B.size x k)
end Index
def ports (I:Type*)[Fintype I]: B.Index (A × I) where
 port := Prod.fst
 roof:= Fintype.card I
 caps x:= by apply le_trans (card_le_card (t:= {x} ×ˢ (univ:Finset I)) (fun i (hi:i∈univ.filter (fun i:A×I=>i.1=x))=>mem_product.mpr ⟨mem_singleton.mpr (mem_filter.mp hi).2,mem_univ _⟩)); simp
end Base
end YM.CF.BProof.Prox
