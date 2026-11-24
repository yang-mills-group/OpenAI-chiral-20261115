import YM.CF.Vp929.Borel.Memo
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory Relation
open Mesh Lattice Atlas Skye Cane Spire Scroll SU Cube Lat Aerial Sample
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
namespace Gather
variable (n:Side)(r:ℕ)(M:Finset (Seat n))
abbrev Stain(n:Side)(r:ℕ)(M:Finset (Seat n)):= {S:Finset (Seat n)// S.Nonempty∧ ∃ i:reach n,S=soup M r i}
local notation "S_"=>Stain n r M
variable {x y:Seat n}{i:reach n}
abbrev plotTag(e:reach n)(p:(soup M r e).Nonempty):Stain n r M:=⟨soup M r e,p,e,rfl⟩
lemma nigh(e:reach n):separation e.1 (e.1+step e.2)≤1 :=by rw [separation_comm,separation,add_comm,add_sub_cancel_right]; exact pdist_step _
lemma nearby(e:reach n){x y}(p:x∈Skye.ends e)(q:y∈Skye.ends e):separation x y ≤1 :=by
 simp only [Skye.ends,mem_insert,mem_singleton] at p q; obtain rfl|rfl:=p <;> obtain rfl|rfl:=q
 · simp
 · exact nigh n e
 · rw [separation_comm]; exact nigh n e
 · simp
private lemma reflex {x y:Seat n}(p: legs M r x y): legs M r y x:=⟨p.2.1,p.1,separation_comm x y ▸ p.2.2⟩
private lemma cakeV(k:reach n){x y}(p:x∈ Cake M r k)(q:y∈ Cake M r k):legs M r x y:=by
 obtain ⟨a,w,h⟩:= (mem_filter.mp p).2; obtain ⟨b,v,t⟩:= (mem_filter.mp q).2; refine ⟨(mem_filter.mp p).1,(mem_filter.mp q).1,?_⟩; have u:= nearby n k w v; have p:=separation_triangle x a b; have q:=separation_triangle x b y; rw [separation_comm a] at h; omega
private lemma joins (t:x∈soup M r i)(q:y∈soup M r i): ReflTransGen (legs M r) x y:=by
 obtain ⟨u,v,w⟩:= (mem_filter.mp t).2; obtain ⟨d,e,k⟩:= (mem_filter.mp q).2; letI : Std.Symm (legs M r):=⟨fun x y=>reflex n r M⟩; exact ((symm w).tail (cakeV _ _ _ i v e)).trans k
lemma marking(a:S_)(p:x∈a.val) : x∈M:=by obtain ⟨i,h⟩:= a.property.2; rw [h] at p; exact (mem_filter.mp p).1
protected lemma separate(a b:S_)(h:a≠b): stone (More n) a.val b.val (2*r+20):=by
 have u{x:Seat n}(a:S_)(p:x∈a.val){y}(q:ReflTransGen (legs M r) x y)(t:y∈M): y∈a.val:=by obtain ⟨i,h⟩:=a.property.2; rw [h] at p ⊢; apply mem_filter.mpr; obtain ⟨v,w,k⟩:=(mem_filter.mp p).2; exact ⟨t,v,w,k.trans q⟩
 have t(a b:S_)(x y:Seat n)(p:legs M r x y)(e:x∈a.val)(g:y∈b.val): b.val ⊆ a.val:=by intro z v; apply u _ e ((ReflTransGen.single p).trans (by obtain ⟨i,h⟩:= b.property.2; exact joins n r M (h ▸ g) (h ▸ v))); exact marking n r M b v
 intro x e y g; by_contra! k; have l:legs M r x y:=⟨marking n r M _ e,marking n r M _ g,k⟩; exact h (Subtype.ext (Finset.Subset.antisymm (t b a _ _ (reflex n r M l) g e) (t a b _ _ l e g)))

def moat(S:S_)(b:ℕ):= halo (2*b+1) S.val
def Budget(a k:ℕ):Prop:= 2*a+k+1 ≤ r
lemma apart(a b:S_)(h:a≠b)(f k:ℕ)(q:Budget r f k): stone (More n) (moat n r M a f) (moat n r M b f) k:=by
 intro x u y v; obtain ⟨z,g,hx⟩:= halo_spec.mp u; obtain ⟨w,W,hy⟩:= halo_spec.mp v; have t:= Gather.separate n r M _ _ h _ g _ W; have H:=separation_triangle x y w; have P:=separation_triangle z x w; rw [separation_comm w y] at hy; unfold Budget at q; omega
lemma moats (e:reach n)(f:ℕ)(u:f ≤ r)(p:(soup M r e).Nonempty)(q:¬Disjoint M (win f e)) : Read.glow _ e f⊆ moat n r M (plotTag _ _ _ e p) f:=by
 intro x t; obtain ⟨a,g⟩:= (show (M∩win f e).Nonempty from Finset.not_disjoint_iff_nonempty_inter.mp q)
 obtain ⟨r',k⟩:=mem_inter.mp g; obtain ⟨i,j,H⟩:= halo_spec.mp t; have h:= mem_singleton.mp j; subst i; obtain ⟨v,z,w⟩:= halo_spec.mp k
 have W:=nearby n e (x:=e.1) (mem_insert_self ..) z; rw [separation_comm] at W; apply halo_spec.mpr; have t':=separation_triangle a v e.1; have g:=separation_triangle a e.1 x; rw [separation_comm v a] at w; refine ⟨a, soup_p M r e (mem_filter.mpr ?_), by omega⟩
 exact ⟨r',v,z,by rw [separation_comm]; exact w.trans u⟩
end Gather
end YM.CF.VolumeCape.Borel
