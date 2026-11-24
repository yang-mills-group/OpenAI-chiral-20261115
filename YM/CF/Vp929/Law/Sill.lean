import YM.CF.Vp929.Law.Stamina
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function
open scoped Classical
namespace Rooms
variable {L K : Set Rooms} {r t:Rooms→ℕ}{x y z:Rooms} {a b c r' R:ℕ}{o:Cover}
-- membership observable comparing two configurations at same center. bound inferred when already belong either.
structure Aware (L K:Set Rooms) (o:Cover)(r:ℕ) :Prop where
 eq (x:Rooms): Range r o x.foot→ (x∈L ↔ x∈K)
def Chart (l m:Rooms→ℕ)(o:Cover)(B b:ℕ):Prop:=∀ x:Rooms,x.bounded B→ Range b o x.foot→l x=m x
protected lemma Aware.mono(k:Aware L K o b)(p:r'≤b) : Aware L K o r':= ⟨fun x e=> k.eq x (e.mono p)⟩
protected lemma Aware.symm(k:Aware L K o b):Aware K L o b:=⟨fun x e=> (k.eq x e).symm⟩
lemma sliceSpan (t₁:∀ x∈L,bounded x R)(t₂:∀ x∈K,bounded x R)(p:Chart r t o R (a+4*R))(k:Aware L K o (a+4*R)) :Aware (Spread r L) (Spread t K) o a:=by
 have v{L K:Set Rooms}{r t:Rooms→ℕ}(v:∀ x∈L,bounded x R)(u:∀ x∈K,bounded x R)(p:Chart r t o R (a+4*R))(k:Aware L K o (a+4*R)){y:Rooms}(rV:Range a o y.foot)(h:y ∈ Spread r L):y∈Spread t K:=by
   obtain ⟨x,e,q,W⟩:=h; let ux:= v _ e; let h:= diced_le q; let b:= rV.trans (closeFoot h ux); have c(z:Rooms)(t:z.bounded R)(q:z.meets x): Range (a+4*R) o z.foot:= (b.trans (nearMeeting (meet_comm q) t ux)).mono (by omega)
   have H(i):Cuts L x i=Cuts K x i:=by
      ext j; constructor; · rintro ⟨y,v',e,t⟩; exact ⟨y,(k.eq _ (c _ (v _ v') e)).1 v',e,t⟩
      rintro ⟨y,v',e,t⟩; exact ⟨y,(k.eq _ (c _ (u _ v') e)).2 v',e,t⟩
   refine ⟨x,(k.eq _ (b.mono (by omega))).1 e,(fun i=>H i ▸ q i),fun z e w P=>?_⟩; have e':= u _ e; let kV:=c z e' (touch (place w) h); rw [←p x ux (b.mono (by omega)),←p z e' kV]; exact W _ ((k.eq _ kV).2 e) w P
 exact ⟨fun x e=> ⟨v t₁ t₂ p k e,v t₂ t₁ (fun _ e t=> (p _ e t).symm) k.symm e⟩⟩
lemma connects (i p:ℕ)(u:Canopy L r R)(v:Canopy K t R)(e:Chart r t o R (p+(i+1)*6*R))(k:Aware L K o (p+(i+1)*6*R)) : Aware (batch r L i) (batch t K i) o p:=by
 induction i generalizing p with
 | zero=> exact sliceSpan u.ample v.ample (fun x v t=>e x v (t.mono (by omega))) (k.mono (by omega))
 | succ i ih=>
   have h:p+5*R+(i+1)*6*R ≤ p+(i+1+1)*6*R:=by simp only [Nat.add_mul]; omega
   let d:= ih (p+5*R) (fun x v t=> e x v (t.mono h)) (k.mono h)
   have hZ : Aware {z|∃ y∈batch r L i, z.facet y} {z|∃ y∈batch t K i, z.facet y} o (p+4*R):=by
      refine ⟨fun z e=>?_⟩; constructor
      · rintro ⟨y,k,V⟩; exact ⟨y,(d.eq _ ((e.trans (closeFoot (proper V).1 (shoulder u _ k))).mono (by omega))).1 k,V⟩
      rintro ⟨y,k,V⟩; exact ⟨y,(d.eq _ ((e.trans (closeFoot (proper V).1 (shoulder v _ k))).mono (by omega))).2 k,V⟩
   refine sliceSpan (fun x h=>?_) (fun x h=>?_) (fun x v t=>e x v (t.mono (by omega))) hZ
   · obtain ⟨y,k,V⟩:=h; exact bounded_of_le (proper V).1 (shoulder u _ k)
   obtain ⟨y,k,V⟩:=h; exact bounded_of_le (proper V).1 (shoulder v _ k)
end Rooms
end YM.CF.VolumeCape
