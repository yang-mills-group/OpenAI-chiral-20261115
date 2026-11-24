import YM.CF.Vp929.Law.Parch
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function
open scoped Classical
namespace Rooms
variable {L K : Set Rooms} {r t:Rooms→ℕ}{x y z:Rooms} {a b c R:ℕ}

def Stiff (L:Set Rooms)(B θ:ℕ) :Prop:=∀ x∈L,∀ y∈L,Range B x.foot y.foot →∀ (i:Axis) p q,(x i).tips p→(y i).tips q→ p=q ∨ (q-p).natAbs ≥ θ
-- for every batch room endpoint follows to some L coordinate.Diameter.
lemma closeFoot(p:x≤y)(v:y.bounded R): Range R x.foot y.foot:= within v (x.foot_in.trans p) y.foot_in
lemma nearMeeting(p:x.meets y)(v:y.bounded R)(t:x.bounded a) : Range (a+R) x.foot y.foot:= by obtain ⟨c,i,j⟩:=p; exact (within t x.foot_in i).trans (within v j y.foot_in)
lemma cutKeeper {i:Axis}{v:ℤ}(p:diced L x y)(e:(x i).tips v) : v∈ Cuts L y i:= by
 rcases e with e|e; · exact e ▸ (p i).low
 exact e ▸ (p i).high
lemma fac_tip{i:Axis}{v:ℤ}(t:x.facet y)(p:(x i).tips v): (y i).tips v:=by
 obtain ⟨j,t,z,h,rfl⟩:=t; by_cases e:j=i; subst i; rw [Function.update_self] at p; obtain (rfl|rfl):=p; exact h; exact h
 rwa [Function.update_of_ne (Ne.symm e)] at p
variable (h:Canopy L r R)
local notation "B'" j:max=> batch r L j
include h
lemma stem(j:ℕ)(p:x∈ B' j)(i:Axis)(v:ℤ)(e:(x i).tips v) :∃ y∈L,Range ((j+1)*4*R) x.foot y.foot ∧ (y i).tips v:=by
 induction j generalizing x with
 | zero=>
   obtain ⟨y,p,u,t⟩:=p; obtain ⟨z,k,H,e⟩:= cutKeeper u e; let D:= (closeFoot (diced_le u) (h.ample _ p)); refine ⟨z,k,(D.trans (nearMeeting (meet_comm H) (h.ample _ k) (h.ample _ p))).mono ?_, e⟩; omega
 | succ j ih=>
   obtain ⟨y,⟨z,u,k⟩,H,t⟩:=p; obtain ⟨f,⟨w,m,g⟩,F,E⟩:= cutKeeper H e; obtain ⟨y',g',k',u'⟩:=ih m (fac_tip g E); let p:=shoulder h _ u; let w':=shoulder h _ m; let Y:= bounded_of_le (proper g).1 w'; refine ⟨y',g',(Range.trans (Range.trans (Range.trans (closeFoot (diced_le H) (bounded_of_le (proper k).1 p)) (nearMeeting (meet_comm F) Y (bounded_of_le (proper k).1 p))) (closeFoot (proper g).1 w')) k').mono ?_, u'⟩; simp only [Nat.add_mul]; omega
-- strength: width ≥ B
abbrev Wide (B:ℕ)(x:Rooms):Prop:=∀ i∈x.doors,(x i).a+B ≤ (x i).b
lemma rent(j:ℕ) (p:x∈ B' j) (u:Stiff L (100*R) a) : Wide a x:=by
 intro i e; let X:= x.foot; let b:= (x i).b; let k:4≥j:= (by have hz:= cards h j p; omega); obtain P:=stem h j p i; obtain ⟨x₀,l0,v0,w0⟩:=P (X i) (Or.inl rfl); obtain ⟨y,u1,v1,w1⟩:=P b (Or.inr rfl); let q: (j+1)*4*R+ (j+1)*4*R ≤100*R:=by rw [←Nat.add_mul]; gcongr; omega
 have H: X i < b:= intro_door.1 e; rcases u x₀ l0 y u1 ((v0.symm.trans v1).mono q) _ _ _ w0 w1 with h|h; all_goals change X i+↑a ≤ b; omega

end Rooms
end YM.CF.VolumeCape
