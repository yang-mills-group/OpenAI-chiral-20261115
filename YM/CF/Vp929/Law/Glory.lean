import YM.CF.Vp929.Law.Sort
import YM.CF.Vp929.Law.Stroll
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms March Filter
open scoped Topology Classical
namespace Delta
variable {C d:Side} {χ χ':Cover→ℕ}{x y:Cover} {B n:ℕ}
local notation "H"=> (d.val*C.val)

abbrev tintCode (χ:Cover→ℕ)(x:Rooms):=Encodable.encode (((Rooms.finite x).image χ).toFinset)
lemma token (v:Coloring χ (2*B)): Slayer (tintCode χ) B:=by
 intro a b p q s t; let u:= Encodable.encode_injective t; have h:χ '' b.marks=χ '' a.marks:=by
     have Hx:= congrArg (fun s:Finset ℕ=> (s:Set ℕ)) u;  simpa using Hx
 obtain ⟨y,r,Y⟩:=s; apply March.eq_in; intro z; change z∈ b.marks ↔ z∈ a.marks
 constructor
 · intro e; obtain ⟨x,p',X⟩: χ z ∈ χ '' a.marks:=h ▸ ⟨z,e,rfl⟩; rw [←v x z (((within p p' Y).trans (within q r e)).mono (by omega)) X]; exact p'
 intro e; obtain ⟨x,p',X⟩: χ z∈ χ '' b.marks:= h.symm ▸ ⟨z,e,rfl⟩; rw [←v x z (((within q p' r).trans (within p Y e)).mono (by omega)) X]; exact p'
lemma size_court (x:Cover)(p:ℕ): (court x p).bounded (2*p):=by intro i; change x i+_ ≤ x i- (p:ℤ) +_; omega
lemma rank_court (x:Cover)(p:ℕ)(v:0<p):(court x p).dim=4:=by unfold dim; rw [show (court x p).doors=univ from _]; simp [Axis]; ext i; simp only [mem_univ,iff_true,intro_door]; change x i-(p:ℤ)< x i+p; omega
lemma gathered (z:64*(pinch+1) ≤ d.val)(Q:Coloring χ (1000*H)): Canopy (windQ χ d C) (tintCode χ) (4*H):=by
 let V i:= lotto d C (ballot χ d C i); have hx(i):= culled χ d C z Q i; have hp(i):H+1 ≤ V i:= (hx i).2.1
 refine ⟨?_,?_,?_,token fun x y v=>Q x y (v.mono (by omega))⟩
 · rintro i ⟨x,q,rfl⟩ j; have h:= size_court x (V x) j; change _+ _ ≤_ at h; let v:V x≤ 2*H:= (hx x).2.2; exact h.trans (add_le_add (le_of_eq rfl) (by exact_mod_cast (by omega:2* V x ≤ 4*H)))
 · rintro i ⟨x,q,rfl⟩; exact rank_court x (V x) (by exact (Nat.zero_lt_succ _).trans_le (hp x))
 intro x t; obtain ⟨y,u,v⟩:= exits χ H x.foot; refine ⟨_,⟨y,v,rfl⟩,fun i=>?_⟩; let k:= u i; let he:x.foot i=(x i).a:=rfl; change y i-(V y:ℤ) ≤ (x i).a ∧ (x i).b≤ y i+V y; have h':(x i).b ≤ _+1:= t i; have hb:= hp y; omega
-- Directors chosen ANY min color point; its uniqueness enough for equiv for small rooms
private lemma seek(χ:Cover→ℕ)(X:Rooms) :∃ x:Cover, x∈ X.marks∧ ∀ y∈ X.marks,χ x ≤ χ y:=by
 let q:∃ i:ℕ,∃ x∈X.marks,χ x=i:=⟨_,X.foot,X.foot_in,rfl⟩; obtain ⟨x,e,v⟩:=Nat.find_spec q; exact ⟨x,e,fun y e=> v ▸ Nat.find_min' q ⟨_,e,rfl⟩⟩
def Master(χ:Cover→ℕ)(X:Rooms):Cover:=(seek χ X).choose
lemma at_home (χ:Cover→ℕ)(X:Rooms): Master χ X∈X.marks:=(seek χ X).choose_spec.1
lemma lowT(χ:Cover→ℕ)(X:Rooms)(p:x∈ X.marks):χ (Master χ X) ≤ χ x:= (seek χ X).choose_spec.2 _ p
lemma pick (v:Coloring χ B){X:Rooms} (p:X.bounded B){z:Cover}(t:z∈X.marks)(u:χ z ≤ χ (Master χ X)):Master χ X=z:= v _ _ (within p (at_home χ X) t) (le_antisymm (lowT χ X t) u)
lemma TintCompare {v:Rooms} (u:∀ x∈ v.marks,χ x=χ' x): tintCode χ v=tintCode χ' v:=by unfold tintCode; congr 1; ext p; rw [Set.Finite.mem_toFinset,Set.Finite.mem_toFinset]; constructor <;> rintro ⟨x,e,rfl⟩ <;> first | exact ⟨x,e,u x e⟩ | exact ⟨x,e,(u x e).symm⟩
end Delta
end YM.CF.VolumeCape
