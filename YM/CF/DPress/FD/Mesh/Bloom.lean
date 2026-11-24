import YM.CF.DPress.FD.Mesh.Mace
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {r k:ℕ}
open Bifold Deck
namespace Hue
variable {p:ℕ}(m: 2*Koran p r<n.val) (V Y:Deck.X m)
local notation "Xr"=> Site n
local notation "C"=> ψ m V
local notation "D"=> ψ m Y
variable (i: Site n)
theorem around (s:Signed)(x y z: Xr) : separation (aura s x y) (aura s x z)= separation y z:= by change separation (s.act y+x) (s.act z+x)=_; simp
theorem lightT (s:Signed)(x y:Xr): ψ m (light m s x V) y = ψ m V (aura s x y):=by unfold ψ; rw [follows,pal_t]
theorem haloP(X:Support n)(p:Equiv.Perm (Site n))(t:∀ i j,separation (p i) (p j)=separation i j) (r:ℕ): halo r (X.image p)=(halo r X).image p:=by
 ext x; obtain ⟨x,rfl⟩:= p.surjective x; rw [halo_spec]; simp only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]; constructor
 · rintro ⟨y,h,v⟩; obtain ⟨j,h,rfl⟩:=h; exact halo_spec.mpr ⟨j,h,(t _ _).symm.trans_le v⟩
 rintro v; obtain ⟨y,t',v⟩:=halo_spec.mp v; exact ⟨p y,⟨y,t',rfl⟩,(t _ _).trans_le v⟩
abbrev cell(n:Side)(v:Site n)(r:ℕ):Support n:= halo r {v}
lemma cellP (i j:Xr) (r:ℕ): i∈cell n j r↔separation j i ≤ r:=by simp [cell,halo_spec]
-- std sector.Fe.Path.Support. Foot calc at relative anchors.
lemma readT (g:Set.EqOn C D (cell n i (k*r))) : cluster C r i k=cluster D r i k:=by
 induction k with
 | zero=>rw [cluster,cluster]
 | succ K ih=>
    let h:K*r ≤ (K+1)*r:=Nat.mul_le_mul_right _ (by omega); -- fix
    have t:= ih (fun j v=> g ((cellP j i _).2 (((cellP j i _).1 v).trans h))); unfold cluster; rw [t];
    ext x; rw [memo C _ x i, memo D _ x i]; have hv(j:Xr)(v:j∈cluster D r i K)(k:separation x j≤ r) : C j=D j∧C x=D x:=by
       have hp:= (side_C D K j v).2; refine ⟨g ((cellP j i _).2 (hp.trans h)),g ((cellP ..).2 ?_)⟩; exact (separation_triangle i j x).trans ((add_le_add hp ((separation_comm j x).trans_le k)).trans_eq (by rw [add_mul,one_mul]))
    constructor <;> rintro ⟨j,t,p,h⟩ <;> refine ⟨j,t,p,?_⟩; exact (hv j t p).1.symm.trans (h.trans (hv j t p).2); exact (hv j t p).1.trans (h.trans (hv j t p).2.symm)
lemma comp_cost (h:(Role m).looks (cell n i (p*r)) V Y): heap m V i = heap m Y i:= readT m V Y i (fun x p=> congrArg pal (sees m _ V Y h x p))
lemma transportT (s:Signed) (x: Xr) : (heap m (light m s x V) i).image (aura s x)= heap m V (aura s x i):=by
 let S':= aura s x; let V':= ψ m (light m s x V); let w:= C; have he(k:ℕ): (cluster V' r i k).image S'= cluster w r (S' i) k:=by
    induction k with
    | zero=> unfold cluster; rw [image_singleton]
    | succ k ih =>
       ext j; obtain ⟨j,rfl⟩:=S'.surjective j; simp_rw [mem_image, Equiv.apply_eq_iff_eq,exists_eq_right]; unfold cluster; rw [memo V' _ j j,memo w _ (S' j) (S' j),←ih];
       have hp(i y:Xr):separation i y≤ r∧ V' y= V' i ↔ separation (S' i) (S' y)≤r ∧w (S' y)= w (S' i):= by unfold w S' V'; rw [Hue.lightT,Hue.lightT,Hue.around]
       constructor; · intro p; obtain ⟨k,t,u⟩:=p; exact ⟨S' k,mem_image_of_mem _ t,(hp j k).1 u⟩
       intro ⟨i,z,t⟩; obtain ⟨i,v,rfl⟩:=mem_image.mp z; exact ⟨i,v,(hp j i).2 t⟩
 exact he p
end Hue
end YM.CF.DPress.FD
