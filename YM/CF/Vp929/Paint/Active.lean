import YM.CF.Vp929.Paint.Sector
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Rooms Lattice Atlas Paint Mesh
open scoped Classical
namespace Ticket
variable {I A B:Type*}[Fintype I]
abbrev Active(p:Ticket I):= {x//p.bill x≠0}
lemma sum_active (p:Ticket I)(f:I→ℤ) : ∑x:Active p,p.bill x.val*f x.val=∑x:I,p.bill x*f x:=by rw [← Finset.sum_subtype (p:=fun x=>p.bill x ≠ 0) (univ.filter (fun i=> p.bill i ≠ 0)) (by simp) (fun x=>p.bill x*f x)]; exact sum_subset (subset_univ _) (fun x _ e=> by simp at e; simp [e])
lemma sum_active_one(p:Ticket I) : ∑x:Active p,p.bill x.val=∑x:I,p.bill x:=by simpa using p.sum_active (fun _=>1)
def Alive(p:Ticket I):Ticket (Active p):=⟨fun v=>p.bill v.val,fun _=>p.nn _,by rw [p.sum_active_one]; exact p.pos⟩
instance present (p:Ticket I): Nonempty (Active p):=by by_contra! h; have u:=p.Alive.pos; simp at u
lemma alive_all(p:Ticket I){f:I→A}{g:I→B}(h:p.Indep f g): p.Alive.Indep (fun x=>f x.val) (fun x=>g x.val):=by
 intro s t; specialize h s t; unfold both at *; unfold Alive; dsimp; rw [sum_active p (fun i=>s (f i)*t (g i)),sum_active_one,sum_active p (fun i=>s (f i)),sum_active p (fun i=>t (g i))]; exact h
end Ticket
namespace Mesh
local notation "N"=>spanR
abbrev Sent(n:Side){r:ℕ}(p:2*(spanR*r)<n.val):= Ticket.Active (κ n p)
variable {r:ℕ}(n:Side)(p:2*(spanR*r)< n.val)(x:Sent n p)
abbrev demand(s:Side){r:ℕ}(p:2*(spanR*r)<s.val):= Ticket.Alive (κ s p)
abbrev patchM(x:Sent n p):= marked n x.val
protected theorem scent :∃ d:ℕ, d= 3*(N*r)∧∀ S T:Finset (Site n),stone n S T d→(demand n p).Indep (Vision S (patchM n p)) (Vision T (patchM n p)):=⟨_,rfl,fun S T h=> Ticket.alive_all _ (indep n p S T h)⟩
protected theorem scented(a b:Cover)(v:Range r a b)(h:(patchM n p x (wrap n a)).1=(patchM n p x (wrap n b)).1):a=b:=by unfold patchM at h; rw [marked_cover,marked_cover] at h; exact proper_code _ (genuine n p _ x.property) a b v h
def revert(s:March):Equiv.Perm (Sent n p):= Equiv.subtypeEquiv (billow n s) (fun i=> by change _↔(κ n p).bill (billow n s i) ≠ 0; rw [pay_sym])
lemma reverts(s:March): (demand n p).bill (revert n p s x)=(demand n p).bill x:=pay_sym n p x.val s
lemma scented_turn(s:March): Follows n (patchM n p (revert n p s x)) (patchM n p x) s:= followers n s x.val
end Mesh
end YM.CF.VolumeCape
