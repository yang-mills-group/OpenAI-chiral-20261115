import YM.CF.Vp929.Roof.Screen
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Guide MeasureTheory Palace Mos Mesa Cube Lat Cane Spire Scroll
open scoped Topology Classical NNReal Matrix.Norms.Frobenius
variable (C:Side)(K:ℕ→ℝ)(n:Side)(p:2*(spanR* Bolt C)<n.val)
namespace Read
abbrev Realm(n:Side):= Wilson.Config SU.group n
abbrev Wor(n C:Side):=Site n→Mark (Bolt C)
local notation "R"=> Fringe C
variable (x:Sent n p)
def fetch(W:Wor n C)(i:Site n)(j:Zone (Fringe C)):=W (wrap n j.val+i)
def edition(W:Wor n C)(V:Realm n):Realm n:= fun e=> Cane.display C K (fetch C n W e.1) (expandAt e.1 V) e.2
lemma editionC (W: Wor n C) : Measurable (edition C K n W):=by
 apply measurable_pi_lambda; intro i; exact (Cane.runsM _ _ _ _).comp (measurable_pi_lambda _ fun j=> measurable_pi_apply _)
abbrev point(e: Edge Cover): Edge (Site n):= (wrap n e.1,e.2)
def mold(V:Realm n):Realms:= expandAt 0 V
lemma molding(V:Realm n)(e:Edge Cover): mold n V e=V (point n e):=by simp [mold,expandAt,point]
theorem price (V:Realm n): mold n (edition C K n (patchM n p x) V)= Cane.Q C K (patchM n p x ∘ wrap n) (mold n V):=by
 funext i; rcases i with ⟨o,i⟩; let W:=patchM n p x; let P:= W ∘ wrap n; rw [molding]; change display C K (fetch C n W (wrap n o)) (expandAt (wrap n o) V) i=_
 rw [show fetch C n W (wrap n o)= click C P o by funext; simp [fetch,P,click], show expandAt (wrap n o) V=translate o (mold n V) by funext; simp [mold,expandAt,translate]]; exact display_cover C K P (faith C n p x) (mold n V) ..
-- local dependence for torus kernel in any halo
abbrev glow(n:Side)(i:Edge (Site n))(r:ℕ):Finset (Site n):= halo r {i.1}
private lemma scope{r:ℕ}(v:Cover)(i:Site n)(u:Scope r v) : separation i (wrap n v+i) ≤ r:=by rw [separation_comm,separation,add_sub_cancel_right]; exact Mesh.warp _ _ u
lemma editionL (a b:Realm n)(f t:Wor n C)(i:Edge (Site n))(u:Agrees (↑(glow n i R)) a b)(h: Set.EqOn f t ↑(glow n i R)):edition C K n f a i=edition C K n t b i:=by
 have e(v:Cover)(t:Scope R v): wrap n v+i.1∈glow n i R:= halo_spec.mpr ⟨_,mem_singleton_self _,scope n v i.1 t⟩; unfold edition; rw [show fetch C n f i.1=fetch C n t i.1 from funext fun p=>h (e p.val p.property)]; apply scope0; intro j hj hk; unfold expandAt; refine u _ (e _ hj) ?_; change wrap n j.1+i.1+step j.2∈_; have H:= e _ hk; convert H using 2; simp [add_right_comm]
-- signed motions
variable (s:March)
def pulls(A:Realm n):Realm n:= polarT s.charge ∘ pull s.step (wrap n s.endpt) A
lemma reshape (A:Realm n): mold n (pulls n s A)= s.turns (mold n A):=by
 funext i; rcases i with ⟨a,b⟩; simp only [mold,pulls,expandAt,March.turns, Lattice.pull, add_zero, comp_apply, affine, wrap_signed]; generalize (posDir b).rotate s.step=u; cases h:u.neg <;> simp [Step.read,Step.used,expandAt,h]
lemma mould_inj (a b:Realm n)(h:mold n a=mold n b):a=b:=by
 funext i; obtain ⟨v,j⟩:=i; have e:=congrFun h (Lattice.lift v,j); rw [molding,molding] at e; simpa [point] using e
lemma page_turn (A:Realm n) : edition C K n (patchM n p (revert n p s x)) (pulls n s A)=pulls n s (edition C K n (patchM n p x) A) := by
 apply mould_inj n; rw [reshape,price,price,reshape]; apply matchTurn _ _ _ (faith _ _ _ _) (faith _ _ _ _); intro a; unfold Function.comp; rw [← grid_wrap]; exact Prod.ext ((scented_turn n p x s) _).1 (((scented_turn n p x s) _).2)
end Read
end YM.CF.VolumeCape
