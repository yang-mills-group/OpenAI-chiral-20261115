import YM.CF.Vp929.Roof.Read
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Guide MeasureTheory Palace Mos Mesa Cube Lat Cane Spire Scroll Skye Read
open scoped Topology Classical NNReal Matrix.Norms.Frobenius
namespace Paper
variable (C:Side)(K:ℕ→ℝ)(n:Side)
local notation "s"=> More n
variable (p:2*(spanR* Bolt C)<(More n).val) (x:Sent (More n) p)
variable {u v:ℝ}(h:Sweater C (Delta.roofLength granite) K u v)
local notation "Γ" => Fringe C
abbrev Assembly := edition C K s (patchM s p x)
include h
lemma Vow: Basic n (Assembly C K n p x) u v Γ:=by
 have T:=Cane.faith C s p x; let P:= patchM s p x ∘ wrap s; change Trust C P at T; let F:=Assembly C K n p x
 have Q(V:Pane n): mold s (F V)=Cane.Q C K P (mold s V):= Read.price C K s p x V
 have H(V:Pane n)(a:Cover)(v:PlaqAxes): faceValue (mold s V) (a,v)= faceValue V (wrap s a,v):=by unfold faceValue mold; rw [travel_at]; simp
 have R(e:reach n):glow s e Γ⊆ win Γ e:=by intro a k; obtain ⟨y,b,k⟩:= halo_spec.mp k; exact halo_spec.mpr ⟨y,((mem_singleton.mp b).symm ▸ (mem_insert_self ..)),k⟩
 refine ⟨?_, Read.editionC C K _ _,?_,fun V W e z=> Read.editionL C K _ _ _ _ _ _ (agrees_mono z (R e)) (fun _ _=>rfl)⟩
 · intro V; apply Skye.broad; rintro ⟨a,b⟩; obtain ⟨t,E⟩:= (show ∃t:Cover,wrap s t=a from ⟨_,wrap_lift a⟩); change lambda (faceValue (F _) _ )≤_; rw [← E,← H,Q]; exact paying C P T h _ _ _
 intro V z e; obtain ⟨a,i⟩:=z; let Z:=(a,i); let t:=Lattice.lift a; let f:Edge Cover:=(t,i)
 have J:point s f=(a,i):= Prod.ext (wrap_lift _) rfl; change F V _=_; rw [← J,← molding s (F V) f,← molding s V f,Q]; apply glowing C _ T h; intro j t k; rw [H]; by_contra! K'
 have hv: wrap s j∈RG.flags u V:= (RG.flags_spec ..).2 ⟨(wrap s j,k),by simp [RG.touched,visits,square], K'⟩; apply Finset.disjoint_left.mp e hv; apply R; rw [halo_spec]; refine ⟨_,mem_singleton_self _,?_⟩; nth_rw 1 [← wrap_lift a]; exact Mesh.warp_sep _ _ _ t
omit h

lemma bigger {u d:ℝ}{r t:ℕ}{n:Side}{P:Pane n→Pane n}(h:Basic n P u d r)(v:r≤t): Basic n P u d t:=by
 have p(e:reach n):win r e⊆win t e:=fun i k=>by obtain ⟨x,z,y⟩:=halo_spec.mp k; exact halo_spec.mpr ⟨x,z,y.trans v⟩
 exact ⟨h.legal,h.meas,fun V e p'=>h.covers _ _ (p'.mono_right (p e)),fun V W e z=>h.shore _ _ e (agrees_mono z (p e))⟩

def edit(t:Sweep n):March:= ⟨t.s,t.charge,Lattice.lift ((assembly n).embed t.b)⟩
lemma pulling(V:Pane n)(t:Sweep n):pulls s (edit n t) V=flashA t V:=by unfold pulls edit; rw [wrap_lift,revoke]
lemma whirl(t:Sweep n)(V: Pane n) : Assembly C K n p (revert s p (edit n t) x) (flashA t V)= flashA t (Assembly C K n p x V):=by unfold Assembly; rw [←pulling,←pulling]; exact page_turn C K s p x _ V

lemma allayed(t:Sweep n): mend (Assembly C K n p (revert s p (edit n t) x)) t=Assembly C K n p x:=by funext V; rw [Skye.mend,whirl,revB]
end Paper
end YM.CF.VolumeCape
