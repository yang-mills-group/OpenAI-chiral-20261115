import YM.SU5.Selected.Hill.Pools
import YM.Work.F03.Transport
import YM.Bid.Station
import YM.Work.E01
import YM.Work.H03
/-! Upper gauge account. Bad face pulls under signed action, and light core. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Box
open Function Finset Lattice Tree Wilson RG Exterior Pressure Work.F03 Work.E01 Precision MeasureTheory
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}(r:Side){B K R:ℕ}{C:Clip}(S: Finset (Face (Per n))){x y:Site n}{e t:ℝ} {U:Config G n}
-- depth argument. flavors under tilt later
abbrev Plane (n:Side):=Face (Per n)
abbrev Lots (n:Side):= Finset (Plane n)
def menu (U:Config G n)(t:ℝ) : Lots n:= univ.filter fun p=> t<G.chord (faceValue U p)
def Light (B:ℕ)(x:Site n) := recess r B x∧ ∀ i∈ S,region r x≠ region r i.1
variable {r S} {i:Plane n}
lemma Light.small (h: Light r S B x)(p:R≤B): Light r S R x:=⟨smaller h.1 p,h.2⟩
lemma Light.sees (h:Light r S (B+R) x)(p:separation x y≤ B): Light r S R y:=by
 obtain ⟨p,t⟩:= central h.1 ((separation_comm ..).le.trans p); exact ⟨t,p ▸ h.2⟩
lemma Light.taste (h:Light r (menu U t) B x)(f:region r x=region r i.1): G.chord (faceValue U i) ≤ t:=by
 rw [←not_lt]; intro w; exact h.2 _ (mem_filter.mpr ⟨mem_univ _,w⟩) f
variable {s:Signed}
lemma Light.pulls(h:Light r (menu U t) (B+2) (affine s 0 x))(p:separation x i.1 ≤ B): G.chord (faceValue (pull s 0 U) i) ≤ t:=by
 rw [Face.send_price _ _ _ _ _ G.chord_inv (fun u v=>G.chord_conj _ _)]
 let X:= affine s (0:Site n); let y:= (Face.send s 0 i).1
 refine ((show Light r _ ((B+2)+0) (X x) from h).sees (y:=y) ?_).taste rfl
 apply (separation_triangle _ (X i.1) _).trans; refine Nat.add_le_add (by simpa [X,affine] using p) ?_
 rw [separation_comm]; refine Work.E01.sep_touched (Face.send s 0 i) _ ?_; rw [Work.H03.touched_send]; exact mem_image_of_mem _ (base_touched ..)
lemma Light.keep (h:Light r (menu U t) (B+2) (affine s 0 x))(d:0≤t)(k:2 ≤ t*Real.exp ((B:ℝ)/C.relaxation)): PathData.kept C t x (pull s 0 U):=by
 intro i; rcases le_total (separation x i.1) B with p|p
 · exact (Light.pulls h p).trans (le_mul_of_one_le_right d (Real.one_le_exp (by positivity [C.radius_pos])))
 refine (G.chord_le_two _).trans (k.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) d)); exact div_le_div_of_nonneg_right (Nat.cast_le.mpr p) C.radius_pos.le
lemma Light.link (V:(columbia r n).Slice G)(w:U=(columbia r n).drape V)(h:Light r (menu U t) 1 x)(v:Axis)(p:0 ≤t) : G.chord (U (x,v)) ≤ (4*r.val)*t:= cordon _ p (recess_all h.1 v) (fun _ g=>h.taste g.symm) V w
-- distance pulling a signed positive edge
abbrev snip (s:Signed)(i:Axis):= (posDir i).rotate s -- remove implicit n
abbrev scene(s:Signed)(p:Edge (Site n)):= (snip s p.2).used (affine s 0 p.1)
lemma move_by (d:Step)(x:Site n) : separation x (x+d.vec) ≤ 1:=by
 rw [separation_comm,separation, add_sub_cancel_left,Step.vec]; split; rw [pdist_neg]; all_goals exact pdist_step _
lemma go_by (d:Step)(x:Site n) : separation x (d.used x).1 ≤ 1:=by
 unfold Step.used; split
 next hp=> simpa [Step.vec,hp,sub_eq_add_neg] using move_by d x
 simp -- self
lemma scene_by (s: Signed) (p:Edge (Site n)) : separation (affine s 0 p.1) (scene s p).1≤1:=go_by ..
def scrim (U:Config G n) : fieldDir G n 1:= fun b=> G.plog (G.mat (U (b.1,axisEquiv.symm b.2)))
def badge (v: Directions G n): fieldDir G n 1:= fun b=> v (b.1,axisEquiv.symm b.2)
lemma fold_t (p:Edge (Site n))(v:fieldDir G n 1): Exterior.collect G (Bid.pulled v s) p= if (snip s p.2).neg then - Exterior.collect G v (scene s p) else Exterior.collect G v (scene s p):=by
 unfold Bid.pulled Exterior.collect scene snip; simp only [show axisEquiv.symm (coord p.2)=p.2 from axisEquiv.symm_apply_apply _,Prod.mk.eta] -- tune
@[simp] lemma badge_out (v:Directions G n): Exterior.collect G (badge v)=v := by funext p; unfold badge Exterior.collect; simp only [show axisEquiv.symm (coord p.2)=p.2 from axisEquiv.symm_apply_apply _,Prod.mk.eta]
lemma log_it(p:Edge (Site n))(U:Config G n): Exterior.collect G (scrim U) p= G.plog (G.mat (U p)):= congrFun (badge_out (fun p=> G.plog (G.mat (U p)))) p
end YM.Hill.Box
#print axioms YM.Hill.Box.Light.pulls -- tune
