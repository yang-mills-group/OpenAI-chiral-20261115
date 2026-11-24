import YM.CF.DPress.FD.Warp.Brook
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row Wilson
open Cube (More assembly)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
variable {a:ℝ}{T:Trophy n l u} {I:Type*}[Fintype I] {V:Vision (More n) r I} (U:Plan V l m)(P:Leader T m 5 a)(Q:Valve n (rate a/(m:ℝ))) (x:I) (η μ:Cotton n)(X:Pane n){i j:Seat n}
lemma windowP {S D: MaskU n}{r t:ℕ}(v:r≤t)(h:S⊆ D):halo r S⊆ halo t D:= end_h h v -- order
variable {σ:ℕ}(v:Track l ≤ σ) {e:reach n}
local notation "W"=> Skye.win σ e
lemma broad_g : e.1∈ ends e:=by simp
lemma broad_t : (fromE e).2∈ ends e:=by change e.1+step e.2∈ _; simp
lemma low_h (p:i∈ends e) (h:r≤σ) : brim i r ⊆ Skye.win σ e:= windowP h (singleton_subset_iff.mpr p)
include v
lemma Capt (p:i∈ ends e): halo (globe l+5) (pat U x i)⊆Skye.win σ e:= (rentT U x).trans (low_h p v)
lemma flow_i (p:Disjoint (RG.flags u X) (Skye.win σ e)): flow U P Q x η X e=X e:=by
 have he{i:Seat n}(b:i∈ends e): Grade l u X (pat U x i):= by
    intro y v'; have hp: vessel y l⊆W:= (Finset.Subset.trans (scene _ _ (by omega : globe l+1 ≤ globe l+5)) (Finset.Subset.trans (bit_h v' _) (Capt U x v b)))
    exact disjoint_left.mpr (fun k t y=> disjoint_left.mp p y (hp t))
 rw [flow,if_pos (show mild U u x X (fromE e) from ⟨he broad_g,he broad_t⟩)]
lemma entry_h{X' :Pane n} {x': I}(t:Agrees (Skye.win σ e) X X')(P':0<m)(z:∀ i∈ends e,U.β x i=U.β x' i)(h:Prints η μ (Skye.win σ e)): flow U P Q x η X e=flow U P Q x' μ X' e:=by
 let Y:=X'; let S:= ends e; have hp:∀ i∈ S,Agrees (brim i (Track l)) X Y:=fun i s=> agrees_mono t (Finset.coe_subset.mpr (low_h s v)); have he: ends e⊆ W:= halo_subset ..; have ht:η (pairU (fromE e))=μ (pairU (fromE e)):= h _ he ⟨_,broad_g⟩
 have hv(i:Seat n)(s:i ∈ ends e) :Grade l u X (pat U x i)=Grade l u X' (pat U x' i) := by rw [touch_B (S:=pat U x i) (Y:=X') (agrees_mono t (Finset.coe_subset.mpr (Capt U x v s))), show pat U x i=pat U x' i from congrArg supportT (z i s)]
 have hw(i:Seat n)(s:i∈ends e): realF U P x η X i= realF U P x' μ X' i:= real_K U P x η μ X P' (z i s) (hp i s) (prints_d _ _ h ((halo_subset ..).trans (Capt U x v s)))
 unfold flow; simp only [mild,hv _ broad_g,hv _ broad_t]; split; exact t e (he broad_g) (he broad_t)
 next p=> unfold hand; rw [hw _ broad_g,hw _ broad_t,Q.read _ _ _ ht]
-- Vision pair helpers
lemma pay_Y (b:r≤σ)(p:0<m): (V.pair (Salar n r)).idT (fun c:I×Cotton n=> flow U P Q c.1 c.2 X e) W:=by
 rintro ⟨i,x⟩ ⟨j,y⟩ ⟨t,v'⟩; refine entry_h U P Q i x y X v (fun _ _ _=>rfl) p (fun i' h=>U.consults i' i j ?_) (prints_η x y v'); exact V.le _ _ (low_h h b) i j t
end Turf
end YM.CF.DPress.FD
