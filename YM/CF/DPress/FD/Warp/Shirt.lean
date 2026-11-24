import YM.CF.DPress.FD.Warp.Stitch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row
open Cube (More)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
variable {T:Trophy n l u}{a b:ℝ}(P:Leader T m r a)(Y: ClerkK n m (r+1) b)
local notation "Fp"=> TryV P Y
local notation "I"=> Ramp.supportT
lemma foot_S (η μ:Cotton n)(X Z:Pane n)(w:leaf n m)(v: Live w)(u': Clan l (I w))(h:Prints η μ (I w))(q:Agrees (halo (globe l+5) (I w)) X Z)(z:0<m) : Fp η X w=Fp μ Z w:=by
 unfold TryV; simp_rw [touch_B (u:=u) q]; split; swap; · exact P.foot w v u' _ _ _ _ h q
 next t=>
  rw [Y.w_p (I w) η μ]; · exact h (I w) (Finset.Subset.refl _) (wave_eq w v z)
  intro i k; have he:= k; change Live i∧I i⊂ I w at he; have hg:I i⊆I w:= he.2.le; exact P.foot _ he.1 (u'.mono hg) _ _ _ _ (prints_d _ _ h hg) (agrees_mono q (Finset.coe_subset.mpr (end_h hg le_rfl))) -- tune sidegoal order
include P Y
lemma step_S (g:baseP ≤ a)(z:Solace a b)(v:r<5)(w:a≤b)(t:0<m) (p:0≤ u)(κ:Treasure l m u): Nonempty (Leader T m (r+1) b):=by
 refine ⟨{F:=TryV P Y, m_F:=fun η=> try_p P Y η,v_F:=fun s η X=>try_F P Y s η X, keep:= fun c X i v=>try_keep P Y c X i v, foot:= fun w q u c d X V h k=> foot_S P Y c d X V w q u h k t, clear:= ?_, ℒ_F:=?_}⟩; swap
 · intro c X h; unfold TryV; split
   next l=> exact (try_good P Y z v t _ _ _ l.1.2.1 l.1.2.2).2.1 _ (show _∈facet (I h) from ⟨l.1.1,Finset.Subset.refl _⟩)
   next x=> exact ClearV.2 (fun i v=> ClearV.1 (P.clear c X h) i (by omega))
 intro S uS h c X; rcases h.eq_or_lt with e|e; swap; · refine Tends.T_v ?_ (Tends.widen w (P.ℒ_F S uS (by omega) c X)); intro i t; unfold TryV; rw [if_neg]; intro v; have he:= card_le_card (show I i⊆S from t.2); rw [v.1.2.2] at he; omega
 by_cases y:Grade l u X S; · exact Tends.T_v (Set.EqOn.symm (fun i p=> try_keep P Y c X i (y.mono (show I i⊆S from p.2)))) (Tends.widen (g.trans w) (atS T c X t p κ S y uS)) -- l binder notations
 exact Tends.T_v ((try_m P Y z v t c X S uS e y).symm) ((try_good P Y z v t c X S uS e).2.2)
-- Universal purchase independent of scale (and pre terminal) from FD extension ticket.
omit P Y
lemma bookF (r:ℕ)(t:r≤5):∃ a:ℝ,baseP ≤ a ∧ ∀ n l m u (T:Trophy n l u),0<m→0≤u→ Treasure l m u → Nonempty (Leader T m r a):=by
 induction r with
 | zero=> exact ⟨baseP,le_rfl,fun _ _ _ _ T p _ _=> entry0 T p⟩
 | succ r ih=>
    obtain ⟨a,h,v⟩:= ih (by omega); obtain ⟨b,g,s⟩:= merrit a (base_p.trans h); exact ⟨b,h.trans g,fun n l m u T p q κ=> let ⟨x⟩:=v _ _ _ _ T p q κ; step_S x (hires b).some h s t g p q κ⟩ -- passing t as r<5 (defeq)
end Turf
end YM.CF.DPress.FD
