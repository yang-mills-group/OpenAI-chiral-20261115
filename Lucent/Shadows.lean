import YM.SU5.WakeInvestment.Shuttle
import Lucent.Nocturne
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Pannier.Chancel Rous Pressure
open Peaks Scree
open RG Buffered.Afterglow
open Lamour Lamour.Bridge
open Morn Journey
variable {P:Preparation}{I J:Type}
open Onyx
open Stationary (Gaia)
open Vale Morn
set_option quotPrecheck false
variable {W:ℕ→I→Staff} {R:ℕ→ℝ} {r b l:ℕ→ℕ}(T:Velocity P R r){B:ℝ}
variable [Fintype I]
-- placement pair
abbrev leg (P:Preparation)(x:Gaia)(n:ℕ):= Shuttle.gait P x n
abbrev shade (P:Preparation) (x:Gaia) (n:ℕ):=Shuttle.opposite (leg P x n)
variable (n:ℕ)
abbrev frontS (P:Preparation)(r:ℕ→ℕ)(W:ℕ→ I→Staff) (n:ℕ):=fun s=>forwardS (W s) (liftum P r n s)
abbrev rearS (P:Preparation)(r:ℕ→ℕ)(W:ℕ→ I→Staff) (n:ℕ):=fun s=>otherS (W s) (liftum P r n s)
abbrev nightS (P:Preparation)(r:ℕ→ℕ)(W:ℕ→ I→Staff) (n:ℕ):=fun s=>replayS (W s) (liftum P r n s)

include T
lemma during (h:DanceCost B R W b l):
   let E:=B+2*trackB P n
   DanceCost E R (frontS P r W n) b l ∧ DanceCost E R (rearS P r W n) b l ∧ DanceCost E R (nightS P r W n) b l:= by
 intro E; suffices e: ∀ᶠ s in atTop,Squad (E*R s) (frontS P r W n s) (b s) (l s) ∧ Squad (E*R s) (rearS P r W n s) (b s) (l s) ∧ Squad (E*R s) (nightS P r W n s) (b s) (l s) from ⟨e.mono fun _ h=>h.1,e.mono fun _ h=>h.2.1,e.mono fun _ h=>h.2.2⟩
 filter_upwards [h,T.tracks n] with s g t
 have hp:B*R s +2*|↑(liftum P r n s)| ≤ E*R s:=by unfold E; linarith only [t]
 exact ⟨(dawnCost _ g).mono hp,(duskCost _ g).mono hp,(nightCost _ g).mono hp⟩

omit T
abbrev climb (Z:ℕ→ℝ)(f:ℕ→ Cover)(x: Gaia):= Tendsto (fun s=> riseX (Z s) (f s)) atTop (𝓝 x)
private abbrev matter (r:ℕ→ℕ):ℕ→ℝ:= fun i=>r i
lemma skyT (P:Preparation)(r:ℕ→ℕ)(s:ℕ) : (liftum P r n s:ℝ)= trackB P n*(r s:ℝ):=by unfold liftum disturb Heat.gaugeShift trackB; push_cast; ring
#print Twah.crumbs
#check Shuttle.xP

omit T
variable {f g:ℕ→ Cover}{x:Gaia}
lemma shift_tgt {Z:ℕ→ℝ}(h:climb Z f x) (t:∀ i,Tendsto (fun s=>((g s i:ℝ)-(f s i:ℝ))/Z s) atTop (𝓝 (if i=3 then trackB P n else 0))): climb Z g (leg P x n):=by
 apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr ?_)
 intro i; change Tendsto (fun s=>(g s i:ℝ)/Z s) atTop (𝓝 ((leg P x n) i))
 unfold leg; rw [Shuttle.xP]; refine ((show Tendsto (fun s=>(f s i:ℝ)/Z s) atTop (𝓝 (x i)) from (PiLp.continuous_apply 2 _ i).continuousAt.tendsto.comp h).add (t i)).congr fun s=>?_
 rw [sub_div]; ring
include T
lemma on_foot (h:climb (matter r) f x):
    climb (matter r) (fun s=> ((plane 3 (liftum P r n s)).flee ((plane 3 0).flee (f s)))) (leg P x n):=by
 apply shift_tgt (f:=f) n h; intro i; apply tendsto_const_nhds.congr; intro s
 rw [flee_pos]
 by_cases y:i=(3:Axis)
 · subst i; rw [if_pos rfl, if_pos rfl, flee_pos, if_pos rfl]
   simp only [add_zero]; push_cast; rw [skyT]; unfold matter; have he:=T.t s; field_simp; ring
 rw [if_neg (Ne.symm y),if_neg y,flee_pos,if_neg (Ne.symm y),sub_self,zero_div]

lemma on_hand (h:climb R f x):
    climb R (fun s=> ((plane 3 (liftum P r n s)).motion ((plane 3 0).motion (f s)))) (leg P x n):=by
 apply shift_tgt (f:=f) n h; intro i
 simp_rw [fling_move]
 by_cases y:i=(3:Axis)
 · subst i; rw [if_pos rfl]
   have ht:=(tendsto_const_nhds (x:=2 * trackB P n)).div T.coupled (by norm_num)
   rw [mul_div_cancel_left₀ _ (two_ne_zero)] at ht
   apply ht.congr; intro s; rw [if_pos rfl, if_pos rfl]
   rw [Pi.div_apply]; push_cast; rw [skyT]; have hp:= T.t s; rw [div_div_eq_mul_div]; ring
 rw [if_neg y]; apply tendsto_const_nhds.congr; intro s; rw [if_neg (Ne.symm y), if_neg (Ne.symm y),sub_self,zero_div]

omit T in
lemma back_hand (h:climb R f x):
    climb R (fun s=> (plane 3 0).motion (f s)) (Shuttle.opposite x):=by
 apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr ?_)
 intro i; have g:Tendsto (fun s=>(f s i:ℝ)/R s) atTop (𝓝 (x i)):= (PiLp.continuous_apply 2 _ i).continuousAt.tendsto.comp h
 change Tendsto (fun s=>((plane 3 0).motion (f s) i:ℝ)/_) atTop (𝓝 (if i=3 then -x i else x i))
 simp_rw [fling_move]
 by_cases y:i=(3:Axis)
 · subst i; simpa [neg_div] using g.neg
 simp [Ne.symm y,y]; exact g
lemma back_foot (h:climb (matter r) f x):
    climb (matter r) (fun s=> (plane 3 0).flee (f s)) (Shuttle.opposite x):=by
 apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr ?_)
 intro i; have g:Tendsto (fun s=>(f s i:ℝ)/(matter r s)) atTop (𝓝 (x i)):= (PiLp.continuous_apply 2 _ i).continuousAt.tendsto.comp h
 change Tendsto (fun s=>((plane 3 0).flee (f s) i:ℝ)/(matter r s)) atTop (𝓝 (if i=3 then -x i else x i))
 by_cases y:i=(3:Axis)
 · subst i; rw [if_pos rfl]; have k:= g.neg.sub (tendsto_inv_atTop_zero.comp T.matter); rw [sub_zero] at k; apply k.congr; intro s; rw [flee_pos,if_pos rfl]; push_cast; unfold matter; simp only [Function.comp_apply]; ring
 simpa [y,Ne.symm y,flee_pos] using (g: Tendsto _ _ _)
