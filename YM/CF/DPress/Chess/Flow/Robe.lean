import YM.CF.DPress.Chess.Flow.Turn
import YM.CF.DPress.FD.Issue
/-!
 Conditional on all true fields, using FD.Firm on the *one* actual repair rather than a fresh one per factor. These and all later `LocalOn` assertions use links with both vertices in their S. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Transit
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree
open Cube (More assembly)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal
namespace Robe
variable {n:Side}{P:Loom n} {u d:ℝ}{r:ℕ}
abbrev τ (P:Loom n)(x:Pane n):= (depot n).map fun y=> P (x,y)
lemma lever (p:Measurable P)(x:Pane n): MeasurePreserving (fun y=> P (x,y)) (depot n) (τ P x):=⟨p.comp measurable_prodMk_left,rfl⟩
lemma prob(p:Measurable P)(x:Pane n):IsProbabilityMeasure (τ P x):= Measure.isProbabilityMeasure_map (p.comp measurable_prodMk_left).aemeasurable -- name
lemma move (W:Wall) (X:Roof n u d r P)(x:Pane n): MeasurePreserving (W.shine n) (τ P x) (τ P (W.shine n x)):=by
 let s:= W.joy n; let H: MeasurePreserving (fun y=> P (W.shine n x,bun s y)) (depot n) (τ P (W.shine n x)):= (lever X.bill _).comp (tuft _); refine ⟨(revM _).measurable,?_⟩; rw [τ,Measure.map_map (W.trail _).measurable (lever X.bill _).measurable]; exact (Measure.map_congr (sepT.mono (fun i g=> (X.move x i s g).symm))).trans H.map_eq -- tune binder order & comp infer
section
variable {I:Type}[Fintype I][MeasurableSpace I][MeasurableSingletonClass I](U:Scout I n u d r)
local notation "Ψ"=> Star.Coral n
open Cube (More)
open Star
abbrev View(n:Side):= Seat n→SU.E
variable (S:Support (More n)) (x:Pane n)
private lemma hasWin (e:Skye.reach n) (t:e.1∈ S)(p:e.1+step e.2∈S)(r:ℕ) : Skye.win r e⊆ halo r S:=by intro i g; obtain ⟨j,h,v⟩:=halo_spec.mp g; simp only [Skye.ends, Finset.mem_insert,Finset.mem_singleton] at h; exact halo_spec.mpr ⟨j,h.elim (fun x=>x.symm ▸ t) (fun x=> x.symm ▸ p),v⟩
lemma worth {x y:Pane n}{g h: View n}{i j:I}
    (v:(U.V.set (halo r S)).r i j)(t: Agrees (halo r S) x y)(l:Set.EqOn g h (halo r S)): Agrees S (fairly U x g i) (fairly U y h j):=by
 have he: Set.EqOn g h S:= fun i t=> l (halo_subset r S t); let f:= gauge g x; intro e h₁ h₂; have hu:= (U.V.grow (hasWin S e h₁ h₂ r) (U.V_ear e f)) i j v; have hx:U.X i (gauge g x) e=U.X j (gauge h y) e:= hu.trans ((U.basicF j).shore _ _ e (agrees_mono (Skye.tied (halo r S) x y g h t l) (Finset.coe_subset.mpr (hasWin S e h₁ h₂ r)))); unfold fairly
 change (g e.1)⁻¹ * U.X i f e * _ = (h e.1)⁻¹ * (U.X j _ e) * _; rw [show U.X i f e= _ from hx]; simp only [Pi.inv_apply,he h₁,he h₂]
-- order rep next
end
end Robe
end YM.CF.DPress.Chess.Transit
