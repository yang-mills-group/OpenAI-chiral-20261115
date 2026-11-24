import Anomaly.Compass.Love
import Anomaly.Apert.Cotton
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip Pastry Hake Peaks Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Mew Salt Py Neon
open scoped Mew
open Vow Bake Rive QuadClock Stilo Roots Moto Hove Haro Tap Levier Thera
variable {N B:Side}{s:Sweep N}{U: UNI SpinIdx}{Z Y: ArcΦ}
variable {T A a b c h k:ℝ}{V V':BudgetPoint}{Q Q':ArcΦ}{t:ℝ}
lemma cometP (s:Sweep N)(z:ℝ): Spire.payZ s (↑z:ℂ)=↑z:=by unfold Spire.payZ; cases wageZ s<;>simp [cSignX]
-- small projects proof
def proceed (X:ArcΦ)(w u z:ℝ):ArcΦ:=((w:ℂ) • X.1,(u:ℂ) • X.2.1,(z:ℂ) • X.2.2)
private lemma arise_a (X Y:ArcΦ)(s:Signed)(U:UNI SpinIdx)(p:X.1=Y.1) : (arc_s s U X).1=(arc_s s U Y).1:= congrArg (localFace s⁻¹) p
private lemma arise_b (X Y:ArcΦ)(s:Signed)(U:UNI SpinIdx)(p:X.2.1=Y.2.1) : (arc_s s U X).2.1=(arc_s s U Y).2.1:= by unfold arc_s; simp_rw [zoomL]; split <;> dsimp only <;> rw [p]
private lemma arise_c (X Y:ArcΦ)(s:Signed)(U:UNI SpinIdx)(p:X.2.2=Y.2.2) : (arc_s s U X).2.2=(arc_s s U Y).2.2:= by unfold arc_s; simp_rw [zoomL]; split <;> dsimp only <;> rw [p]
lemma cruise_o (s:Sweep N)(p:s∈Whirl N)(U:UNI SpinIdx)(X:ArcΦ)(w u z:ℝ): proceed (arc_s s.s U X) w u z=arc_s s.s U (proceed X w u z):=by
 have ht(t:ℝ): (↑t:ℂ) • arc_s s.s U X= arc_s s.s U ((t:ℂ) • X):=by rw [colorD s p,cometP]
 apply Prod.ext
 · calc
    _ = ((↑w:ℂ) • arc_s s.s U X).1:=rfl
    _=(arc_s s.s U ((↑w:ℂ) • X)).1:=congrArg (fun x:ArcΦ=>x.1) (ht w)
    _=_:=arise_a ((↑w:ℂ) • X) (proceed X w u z) _ _ rfl
 apply Prod.ext
 · calc
    _=((↑u:ℂ) • arc_s s.s U X).2.1:=rfl
    _=(arc_s s.s U ((↑u:ℂ) • X)).2.1:=congrArg (fun x:ArcΦ=>x.2.1) (ht u)
    _=_:=arise_b ((↑u:ℂ) • X) (proceed X w u z) _ _ rfl
 calc
    _=((↑z:ℂ) • arc_s s.s U X).2.2:=rfl
    _=(arc_s s.s U ((↑z:ℂ) • X)).2.2:=congrArg (fun x:ArcΦ=>x.2.2) (ht z)
    _=_:=arise_c ((↑z:ℂ) • X) (proceed X w u z) _ _ rfl
abbrev docking (L: Side)(X:ArcΦ)(V V':BudgetPoint)(k:ℝ):ArcΦ:=(ζtap L V V' (↑k:ℂ) X,ζVtap L (↑k:ℂ) X,ξtap L (↑k:ℂ) X)
lemma keel (L:Side)(X:ArcΦ)(V V':BudgetPoint)(k:ℝ): docking L X V V' k=proceed ((↑k:ℂ) • X) (Tune.qCorset V.threshold V'.threshold L.val) ((Tap.lace 0 L)^2) ((Tap.lace 0 L)*(Tap.lace 1 L)):=by unfold proceed docking ζtap ζVtap ξtap; rw [Complex.ofReal_pow,Complex.ofReal_mul]; rfl
lemma keel_path (s:Sweep N)(p:s∈Whirl N)(U:UNI SpinIdx)(L:Side)(X:ArcΦ)(V V':BudgetPoint)(k:ℝ): arc_s s.s U (docking L X V V' k)= docking L (arc_s s.s U X) V V' k:=by rw [keel,←cruise_o s p, colorD s p,cometP,keel]
lemma rates_Ψ (s:Signed)(U:UNI SpinIdx)(X Y:ArcΦ): ‖(arc_s s U X).1-(arc_s s U Y).1‖=‖X.1-Y.1‖ ∧ ‖(arc_s s U X).2.1-(arc_s s U Y).2.1‖= ‖X.2.1-Y.2.1‖ ∧ ‖(arc_s s U X).2.2-(arc_s s U Y).2.2‖= ‖X.2.2-Y.2.2‖:=by
 have he:= aria U s (X-Y); have hw:arc_s s U (X-Y) = arc_s s U X-arc_s s U Y:= eq_sub_of_add_eq (by rw [←colorΞ,sub_add_cancel]); change ‖(arc_s s U (X-Y)).1‖=_ ∧ ‖(arc_s s U (X-Y)).2.1‖=_ ∧ ‖(arc_s s U (X-Y)).2.2‖=_ at he; rw [hw] at he; exact he
lemma stocks {L: Side}(s:Sweep N)(p:s∈Whirl N)(U:UNI SpinIdx)(H:αPrice L h A T a b c Q Q' V V' (k:ℂ)): αPrice L h A T a b c (arc_s s.s U Q) (arc_s s.s U Q') V V' k:=by
 let D:ArcΦ:= (ζtap L V V' (↑k:ℂ) Q,ζVtap L (↑k:ℂ) Q,ξtap L (↑k:ℂ) Q)
 let Φ:= arc_s s.s U Q
 let Bx:ArcΦ:= (ζtap L V V' (↑k:ℂ) Φ,ζVtap L (↑k:ℂ) Φ,ξtap L (↑k:ℂ) Φ)
 let Yt:=arc_s s.s U; have hh:Yt D=Bx:=keel_path s p ..
 have hh':=rates_Ψ s.s U Q' D; rw [show arc_s s.s U D=Bx from hh] at hh'
 constructor
 · rw [sameGauge]; change ‖(Yt Q').1-Bx.1‖ ≤ _; rw [show ‖(Yt Q').1-Bx.1‖= _ from hh'.1]; exact H.red
 · rw [sameGauge]; change ‖(Yt Q').2.1-Bx.2.1‖* _ ≤ _; rw [show ‖(Yt Q').2.1-Bx.2.1‖= _ from hh'.2.1]; exact H.violet
 rw [sameGauge]; change ‖(Yt Q').2.2-Bx.2.2‖*_≤_; rw [show ‖(Yt Q').2.2-Bx.2.2‖=_ from hh'.2.2]; exact H.verd
end YM.CF.Ione.Clock
