import YM.SU5.Assay.Proscenium
import YM.SU5.Assay.Deskroom
import YM.SU5.Selected.Affinity
import YM.SU5.Selected.MeshSym
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section

/-- Mean slabs before character selection. The Euclidean height and calibration
 here are attached to this same unselected P. Default value never prices tests. -/
def HabBox (P:Spine)(j:Axis)(s w:ℕ)(F:P.Test):P.Slabs j:=
 if h:P.BEntry j w F then P.atSide j s w h.pos (h.card s) else 0

section
variable {P:Spine}{j:Axis}(s:ℕ){w v n:ℕ}{F G:P.Test}
local notation "X"=>P.HabBox j
lemma job_box (p:P.BEntry j w F): X s w F=P.atSide j s w p.pos (p.card s):=dif_pos p
lemma heard_box (p:P.BEntry j w F): (X s w F).1=P.meanBox j s w F:=by rw[job_box s p, meanBox_eq s p]; rfl
lemma HabBox_add (p:P.BEntry j w F)(t:P.BEntry j w G): X s w (F+G)=X s w F+X s w G:=Subtype.ext (by
 change (X _ _ _).1= (X _ _ F).1+(X _ _ G).1; rw [heard_box s (p.add t),heard_box s p,heard_box s t,meanBox_add s p t])
lemma HabBox_smul (p:P.BEntry j w F)(z:ℂ): X s w (z• F)=z•X s w F:=Subtype.ext (by
 change (X _ _ _).1=z• (X _ _ F).1; rw[heard_box s (p.smul z),heard_box s p,meanBox_smul s p])
lemma HabBox_sub (p:P.BEntry j w F)(t:P.BEntry j w G): X s w (F-G)=X s w F-X s w G:=Subtype.ext (by
 change (X _ _ _).1= (X _ _ F).1-(X _ _ G).1; rw [heard_box s (p.sub t),heard_box s p,heard_box s t,meanBox_sub s p t])
lemma HabBox_concat (p:P.BEntry j w F)(t:P.BEntry j v G): X s (w+v) (F*P.shifts j w G)=X s w F*X s v G:=Subtype.ext (by
 change (X _ _ _).1= (X _ _ F).1*(X _ _ G).1; rw [heard_box s (p.concat t),heard_box s p,heard_box s t,meanBox_concat s p t])
lemma HabBox_left (p:P.BEntry j w F)(n:ℕ): X s (n+w) (P.shifts j n F) = P.Eucl j (whenly (timeMesh P.par) s n) * X s w F:= Subtype.ext (by
 change (X _ _ _).1= P.euclOp j _ * (X _ _ F).1; rw [heard_box s (p.left n),heard_box s p, meanBox_left s p])
lemma HabBox_right (p:P.BEntry j w F)(n:ℕ): X s (w+n) F = X s w F * P.Eucl j (whenly (timeMesh P.par) s n):= Subtype.ext (by
 change (X _ _ _).1= (X s w F).1* P.euclOp j _; rw [heard_box s (w:=w+n) (p.right (by omega)),heard_box s p,meanBox_right s p])
lemma HabBox_raise (p:P.BEntry j w F)(t:ℕ)(h:s≤t): X t (P.par.R.L.val^(t-s)*w) (P.conveying s (t-s) F)= X s w F:=Subtype.ext (by
 rw [heard_box t (p.raise s t h),heard_box s p]; exact meanBox_raise s p t h)
lemma HabBox_across (p:P.BEntry j w F)(d:Trans j)(a:ℤ): P.movesOf j (s,a,d)*X s w F=X s w (P.shifts d a F)*P.movesOf j (s,a,d):=Subtype.ext (by
 change P.shiftOp j _ * (X _ _ F).1=(X s w (P.shifts d a F)).1 * P.shiftOp j _; rw [heard_box s (p.across d a),heard_box s p,meanBox_across s p])
lemma HabBox_star (p:P.BEntry j w F): star (X s w F)= X s w (P.riposte j w F):=Subtype.ext (by
 change star (X _ _ _).1=_; rw [heard_box s (p.riposte),heard_box s p,meanBox_star s p])
lemma HabBox_one (P:Spine)(j:Axis)(p:0<w):P.HabBox j s w 1=P.Eucl j (whenly (timeMesh P.par) s w):=Subtype.ext ((heard_box s (BEntry.one P j p)).trans (meanBox_unit s P j p))
lemma HabBox_mean (p:P.BEntry j w F): inner ℂ (P.floorVec j) ((X s w F).1 (P.floorVec j))=P.E s F.val:=by rw [heard_box s p, meanBox_earns s p]
lemma HabBox_solo (p:P.BEntry j w F)(x:P.Spectrum0 j): inner ℂ (P.emptyV j x) (P.stateSpace j x (X s w F) (P.emptyV j x))= P.singleState j s x F:=by
 rw [job_box s p]; exact (gns_state (P.portion j x) _).trans (P.room_single j x s w p.pos (p.card s))
end

/-- Full mean or full slab character calculating a common cost. In this interface
 `Time` has **placeholder** spatial law (ability on ticks is purchased from Slabs,
 and later separately made to permit real motions, not meant in the Time field). -/
structure Porch (P:Spine)(cost:ℕ→P.Test→ℂ) (j:Axis) where
  H : Hilbert
  ρ : P.Slabs j→⋆ₐ[ℂ] H.Op
  Ω : H
  normΩ : ‖Ω‖=1
  Time : OS.Semigroup H j
  heat (t:ℝ≥0): Time.E t=ρ (P.Eucl j t)
  still (t:ℝ≥0): ρ (P.Eucl j t) Ω=Ω
  transverse (g:Grid j): ρ (P.movesOf j g) Ω=Ω
  axSym (s:ℕ)(k:ℤ)(F:P.Test): cost s (P.shifts j k F)=cost s F
  expense {s w:ℕ}{F:P.Test}:P.BEntry j w F → inner ℂ Ω (ρ (P.HabBox j s w F) Ω)=cost s F

abbrev publicBill (P:Spine)(s:ℕ)(F:P.Test):ℂ:=P.E s F.val
abbrev soloBill (P:Spine)(x:P.Spectrum0 3)(s:ℕ)(F:P.Test):ℂ:=P.singleState 3 s x F
private def placeholderTime (P:Spine)(j:Axis): OS.Semigroup (P.Hil j) j where
 E t:=P.euclOp j t
 U _:=ContinuousLinearMap.id ℂ _
 eZero:=advance_source P.run P.large P.law P.history.circuit j 0 false (P.room j)
 time _ _:=advance_smag P.run P.large P.law P.history.circuit j 0 false (P.room j) _ _
 shrinks t:=P.heat_norm j t
 sym t:=advance_adjoint P.run P.large P.law P.history.circuit j 0 false (P.room j) _
 space _ _:=rfl
 uZero:=rfl
 unitary _ _:=rfl
 independent _ _:=by simp
 continuousE x:= (advance_strong P.run P.large P.law P.history.circuit j 0 false (P.room j) x).continuous
 continuousU _:=continuous_const
def publicH (P:Spine)(j:Axis): Porch P P.publicBill j where
 H:=P.Hil j
 ρ:= (P.slabAlgebra j).subtype
 Ω:=P.floorVec j
 normΩ:=P.unit_norm j
 Time:=placeholderTime P j
 heat _:=rfl
 still _:=advance_vacuum P.run P.large P.law P.history.circuit j 0 false (P.room j) _
 transverse g:=P.floor_moves j g
 axSym:=P.E_invariant j
 expense {s _ _} p:= HabBox_mean s p

def privateH (P:Spine)(x:P.Spectrum0 3)(j:Axis): Porch P (P.soloBill x) j where
 H:=P.PortionHil j (P.otherSpectrum 3 j x)
 ρ:=P.stateSpace j (P.otherSpectrum 3 j x)
 Ω:=P.emptyV j (P.otherSpectrum 3 j x)
 normΩ:=origin_norm _ (P.portion_unit j (P.otherSpectrum 3 j x))
 Time:=P.dynamics0 j (P.otherSpectrum 3 j x)
 heat _:=rfl
 still _:= P.at_full j (P.otherSpectrum 3 j x) _
 transverse g:=P.move_vac j (P.otherSpectrum 3 j x) g
 axSym s k F:=
   (P.single_agrees 3 j x s (P.shifts j k F)).symm.trans
   ((P.slide_single j (P.otherSpectrum 3 j x) s k F).trans (P.single_agrees 3 j x s F))
 expense {s w F} p:= (HabBox_solo s p (P.otherSpectrum 3 j x)).trans (P.single_agrees 3 j x s F)

end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
