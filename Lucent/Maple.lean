import Lucent.Wire
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

set_option maxHeartbeats 380000
set_option linter.unusedSimpArgs false
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

namespace Story

abbrev seat5(x y:ℤ) : Cover:= ![0,0,x,y]
/-- In array pitches (r in matter, R=2r in gauge). -/
def points: Fin 5 → Cover := ![
  seat5 (-2048) (-512), seat5 (-2048) (-512),
  seat5 0 0, seat5 200 50, seat5 2048 512]
def arm: Fin 5→ℕ:= ![0,1,0,0,0]
def song: Fin 5→DirSpin:= ![0,0,(0,1),(1,0),0]
def budget:=array points arm song

lemma arms : ∀ i, arm i≤1:=by decide
lemma tall : ∀ i j, |↑(points i j)|≤(2048:ℝ):=by
 intro i j; exact_mod_cast (show ∀ i j,|points i j|≤(2048:ℤ) from by decide) i j
lemma lengths (i j:Fin 5) (h:i≠j): Duo ((budget.hands i).p-(budget.hands j).p):=by
  let X:=fun i=>points i+disp (arm i)
  have hv: ∀i,(X i 0=0 ∧ X i 1=0):=by unfold X; decide
  have hi(i):((budget.hands i).p) 0=0 ∧ ((budget.hands i).p) 1=0:=by
    change ((X i 0:ℝ)=0) ∧ ((X i 1:ℝ)=0)
    exact_mod_cast hv i
  refine ⟨by rw [PiLp.sub_apply,(hi _).1,(hi _).1, sub_self],
    by rw [PiLp.sub_apply,(hi _).2,(hi _).2,sub_self],?_⟩ -- refine

  rw [PiLp.sub_apply]; apply sub_ne_zero.mpr
  change ((X i 2):ℝ) ≠ (X j 2:ℝ)
  exact_mod_cast (show ∀ i j,i≠j→X i 2 ≠ X j 2 from by unfold X; decide) i j h

lemma link: Money budget 0 1 2 3 4 where
 shades _:=rfl
 apart:=fun h=>lengths _ _ h
 tied:=by
   intro a z; simp only [List.mem_cons,List.not_mem_nil,or_false] at z
   rcases z with rfl|rfl|rfl <;> change gin (points _ + disp 0)=_
   all_goals simp only [disp,zero_smul,add_zero];rfl
 left:=rfl
 right:=rfl
 axial:=rfl
 guests:= by decide
