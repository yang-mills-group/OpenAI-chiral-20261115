import YM.CF.BPress.Sea.Pearls
import YM.CF.Pic.Stem
import YM.CF.Spire.Hats
/-! eq:B-hum. variation on compatibility with a reference with speed slack. Smooth charts per-field; take fundamental paths for both in the form of small rotations in SU(5) (this is one way of making the unit-sphere interpolation). Works on any such locality-compatible read, no actor extension across singular seams.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Nougat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Pec Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial Scroll Thera
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {B m L N :Side}{q d a b K κ:ℝ}
open Jet Spire Phase.Sample Brace Phase Kea Pic Sods
structure Shell (s:Support (More N))(Y: Stun N)(u: Bkg (More N))(X: Stun N)(a:ℝ): Prop where
 tag(q:Link (More N))(h:q.1∈s)(v:q.1+step q.2∈s): Cube.cmp firstF (u q) 1 ≤ a
 rods : ∀ i∈s, ∃ g:E,X i=scaledV g (Y i)∧ Cube.cmp firstF g 1 ≤ a
variable (Y:Stun N){T: Bkg (More N)}{g: Mach (More N)}
theorem slow_feast (p:lawnK T 1 a)(t:∀ i,Cube.cmp firstF (g i) 1 ≤ b)(h:Slow 1 (hook Y) q) : Slow T (hook (feast g Y)) (a+(b+(q+b))):=by
 let X(o):= hook (feast g Y) o; let Z(o):= hook Y o; have hs(o): ‖X o-Z o‖≤ b:=by
    have he:= turn_price (g o) 1 (Z o); simp only [Z, Lat.turn, fund_one,act_one,hookN,mul_one] at he; exact he.trans (t o)
 intro x i; let y:=x+step i; have ht:‖Z y-Z x‖<q:= by simpa only [Pi.one_apply,Lat.turn,fund_one,act_one] using h x i
 refine lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub _ (X y) _) (add_lt_add_of_le_of_lt ?_ ?_ )
 · have he:=turn_price (T (x,i)) 1 (hook (feast g Y) y); rw [hookN, mul_one] at he; simp only [Lat.turn,fund_one,act_one] at he; exact he.trans (p _)
 have he:= norm_sub_le_norm_sub_add_norm_sub (X y) (Z y) (X x); exact lt_of_le_of_lt he (add_lt_add_of_le_of_lt (hs y) (lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub _ (Z x) _) (add_lt_add_of_lt_of_le ht ((norm_sub_rev ..).le.trans (hs x)))))
variable {E:Type}[Fintype E][DecidableEq E]
def actsAt (x:Ket E): Op E→L[ℝ] Ket E:= let Z: Op E→ₗ[ℂ] Ket E:= ⟨⟨fun A=>acts A x, fun a b=>act_add a b x⟩, fun a b=> act_smul ..⟩; Z.toContinuousLinearMap.restrictScalars ℝ
lemma Act_attend(x:Ket E)(h:‖x‖=1): ‖actsAt x‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=> (Eye.norm_act i x).trans_eq (by rw [h, mul_one,one_mul])) -- tune
lemma seek_pose (T:ℝ→ Mach (More N))(A:Stun N)(t:ℝ)(h:∀ i, Allows 1 (fun x:ℝ=>SU.fund (T x i)) t K): Jet.seek (fun t=> feast (T t) A) 1 t K:=by
 intro i; let x:=hook A i; have hX:= (h i).linear (actsAt x) (Act_attend x (hookN ..)); rw [one_mul] at hX; exact hX
end YM.CF.BPress.Nougat
