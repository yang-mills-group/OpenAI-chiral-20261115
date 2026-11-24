import YM.SU5.Reconstruction.Hygrometry.Morph
import YM.SU5.Reconstruction.Oblique.Bows
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open PriceCliff
variable {α : Type*} {N m B:Side} {j:ℕ}
def Darkness (x:Op SpinIdx) := (1-Aop)*x=x*Aop
noncomputable def impel (U:Op SpinIdx)(h:Darkness U)(t:Personality): Personality where
 down:= !t.down
 voice:= acts U t.voice
 color:=t.color
 signed:= by
    have ht:=t.signed; unfold remains at ht; change remains _ _; unfold remains; cases k:t.down
    · rw [k,if_neg (by decide)] at ht
      suffices (1:Op SpinIdx)*U-U*Aop=Aop*U by rw [←act_mul,←this, act_sub,one_mul,act_mul U Aop,ht]; simp
      rw [←h,sub_mul]; abel
    rw [k,if_pos rfl] at ht
    have he: acts (1-Aop) (acts U t.voice)=0:= by rw [←act_mul,h,act_mul,ht,map_zero]
    rw [act_sub,act_one,sub_eq_zero] at he; exact he.symm

structure ActMark where
  cell:Cover→ Cover
  spinner:Op SpinIdx
  shades:Darkness spinner
  turnout(N:Side): UNI (Single N)
  charge(N:Side)(x:Cover)(i:SpinIdx)(s:Slot): acts (turnout N).val (basisC N x i s) = ∑ k, spinner k i • basisC N (cell x) k s
private lemma darkRide (P:UNI SpinIdx)(h:twist P Aop=1-Aop): Darkness P.val:=by unfold Darkness; rw [←h,twist_formula,mul_assoc _ (star _),P.property.1,mul_one]
def applaud (a:Axis):ActMark where
 cell:=(Buffered.plane a 0).flee
 spinner:=pin a
 shades:= darkRide (pinLift a) (angleX (mirrorX a) true)
 turnout:= carR a 0
 charge:= Lifted.acted_basisC a 0

def whisper (P:Ramp):ActMark where
 cell:= P.plan.flee
 spinner:=P.imageP
 shades:= darkRide P.reel (angleX P.jet true)
 turnout:= P.vehicle
 charge:= P.acted_basisC
namespace ActMark
variable (P:ActMark)
def role (x:Personality): Personality:= impel P.spinner P.shades x
def applause (b:Bool):ℂ:= if b then -Complex.I else Complex.I
lemma tenor (x:Cover)(s:Slot)(v: Ket SpinIdx): acts (P.turnout N).val (cantor N x s v) = cantor N (P.cell x) s (acts P.spinner v):=by
 unfold cantor; rw [map_sum]; simp_rw [map_smul,P.charge]; nth_rw 2 [←basis_expand v]; simp_rw [map_sum, map_smul, Finset.smul_sum, smul_smul, WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, basis_act, Finset.sum_smul, smul_eq_mul]; exact sum_comm -- tune
lemma lets (x:Cover)(r:ℝ)(t:Personality): Fock.theta (P.turnout N) (ton (player N x r t)) = applause t.down • ton (player N (P.cell x) r (P.role t)):=by
 have he: acts (P.turnout N).val (pitch N x r t.color t.voice)=pitch N (P.cell x) r t.color (acts P.spinner t.voice):=by unfold pitch; rw [map_smul,P.tenor]
 cases k:t.down <;> simp only [player, role, impel, k,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
 · change Fock.theta (P.turnout N) (create (pitch N x r t.color t.voice))= Complex.I • Fock.remove (-(pitch N (P.cell x) r t.color (acts P.spinner t.voice))) -- may simp not reducing role
   rw [theta_upV, show _=_ from he]; simp [Fock.remove] -- simplif
 change Fock.theta (P.turnout N) (Fock.remove (-(pitch N x r t.color t.voice)))= (-Complex.I) • create (pitch N (P.cell x) r t.color (acts P.spinner t.voice))
 rw [theta_downV,map_neg,he,map_neg,neg_smul,smul_neg]
variable (X:α→ Cover)(Z:α→Personality)
abbrev royalties(Z:α→Personality)(w:List α):ℂ := (w.map (fun i=> applause (Z i).down)).prod
lemma shifts(r:ℝ)(w:List α): Fock.theta (P.turnout N) (literal X Z N r w)= royalties Z w • (literal (P.cell ∘ X) (P.role ∘ Z) N r w) :=by
 induction w with
 | nil=> simp [literal,rollC,royalties,theta_one]
 | cons i w ih=> unfold literal rollC at *; unfold royalties; simp only [List.map_cons,List.prod_cons, theta_mul]; rw [ih, P.lets,Matrix.smul_mul,Matrix.mul_smul,mul_smul]; rfl
end ActMark
end YM.CF.Hygrometry
