import YM.SU5.SatinWard.Resolution.Discus
import YM.SU5.SatinWard.Resolution.Arcade
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open Maxwell.Free
namespace PSE
open LitCurrent Surplus Next.Rank.Spindle
-- booleans plus oriented proper. ρ± outputs have B assigned ±charge∘levy. αPole.
abbrev windAx (i j:Axis) :=Pec.X (Equiv.swap i j)
abbrev chipP (s:Signed):= Signed.mirror 3 * s
noncomputable def sailUp (i:Fin 3) := (![ (1:Signed), chipP (windAx 1 3), chipP (windAx 1 2) ]:Fin 3→Signed) i
noncomputable def sailDown (i:Fin 3) := (![Signed.mirror 3, windAx 1 3, windAx 1 2]:Fin 3→Signed) i
@[simp] lemma presenceUp (i): detX (sailUp i)=false:=by fin_cases i <;> simp [sailUp,det_i,chipP,windAx, det_p, Pec.detSwap _ _ (show (1:Axis)≠3 from by decide),Pec.detSwap _ _ (show (1:Axis)≠2 from by decide),det_t]
@[simp] lemma presenceDown (i): detX (sailDown i)=true:=by fin_cases i <;> simp [sailDown,windAx,Pec.detSwap _ _ (show (1:Axis)≠3 from by decide), Pec.detSwap _ _ (show (1:Axis)≠2 from by decide),det_t]
abbrev flyP (i:Fin 3)(F:PlaqAxes):ℝ:=orientAx (sailUp i) F
abbrev flyM (i:Fin 3)(F:PlaqAxes):ℝ:=orientAx (sailDown i) F
abbrev palG(F G:PlaqAxes):ℝ:=(1/2)* ∑ i:Fin 3, (flyP i F*flyP i G-flyM i F*flyM i G)
set_option maxHeartbeats 1000000 in
lemma sail_scan (i:Fin 3)(F:PlaqAxes): flyP i F=(if F=foilA i then 1 else if F=foilB i then levy i else 0) ∧ flyM i F=(if F=foilA i then 1 else if F=foilB i then -levy i else 0):=by
 rcases rimCases F with v|v|v|v|v|v <;> subst F <;> fin_cases i <;> norm_num (config := {decide:=true}) [flyP,flyM,orientAx,polarShift,_root_.Zephyr.Chern.flux,sailUp,sailDown,foilA,foilB, levy,chipP,windAx,Pec.X,Signed.mul_flip, Signed.mul_perm_apply,rimA,rimB,rimC,rimD,lowLow,highHigh]
set_option maxHeartbeats 1300000 in
lemma swanscan (F G:PlaqAxes)(X:Axis→ℝ)(v:ℝ):
    let M:=kernel X v; ∑ i:Fin 3, levy i*(shell M F (foilA i)*shell M G (foilB i)+shell M F (foilB i)*shell M G (foilA i)) = (1-v*∑ i:Axis, X i^2)*palG F G:=by
 intro M; dsimp only [M,palG] -- syntax
 simp_rw [(sail_scan _ _).1,(sail_scan _ _).2]
 rcases rimCases F with v|v|v|v|v|v <;> subst F <;> rcases rimCases G with v|v|v|v|v|v <;> subst G <;> simp (config := {decide:=true}) [shell,Maxwell.Free.wedge,kernel,foilA,foilB,levy,Fin.sum_univ_four,Fin.sum_univ_three,kr_eq,rimA,rimB,rimC,rimD,lowLow,highHigh,YM.Axis] <;> ring
abbrev webC (F G:PlaqAxes)(d:Gaia):ℂ:= ∑ i:Fin 3, coeff2 1 1 i * (specter F (foilA i) d*specter G (foilB i) d+specter F (foilB i) d*specter G (foilA i) d)
lemma webValue (x:Gaia)(F G:PlaqAxes)(p:x≠0): Complex.I * webC F G x=(↑(palG F G):ℂ)*(↑(4*Maxwell.normal*(‖x‖^2)⁻¹^2:ℝ):ℂ)^2:=by
 let v:=2*(‖x‖^2)⁻¹; let M:=kernel (WithLp.ofLp x) v; have u:(Maxwell.Free.house x).val=M:=rfl
 have hv: ∑ k:Axis, ((WithLp.ofLp x) k)^2 = ‖x‖^2:=by simp_rw [pow_two ((WithLp.ofLp x) _)]; exact (Maxwell.Free.inner4 x x |>.symm).trans (real_inner_self_eq_norm_sq x)
 let C:=4*Maxwell.normal*(‖x‖^2)⁻¹^2; let V:=(C:ℂ)^2
 let g (i:Fin 3):= levy i*(shell M F (foilA i)*shell M G (foilB i)+shell M F (foilB i)*shell M G (foilA i))
 have z:∑ i:Fin 3,g i= -palG F G :=by
    unfold g M; rw [swanscan,hv]; have h:0< ‖x‖:= norm_pos_iff.mpr p; have e:1-v*‖x‖^2= -1:=by unfold v; field_simp; ring
    rw [e]; ring
 have he(i): Complex.I*coeff2 1 1 i=-(levy i:ℂ):=by fin_cases i <;> simp [coeff2,levy]
 have hx(F G:PlaqAxes): specter F G x=(C:ℂ)* (shell M F G:ℝ):=by unfold specter; rw [bare_formula _ _ _ _ p,u,Complex.ofReal_mul]
 unfold webC; rw [mul_sum]; simp_rw [←mul_assoc Complex.I,he,hx]
 refine Eq.trans (b:=∑ i:Fin 3,-(g i:ℂ)*V) (sum_congr rfl ?_) ?_; · intro i _; unfold g V; push_cast; ring
 rw [←sum_mul,sum_neg_distrib,←Complex.ofReal_sum,z]; simp only [Complex.ofReal_neg,neg_neg]; rfl
#print axioms webValue
end PSE
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
