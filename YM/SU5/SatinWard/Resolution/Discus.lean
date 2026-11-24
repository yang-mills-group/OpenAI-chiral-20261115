import YM.SU5.SatinWard.Resolution.Synod
import YM.Next.MAXWELL.House
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
abbrev optic : Gaia→ℂ:= tangency 1 1 1 1
abbrev posix (x:Gaia):ℝ:=3 * Fintype.card Sage * (4*Maxwell.normal*(‖x‖^2)⁻¹^2)^2
abbrev levy (i:Fin 3):ℝ:= (![1,1,-1]:Fin 3→ℝ) i
abbrev kernel (X: Axis→ℝ)(v:ℝ): Matrix Axis Axis ℝ := Matrix.of fun i j=> kr i j-v*X i*X j
abbrev shell (M:Matrix Axis Axis ℝ)(A B:PlaqAxes):= Maxwell.Free.wedge M A.val.1 A.val.2 B.val.1 B.val.2
local notation "V" => foilA
local notation "Wq"=> foilB
abbrev slash(M:Matrix Axis Axis ℝ)(i j:Fin 3):ℝ:= shell M (V i) (V j)* shell M (Wq i) (Wq j)+shell M (V i) (Wq j)* shell M (Wq i) (V j)
lemma axialN (v:ℝ)(X:Axis→ℝ)(i:Fin 3):∑ j:Fin 3, levy i*levy j* slash (kernel X v) i j= 1-v*∑ i:Axis, (X i)^2:=by fin_cases i <;> simp (config := {decide:=true}) [slash,shell,Maxwell.Free.wedge, kernel,foilA,foilB,levy,Fin.sum_univ_four, Fin.sum_univ_three,kr_eq, lowLow,highHigh,rimA,rimB,rimC,rimD,YM.Axis] <;> ring
lemma suitOf (x: Gaia)(p:x ≠ 0)(i: Fin 3):
    ∑ j:Fin 3, coeff2 1 1 i * (coeff2 1 1 j * mintBody (V i) (Wq i) (V j) (Wq j) x) = (↑(Fintype.card Sage):ℂ)* ((↑(4*Maxwell.normal*(‖x‖^2)⁻¹^2:ℝ):ℂ)^2):=by
 let v:=2*(‖x‖^2)⁻¹; let M:=kernel (WithLp.ofLp x) v; have u:(Maxwell.Free.house x).val=M:=rfl
 have hv: ∑ k:Axis, ((WithLp.ofLp x) k)^2 = ‖x‖^2:=by simp_rw [pow_two ((WithLp.ofLp x) _)]; exact (Maxwell.Free.inner4 x x |>.symm).trans (real_inner_self_eq_norm_sq x)
 let C:=4*Maxwell.normal*(‖x‖^2)⁻¹^2; let G:ℂ:= (↑(Fintype.card Sage):ℂ) * (C:ℂ)^2
 have z:∑ j:Fin 3, (↑(levy i*levy j* slash M i j):ℂ)=(-1:ℂ):=by
    unfold M; rw [← Complex.ofReal_sum,axialN,hv]; have h:0< ‖x‖:= norm_pos_iff.mpr p; have e:1-v*‖x‖^2= -1:=by unfold v; field_simp; ring
    rw [e]; norm_num
 have he(i): coeff2 1 1 i=(levy i:ℂ)*Complex.I:=by fin_cases i <;> simp [coeff2,levy]
 have hx(F G:PlaqAxes): specter F G x=(C:ℂ)* (shell M F G:ℝ):=by unfold specter; rw [bare_formula _ _ _ _ p,u,Complex.ofReal_mul]
 let b(j:Fin 3):= (↑(levy i*levy j*slash M i j):ℂ)
 calc _ = ∑ j:Fin 3,-G*b j:=by
                apply sum_congr rfl; intro j _; simp only [he,mintBody,hx,b, slash]; push_cast; unfold G
                let α:= - ( (C:ℂ)^2*(↑(Fintype.card Sage):ℂ)* ((levy i:ℂ)*(levy j:ℂ))* (slash M i j:ℝ))
                -- factor as - I I; compare separately
                calc _ = - (Complex.I*Complex.I)*α:=by unfold α slash; push_cast; ring
                     _ = _:=by rw [Complex.I_mul_I]; unfold α slash; push_cast; ring
      _ = _:=by rw [←mul_sum, show ∑ j,b j=(-1:ℂ) from z,neg_mul_neg,mul_one]
lemma optic_formula (x:Gaia)(p:x≠0): optic x=(posix x:ℂ):=by
 unfold optic tangency; simp_rw [mul_sum,suitOf x p]; unfold posix; rw [sum_const]; simp; push_cast; ring
lemma optic_pos (x:Gaia)(p:x≠0): 0<posix x:=by
 unfold posix; have hm :=Maxwell.normal_pos; have hv:0<‖x‖:=norm_pos_iff.mpr p; haveI:Nontrivial SU.group.Color:= Thera.yet_one.nontrivial_color; have ht:0<SU.group.lieDim:=by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
 change 0 < 3*(Fintype.card (Fin SU.group.lieDim):ℝ)*_; rw [Fintype.card_fin]; positivity
lemma stamp (x:Gaia)(a:0<‖x‖):0<(optic x).re:=by rw [optic_formula x (norm_pos_iff.mp a)]; exact optic_pos x (norm_pos_iff.mp a)
#print axioms optic_formula
end PSE
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
