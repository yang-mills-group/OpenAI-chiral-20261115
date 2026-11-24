import Crape.Heights
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
variable (P:Spine)
local notation "Lx"=>P.par.R.L
local notation "T"=>timeMesh P.par
local notation "rC"=>ruler P.par.block
-- coarse polynomial overhead. all powers.C D eventually.small. no RP consequence needed here.
lemma polyRise :∃ D:ℝ,0< D ∧∀ s:ℕ, (reachQ P s:ℝ) ≤ D*(1+(s:ℝ))^6:=by
 have hx : Real.exp 1 ≤ P.par.x:= P.large; have h1:1≤P.par.x:=by linarith only [Real.add_one_le_exp (1:ℝ),hx]
 let X:=P.par.x; let b:=Vale.billX P.par.R.L; have he:= Vale.pitch Lx; change 0 ≤ b at he
 let G:=X+b; have hx':1≤G:=by unfold G X; linarith
 let d:=G^2+1; have hd:1 ≤ d:=by unfold d; linarith [sq_nonneg G]
 let U(s:ℕ):ℝ:=1+s
 let B(s:ℕ):ℝ:=(P.run.meter.a s).B
 have hh(s:ℕ):1 ≤ U s:=le_add_of_nonneg_right (Nat.cast_nonneg _)
 have e(s:ℕ): B s ≤d*U s^2:=by
    unfold B; rw [P.run.meter.boot s|>.2.1]; unfold Pressure.radiusB
    let y:= Vale.hat Lx X s
    change (↑(Nat.ceil ((Real.log y)^2)):ℝ) ≤_
    apply (Nat.ceil_lt_add_one (sq_nonneg _)).le.trans; have hy:X ≤ y:=Vale.crown ..; have hv:y ≤ G*U s:=by
      unfold y G U Vale.hat; nlinarith [Nat.cast_nonneg (α:=ℝ) s]
    have cnt:Real.log y ≤ G*U s:= by linarith only [hv,Real.log_le_sub_one_of_pos (show 0<y by unfold X at hy; linarith)]
    apply le_trans (add_le_add_left (pow_le_pow_left₀ (Real.log_nonneg (h1.trans hy)) cnt _) 1); unfold d; have q:1 ≤ U s ^2:=one_le_pow₀ (hh _); nlinarith only [q] -- ring
 let D':= (P.calibration.ℓ:ℝ)+22+4*d^3+16*(P.calibration.B.val:ℝ)
 refine ⟨D',(by unfold D'; positivity),fun s=>?_⟩
 let Y:=d*U s^2; have hp:1 ≤ Y:= one_le_mul_of_one_le_of_one_le hd (one_le_pow₀ (hh _)); have hr:= (e s|>.trans (show Y ≤ Y^3 from (pow_le_pow_right₀ hp (by norm_num:(1:ℕ)≤3)).trans' (le_of_eq (pow_one Y).symm))); have hn : B s^3 ≤ Y^3:= pow_le_pow_left₀ (by unfold B; positivity) (e s) _
 have hG:1 ≤ U s^6:=one_le_pow₀ (hh _)
 let X':=(P.calibration.ℓ:ℝ)+22+16*(P.calibration.B.val:ℝ); have hu:=mul_le_mul_of_nonneg_left hG (by unfold X'; positivity:0≤X')
 unfold reachQ minB Calico.amount; push_cast; change (P.calibration.ℓ:ℝ)+(22+2*(B s^3+B s))+_≤ D'*(U s)^6
 unfold X' Y at * -- possible u references Y.D. hu huge. nlinarith only
 unfold D'; nlinarith only [hr,hn,hu]
#check Real.log_le_sub_one_of_pos
lemma recessVanish (F:ℕ): Tendsto (tidal P F) atTop (𝓝 0):=by
 obtain ⟨D,h,t⟩:= polyRise P
 let θ:=((P.par.R.L.val:ℝ))⁻¹; have p₂:= P.par.R.coarse
 have b₀:1<(P.par.R.L.val:ℝ):=by exact_mod_cast p₂.trans_lt' (by norm_num:1<3)
 have e:0<θ∧θ<1:=⟨inv_pos.mpr (zero_lt_one.trans b₀), (inv_lt_one₀ (zero_lt_one.trans b₀)).2 b₀⟩
 have he:‖θ‖<1:=lt_of_le_of_lt (le_of_eq (Real.norm_of_nonneg e.1.le)) e.2
 have ee: Tendsto (fun s:ℕ=> (1+(s:ℝ))^6*θ^s) atTop (𝓝 (0:ℝ)):=by
    let f(n:ℕ):= (n:ℝ)^6*θ^n
    have H0:Summable f:= summable_pow_mul_geometric_of_norm_lt_one _ he
    apply Summable.tendsto_atTop_zero
    apply Summable.congr ( ((summable_nat_add_iff 1).2 H0).mul_right θ⁻¹)
    intro n; unfold f; rw [Nat.cast_add,Nat.cast_one,pow_succ θ, mul_assoc _ _ θ⁻¹,mul_inv_cancel_right₀ e.1.ne',add_comm]
 let b:=16*(P.par.block.val:ℝ); have hb:0<b:=by unfold b; exact mul_pos (by norm_num) (by exact_mod_cast P.par.block.property)
 let u:ℝ:=(T).base
 refine squeeze_zero (fun i=>(tide_price P F i).le) (g:=fun s:ℕ=> (D/b*u)*((1+(s:ℝ))^6*θ^s)) ?_ ?_
 · intro s; unfold tidal measured
   have hx:((nodeC (cellar P F s) 3:ℤ):ℝ)≤ reachQ P s:=by exact_mod_cast (recess P F s).2
   rw [show ((rC:ℤ):ℝ)=b from (by unfold b ruler; push_cast; rfl)]
   apply (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hx.trans (t _)) hb.le) (mill_pos ..|>.le)).trans (le_of_eq ?_)
   unfold mill; change _/ _ * ((( (T).base / ((T).L:ℝ≥0)^s:ℝ≥0):ℝ))=_; rw [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast ] -- ←inv_pow direction need div_eq_mul_inv
   unfold u θ; change _/ _ * (_ / ((P.par.R.L.val:ℝ)^s))= _; rw [inv_pow]
   ring
 simpa only [mul_zero] using ee.const_mul (D/b*u)
#check squeeze_zero
#print axioms recessVanish
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
