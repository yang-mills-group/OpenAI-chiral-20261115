import Aloft.Dorset
import Ridgetop.PriceU
import Preen.Licensed
import Ridgetop.Dial
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Ridgetop
local notation "SP" s:max=> P.spotMesh s
local notation "ρ" d:max=> ((girder P d):ℝ)
local notation "χ" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
local notation "R" d:max=> girder P d
variable (c:ℕ)(d:ℕ)(w:Cover)
abbrev blazeF(i:Bool): Cover:= if i then shuffleT P (bootH P c d) w else shuffleT P 0 (swapW w)
local notation "γ"=> (pollN P)
abbrev led(d:ℕ)(w:Cover):ℝ:= (γ:ℝ)*4*c*(ρ d)+ 2*(nodeC w (3:Axis):ℝ)
lemma suitability : (∀ i:Axis, (( (nodeC (blazeF P c d w false)-nodeC (blazeF P c d w true)) i:ℤ):ℝ) = if i=(3:Axis) then -led P c d w else -(γ:ℝ)*(4*(idleCar P:ℝ))):=by
 intro i; unfold blazeF; simp only [Bool.false_eq_true, ite_false,ite_true, Pi.sub_apply,Int.cast_sub,cruise_price,fling_price,Pi.zero_apply,mul_zero,add_zero]; by_cases p:i=(3:Axis)
 · subst i; simp only [bootH,spindle,if_pos rfl]; unfold led girder; push_cast; ring
 simp only [bootH,spindle,if_neg p,if_neg (Ne.symm p)]; push_cast; ring
lemma mandate (V:Enrolled P d (stairW d) w) (e:1 ≤ c): (γ:ℝ)*4*c*(ρ d) ≤ led P c d w ∧ led P c d w ≤((γ:ℝ)*4*c+2)*(ρ d):=by
 have he:0 ≤ nodeC w (3:Axis):=by linarith only [V.clock.1, Int.natCast_nonneg P.calibration.ℓ]
 have hu: nodeC w (3:Axis) ≤ R d:=(chip P w V 3).2.2
 unfold led; constructor <;> linarith only [show 0 ≤ ((nodeC w 3:ℤ):ℝ) by exact_mod_cast he, show (((nodeC w 3):ℤ):ℝ) ≤ (ρ d) by exact_mod_cast hu]
lemma ledG (V:Enrolled P d (stairW d) w) (e:1 ≤ c): ρ d ≤ led P c d w:= by
 have he:= (mandate P c d w V e).1; apply le_trans ?_ he
 have h0:1 ≤ (γ:ℝ):=by exact_mod_cast (pollN_pos P)
 have h1:1 ≤ (c:ℝ):= by exact_mod_cast e
 have hh:1 ≤ (γ:ℝ)*4*c:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 (by norm_num)) h1
 exact le_mul_of_one_le_left (by positivity) hh
lemma withinAim (V:Enrolled P d (stairW d) w): withinT (blazeF P c d w) ((4*(1+c)*γ+1)*R d) ∧ withinT (deputize P d w) ((4*(1+c)*γ+1)*R d):=by
 let Q:= girder P d; let r:=((4*(1+c)*pollN P+1):ℕ)
 have h(c:ℕ):idleCar P ≤ Q:=by unfold Q girder trailerH idleCar; omega
 constructor; all_goals intro b i; have hz:=chip P w V i
 · cases b <;> (unfold blazeF; simp only [Bool.false_eq_true, ite_false, ite_true,cruise_price,Pi.zero_apply,mul_zero,add_zero,fling_price])
   · have he: Q ≤ r*Q:= le_mul_of_one_le_left (by positivity) (by unfold r; omega)
     unfold r Q at he; split <;> constructor <;> omega
   let H:ℤ:= (pollN P:ℤ)*bootH P c d i; have hH:0 ≤ H:=by unfold H bootH spindle; split_ifs <;> positivity
   have hp:H ≤ ((↑(4*(1+c)*pollN P*Q):ℤ)):=by
      unfold H bootH spindle
      split_ifs <;> norm_cast
      · change pollN P*(c*(4*Q))≤_
        calc _ = 4*c*pollN P*Q:=by ring
             _ ≤ _:= by gcongr; omega
      calc _ ≤ pollN P*(4*Q):=by gcongr; exact h c
           _ = 4*1*pollN P*Q:=by ring
           _ ≤ _:= by gcongr; omega
   change -((r*Q:ℕ):ℤ) ≤ nodeC w i+H ∧ _+H ≤ ((r*Q:ℕ):ℤ)
   have he: r*Q=4*(1+c)*pollN P*Q+Q:=by unfold r; ring
   change _ ∧ -(Q:ℤ) ≤ nodeC w i ∧ nodeC w i ≤ Q at hz; rw [he,Nat.cast_add]; constructor <;> linarith only [hz.2.1,hz.2.2,hp,hH,show (0:ℤ)≤↑(4*(1+c)*pollN P*Q) from Int.natCast_nonneg _]
 · have he : Q ≤ r*Q:= le_mul_of_one_le_left (by positivity) (by unfold r; omega)
   unfold r Q at he; unfold deputize; omega
lemma licensed :∃ l:ℕ,∀ᶠ d:ℕ in atTop, (ρ d) ≤ (χ d)^l ∧ ∀ w:Cover, Enrolled P d (stairW d) w→ withinT (blazeF P c d w) (intervalZ (stackW d) l P) ∧ withinT (deputize P d w) (intervalZ (stackW d) l P):=by
 obtain ⟨l,h⟩:=span_price P; let r:=4*(1+c)*pollN P+1; refine ⟨l+1,?_⟩
 filter_upwards [h,(stages_q P).eventually_ge_atTop (r:ℝ)] with d h t
 have hv:1 ≤ χ d:=summitT _
 refine ⟨h.1.trans (pow_le_pow_right₀ hv (Nat.le_succ _)),fun w p=> ?_⟩
 have hx : r*R d ≤ intervalZ (stackW d) (l+1) P:=by
    have he: (r:ℝ)*(ρ d) ≤ (χ d)^(l+1):=by rw [pow_succ']; exact mul_le_mul t h.1 (Nat.cast_nonneg _) (zero_le_one.trans hv)
    exact_mod_cast he.trans (Nat.le_ceil _)
 obtain ⟨x,y⟩:=withinAim P c d w p
 exact ⟨raiseB x hx,raiseB y hx⟩
where raiseB {o:Bool→ Cover}{a b:ℕ}(p:withinT o a)(q:a ≤ b):withinT o b:=fun i j=>by have h:=p i j; omega
-- serum shifted
open CF.Onyx Stationary
variable {D:ℕ→ℕ}(W:ℕ→ Cover)(V:∀i:ℕ, Enrolled P (D i) (stairW (D i)) (W i))(u:1 ≤ c)
include V u
lemma leader(i:ℕ):0< led P c (D i) (W i):=lt_of_lt_of_le (show 0< (ρ (D i)) from (by exact_mod_cast (show 0 < R (D i) from measure_min P (D i)))) (ledG P c _ _ (V i) u)
lemma elevate(x:Tendsto D atTop atTop): Tendsto (fun d=>led P c (D d) (W d)) atTop atTop:= tendsto_atTop_mono (f:=fun d=>ρ (D d)) (fun d=>ledG P c _ _ (V d) u) (tendsto_natCast_atTop_atTop.comp ((measuring_up P).comp x))
lemma lensΔ(x:Tendsto D atTop atTop): Tendsto (fun d=>riseX (led P c (D d) (W d)) (nodeC (blazeF P c (D d) (W d) false)-nodeC (blazeF P c (D d) (W d) true))) atTop (𝓝 (-YM.basis 3)):=by
 rw [(PiLp.homeomorph 2 (fun _:Axis=>ℝ)).isInducing.nhds_eq_comap (-YM.basis 3),tendsto_comap_iff,tendsto_pi_nhds]; intro i
 change Tendsto (fun d=> (↑((nodeC (blazeF P c (D d) (W d) false)-nodeC (blazeF P c (D d) (W d) true)) i):ℝ) / led P c (D d) (W d)) atTop (𝓝 (- ((YM.basis 3) i)))
 simp_rw [suitability]; by_cases g:i=(3:Axis)
 · subst i; change Tendsto (fun d:ℕ=> -(led P c (D d) (W d))/led P c (D d) (W d)) atTop _
   simp_rw [neg_div_self (leader P c W V u _ |>.ne')]; rw [basis_eq]; simp
 let z:=-(γ:ℝ)*(4*(idleCar P:ℝ)); have he:Tendsto (fun d:ℕ=> z/(led P c (D d) (W d))) atTop (𝓝 0):=by simpa only [Function.comp_def,← div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp (elevate P c W V u x)|>.const_mul z)
 simp_rw [if_neg g]; rw [basis_eq]; simpa [z,g] using he
#check suitability
#print axioms mandate
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
