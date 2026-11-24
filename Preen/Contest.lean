import Preen.Libation
import Preen.Gamma
import Preen.FoyerX
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
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
set_option maxRecDepth 6000
set_option maxHeartbeats 110000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Nc" i:max=> count P.run s i
local notation "Y"=>P.run
local notation "π₀" i:max => P.period (P.projection.rows i)
local notation "ζ₀" i:max => P.cutoff (P.projection.columns i)
open _root_.YM.Preen Calico _root_.YM.Gleam.Luster Almanac
/- Bare dimensional factors counter etc. Expense stamped.Pair adjusted purse: remitt exact = normalized $scale.$ -/
variable (x:P.Spectrum0 3)(w d:Cover)
local notation "Z"=> (plane 3 (0:ℤ))
noncomputable abbrev swapW(w:Cover):= (plane 3 (0:ℤ)).flee w
private def cruiseAt (d:Cover)(T:List Axis)(w:Cover):Cover:= T.foldr (fun i f=> Calico.slid (K) i (d i) f) w
noncomputable abbrev shuffleT(P:Spine)(d w:Cover):Cover:=cruiseAt P d Vacancy.ordinate w
private lemma wp_cruise(T: List Axis): P.cruise T d (wp P s w) = wp P s (cruiseAt P d T w):=by
 induction T with
 | nil=>rfl
 | cons i T h=> rw [P.cruise_step,AlgHom.comp_apply,h]; exact Subtype.ext (coilT ..)
lemma wp_visits (F:Cover): P.chartAll F (wp P s w)=wp P s (shuffleT P F w):=wp_cruise P s w F _
lemma cruise_alpha(T:List Axis)(h:T.Nodup)(k:Axis): nodeC (cruiseAt P d T w) k=nodeC w k + if k∈T then (pollN P:ℤ)* d k else 0:=by
 induction T with
 |nil=>simp [cruiseAt]
 |cons i T ih=>
    obtain ⟨l,t⟩:=List.nodup_cons.mp h
    rw [show cruiseAt P d (i::T) w= Calico.slid (K) i (d i) (cruiseAt P d T w) from rfl,bellV,ih t]; by_cases g:k=i
    · subst k; rw [if_neg l,if_pos rfl,if_pos List.mem_cons_self,add_zero]; rfl
    simp [g]
-- check ordinate.Nodup.
lemma cruise_price (k:Axis): nodeC (shuffleT P d w) k=nodeC w k+(pollN P:ℤ)*d k:= by unfold shuffleT; rw [cruise_alpha P w d _ (show Vacancy.ordinate.Nodup from ?_) k,if_pos (show k∈ Vacancy.ordinate from ?_)] <;> simp [Vacancy.ordinate] -- Finite basis?
lemma fling_price(i:Axis):nodeC (swapW w) i = if (3:Axis)=i then -nodeC w i else nodeC w i:=by rw [show nodeC (swapW w)= (Z).motion (nodeC w) from ((Z).mote w).symm,fling_move]; simp
noncomputable abbrev outlookT(P:Spine)(n:ℕ)(w:Cover):Bool→ Cover:=fun i=> match i with|false=>shuffleT P 0 (swapW w)|true=>shuffleT P (spindle P n (stairW n)) w
noncomputable abbrev deputize(P:Spine)(n:ℕ)(w:Cover):=fun _:Bool=> w
local notation "O" n:max=>outlookT P n w
local notation "skH" n:max=> stackW n
local notation "Kq" n:max=> P.singleState 3 (stackW n) x
local notation "M" n:max=> scaleY (hat P.par.R.L P.par.x (skH n))
lemma reflected_h: P.reflectTest 3 (wp P s w)=wp P s (swapW w):= Subtype.ext (ace ..)
set_option maxHeartbeats 240000 in
lemma homes_time(n:ℕ): let γ:= Kq n; let s:=skH n; let θ':ℝ:=(M n)^2/P.payday s; let C:= γ (bodyT P s (O n) true) - star (γ (bodyT P s (deputize P n w) false))*γ (bodyT P s (deputize P n w) false)
 ((θ')^2:ℂ) * expenseR P x s w 0 (spindle P n (stairW n))= C:=by
 intro γ sV a C; let p:=wp P sV; let Q:=spindle P n (stairW n); let i:ℂ:=a
 exact Poly γ i (P.chartAll Q) (P.chartAll 0 ∘ P.reflectTest 3) (p w) (p ((O n) true)) (p ((O n) false)) (wp_visits P sV w Q) ((congrArg (P.chartAll 0) (reflected_h P sV w)).trans (wp_visits P sV ..)) (Complex.conj_ofReal _)
where Poly {T:Type}[CommRing T][Algebra ℂ T](f:T→ₗ[ℂ]ℂ)(i:ℂ)(g v:T→T)(p a b:T)(e:g p=a)(h:v p=b)(hi:star i=i): i^2 * (f (v p*g p)-star (f p)*f p)=f ((i•b)*(i•a))-star (f (i •p))*f (i•p):=by rw [e,h, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul,map_smul, smul_eq_mul,map_smul,smul_eq_mul,star_mul',hi]; ring

lemma estateT(n:ℕ)(e:0<P.payday (skH n)):remitt P x n w= (girder P n:ℝ)^8 * ‖ (Kq n) (bodyT P (skH n) (O n) true)-star ((Kq n) (bodyT P (skH n) (deputize P n w) false))* (Kq n) (bodyT P (skH n) (deputize P n w) false)‖:=by
 let F:=expenseR P x (stackW n) w 0 (spindle P n (stairW n)); unfold remitt altitude; change ‖F‖*_ * _ /_ = _
 rw [←homes_time P x w n,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) e.le), div_pow,←pow_mul]; rw [show _root_.YM.Preen.breeze (hat P.par.R.L P.par.x (stackW n))=M n from (coin_scale ..).symm]; ring
#print axioms estateT
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
