import SatinThinCentury
import YM.SatinExist.QuoteHeight
import YM.SatinExist.Powder

/-! ## Quantitative consultation time. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
variable (P:Spine) (j:Axis) (s f:ℕ)(k:List Axis)(A:ℝ)
local notation "X" s:max=> P.rootSpace f s k
abbrev columnW:= twiceT (P.rootSpace f s k) j
lemma column_bill : Watchdesk (f:=s) P j (X s) (P.columnW j s f k) :=by
 let W:=P.columnW j s f k
 have hp:= P.point_bought j s f k
 unfold columnW twiceT; constructor
 · exact P.rent_honors ..
 · omega
 push_cast; rw [abs_of_nonneg hp.le,mul_comm (nodeC _ j)]; exact le_mul_of_one_le_left (by omega) (ruler_gene _)

local notation "C₀" s:max=> P.columnW j s f k
local notation "Λw"=> timeMesh P.par
local notation "d" s:max=>P.pinTime j f s k
noncomputable abbrev turtle:= whenly (timeMesh P.par) s (P.columnW j s f k)
local notation "h₀" s:max=>P.turtle j s f k
lemma prime_length : ↑(h₀ s)= (2:ℝ)* P.sidesPerTick*P.pinTime j f s k:=by
 let t:ℕ:= C₀ s; let v:= nodeC (X s) j; let x:=P.sidesPerTick
 have he: (t:ℝ)= 2*(↑v:ℝ):=by exact_mod_cast (show (t:ℤ)=2*v from (by have H:0<v:=P.point_bought j s f k; change ((2*v.natAbs:ℕ):ℤ)= _; omega))
 have hp:(whenly Λw s t:ℝ)= (t:ℝ) * P.macroStep s:=by unfold whenly; push_cast; rfl -- macroStep check
 change (whenly Λw s t:ℝ)= _; rw [hp,he]; unfold pinTime; change 2*(↑v:ℝ)*P.macroStep s=2*(x:ℝ)*(_*_/x); have h:0<x:=P.sides_pos; field_simp; exact mul_comm .. 
lemma prime_fit : 0<P.pinTime j f s k ∧ P.pinTime j f s k< (h₀ s:ℝ):=by
 have h:= P.pin_p j f s k; refine ⟨h,?_⟩; rw [P.prime_length]; have hp: (1:ℝ)≤P.sidesPerTick:=by exact_mod_cast P.sides_pos
 exact lt_mul_of_one_lt_left h (by linarith)
lemma turtle_down : Tendsto (fun s:ℕ=> (P.turtle j s f k:ℝ)) atTop (𝓝 0):=by simp_rw [P.prime_length]; simpa only [mul_zero] using (P.pin_approach j f k).const_mul ((2:ℝ)* P.sidesPerTick)
-- price uniformly ALL soon, use pillar approach. Pole bounds.
local notation "E₀"=> P.par
local notation "L"=> P.par.R.L
private lemma corn (W Y T:ℝ) (u:0≤W)(v:0 ≤Y)(h: T>0): Y*(2*W)^3*W ≤ T*(4*(W+Y))^4+Y*(2*W)^3*W:=le_add_of_nonneg_left (by positivity)
variable {P}
-- avoid overclaim.UV growth.Here Theta is constant at fitting protector
lemma blasted (P:Spine) (i:ℕ)(w:ℕ)(q:P.repeatBill w i) : stopX P.par i * ↑(Yoke.spacePrice P.par.block w (P.labW i)) ≤ (P.par.block.val:ℝ)*65536:=by
 let B:= P.par.block.val; let M:= plusAgain P.par.block (P.labW i); let V:=stopX P.par i; have hp:V ≥ 0:=mul_nonneg (by norm_num) (coin_pos ..).le; have hv:V*(4*((w:ℝ)+M))^4 ≤ 1:=by unfold repeatBill at q; push_cast at q; exact q
 change V * _ ≤ (B:ℝ)*65536
 unfold Yoke.spacePrice; push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 let R:ℝ:= (w:ℝ)+M; have hb: (w:ℝ)≤ R:=le_add_of_nonneg_right (by positivity)
 have he: (M:ℝ)≤ R:=le_add_of_nonneg_left (by positivity) -- replace
 change V*((16:ℝ)*(16* (B:ℝ) * (w:ℝ))*(2*M)^3)≤ _
 calc
  _ ≤ V*(16*(16* (B:ℝ) * R)*(2*R)^3):=by gcongr
  _ = V*(4*R)^4*((B:ℝ)*8):=by ring
  _ ≤ 1*((B:ℝ)*8):=by gcongr
  _ ≤ _:=by nlinarith only [Nat.cast_nonneg (α:=ℝ) B]
variable (P)
lemma column_paid : ∃ D:ℝ, ∀ᶠ s:ℕ in atTop, Real.sqrt (P.fenceZ A s (s+1) (C₀ s)+3) ≤ D ∧ Real.sqrt (poleX P s (C₀ s) A+3)≤ D:=by
 obtain ⟨z,hz,kp⟩:=P.tiny_purses
 let B:= z * Real.exp (8*A); let C:= Real.exp ((P.par.block.val:ℝ)*65536); let K:=fareMin L 1; have hK:0 ≤ K:=by unfold K fareMin; positivity
 let Y:=(1+K)*B; have ht:0 ≤ C:=(Real.exp_pos _).le
 refine ⟨Real.sqrt ((2*(Y*C))^2+3),?_⟩; filter_upwards [P.size_honors,P.earns_newsprint j 1 zero_lt_one,P.offers_plans j 1 zero_lt_one,kp] with s ⟨p,h'⟩ q v hx₀
 have hp:slotFee P.par s ≤z:= hx₀.1; -- tune
 have hq := P.blasted s (C₀ s) (v.1 _ (q f k));
 let fq(s:ℕ)(x:ℝ):= truckBill P.par.block (C₀ s) (P.labW s) x (stopX P.par s);
 have h(x:ℝ)(g:0 ≤ x)(e:x ≤Y): Real.sqrt ((2* fq s x)^2+3) ≤ Real.sqrt ((2*(Y*C))^2+3):=by
    have p:0 ≤ fq s x:=by unfold fq truckBill; positivity
    have he:fq s x ≤ Y*C:= mul_le_mul e (Real.exp_le_exp.mpr hq) (Real.exp_pos _|>.le) (le_trans g e); gcongr
 have hx: 0 < stemX P.par s A:=mul_pos p (Real.exp_pos _); have hr:B≥0:=mul_nonneg hz.le (Real.exp_pos _).le; have he:stemX P.par s A ≤ B:=mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le; have hv:P.stemZ A s (s+1)= K*stemX P.par s A:= by unfold stemZ; rw [Nat.add_sub_cancel_left]
 unfold fenceZ; rw [hv]
 exact ⟨h _ (mul_nonneg hK hx.le) ((mul_le_mul_of_nonneg_left he hK).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hr)), h _ hx.le (he.trans (le_mul_of_one_le_left hr (by linarith only [hK])))⟩ -- unfold Y issue
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
