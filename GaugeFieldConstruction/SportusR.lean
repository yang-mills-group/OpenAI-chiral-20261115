import GaugeFieldConstruction.AltitudeJ
import GaugeFieldConstruction.LuciaStarJ
import GaugeFieldConstruction.Degrees
import GaugeFieldConstruction.TrickΛ
import GaugeFieldConstruction.Cadent
import GaugeFieldConstruction.Pyrus
import GaugeFieldConstruction.SeraphicJ
import GaugeFieldConstruction.BenguelaJ
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
local notation "ΤΓ"=> P.run
local notation "Pα"=> P.par
local notation "δα"=> P.par.R.L
section
open Gleam BProof BProof.PricePort Gleam.Guide Gleam.clocks
open GaugeFieldConstruction GaugeFieldConstruction.Calibration
variable (P)
lemma loftL_R : (2:ℝ) ≤ P.par.R.L.val:=by exact_mod_cast (show 2 ≤P.par.R.L.val from (by have h:=P.par.R.coarse; omega))
lemma choiceR (f:ℕ):∃ n:ℕ,coos (P.urnMark f)≤ (P.par.R.L.val:ℝ)^n:= ((tendsto_pow_atTop_atTop_of_one_lt (lt_of_lt_of_le one_lt_two (loftL_R P))).eventually_ge_atTop (coos (P.urnMark f))).exists
noncomputable def boxNP (P:Spine)(f:ℕ):ℕ:= Nat.find (choiceR P f)
abbrev SpringR (P:Spine)(f:ℕ):ℝ := (P.par.R.L.val:ℝ)^(boxNP P f)
abbrev SportR (P:Spine)(m f:ℕ):ℕ := f+ boxNP P f * (8*m)
lemma SpringR.low (P:Spine)(f:ℕ): coos (P.urnMark f) ≤ SpringR P f:= Nat.find_spec (choiceR P f)
lemma coos_R(y:ℝ):1 ≤ coos y:=by rw [show coos y=_ from coin_scale y]; exact Real.one_le_exp (sq_nonneg _)
lemma SpringR.tall (P:Spine)(f:ℕ): 1 ≤ SpringR P f:= (coos_R _).trans (low P f)
lemma SpringR.high (P:Spine)(f:ℕ): SpringR P f ≤ coos (P.urnMark f)* (P.par.R.L.val:ℝ) :=by
 rcases Nat.eq_zero_or_pos (boxNP P f) with h|h
 · unfold SpringR; rw[h,pow_zero]; apply one_le_mul_of_one_le_of_one_le (coos_R _) (one_le_two.trans (loftL_R P)) -- tune
 obtain ⟨k,H⟩:=Nat.exists_eq_succ_of_ne_zero h.ne'
 have v:=Nat.find_min (p:=fun i=> coos (P.urnMark f) ≤ (P.par.R.L.val:ℝ)^i) (choiceR P f) (show k < boxNP P f from by omega); unfold SpringR; rw[H,pow_succ]; exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge v)) (Nat.cast_nonneg _)
lemma SpringR.escape : Tendsto (SpringR P) atTop atTop:=by
 refine tendsto_atTop_mono (fun i=> (SpringR.low P i)) ?_; apply Tendsto.comp («f»:= P.urnMark) («g»:= coos) _ (turnover P.par)
 unfold coos; simp_rw [show ∀ y:ℝ,BProof.coin y 0 1 0= Real.exp (Real.log (Real.log y)^2) from coin_scale]; exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by decide:2≠0)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)) -- tune
lemma SpringR.telescope (f:ℕ): (boxNP P f:ℝ) ≤ SpringR P f:=by
 let L:ℝ:=P.par.R.L.val; have h:2 ≤L:=loftL_R P; let U(n:ℕ):=L^n
 suffices ∀ n:ℕ, (n:ℝ)+1 ≤ U n from (le_add_of_nonneg_right zero_le_one).trans (this _)
 intro n; induction n with
 | zero=> simp [U]
 | succ n ih=>
   push_cast; unfold U at *; rw [pow_succ]; have ht: 1 ≤ L:=one_le_two.trans h; nlinarith only [ih,h, Nat.cast_nonneg (α:=ℝ) n, mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans ht) n)]
lemma SportR.hop (m f:ℕ):f ≤ SportR P m f:= Nat.le_add_right ..
lemma SportR.tale(m:ℕ): Tendsto (SportR P m) atTop atTop:= tendsto_atTop_mono (SportR.hop P m) tendsto_id
local notation "Κs" => P.urnMark
lemma growthL_R(m:ℕ) :∀ᶠ f:ℕ in atTop, P.urnMark f≤ P.urnMark (SportR P m f) ∧ P.urnMark (SportR P m f) ≤ (P.urnMark f)^2:=by
 let t(f):=boxNP P f*(8*m); let b:= Vale.billX P.par.R.L; let A:= (P.par.R.L.val:ℝ)*(8*m)*b
 have ht:0≤b:=Vale.pitch .. 
 let S:= SportR P m; have Hp(f:ℕ):P.urnMark (SportR P m f)= P.urnMark f+ (boxNP P f:ℝ)*(8*m)*b:=by unfold SportR urnMark Vale.hat b; push_cast; ring
 have hx:∀ᶠ y:ℝ in atTop,A*coos y ≤ y:=by
   filter_upwards[grade_price ((RunRate.coins 0 1 0).cmul A) (a':=1) (b':=0) (Or.inl zero_lt_one) 1 zero_lt_one 0,eventually_gt_atTop (0:ℝ)] with y h g; simpa only [one_mul,coinY g] using (le_abs_self _).trans h
 filter_upwards [(turnover P.par).eventually hx,(turnover P.par).eventually_ge_atTop 2] with f H Y
 rw [Hp]; have hz:= (SpringR.telescope P f).trans (SpringR.high P f); have h: (boxNP P f:ℝ)*(8*m)*b ≤ P.urnMark f:=calc
    _ ≤ (coos (P.urnMark f)*P.par.R.L.val)*(8*m)*b :=by gcongr
    _ = A*coos _:=by unfold A; ring
    _ ≤ _:= H
 refine ⟨le_add_of_nonneg_right (by positivity),?_⟩; nlinarith only [h,Y] -- norm tune hidden
#print axioms growthL_R
end
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
