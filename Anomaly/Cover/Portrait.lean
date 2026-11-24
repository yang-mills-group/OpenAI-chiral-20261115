import Anomaly.Cover.Catch
import Anomaly.Cover.Court
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke
open Swell Sonar StageQ Ione Vow Tapestry.StageW
namespace Spine
universe u
variable (P:Spine)
open Heat
-- fees at original p Purchase Mortgage food.rawQ; E delta of mesh grasp.Measuring stencil transport. E price, any aligned lag inspecting passports.
local notation "M"=>P.calibration
variable {s m:ℕ} (G:Proscenium→ Tapestry.Swatch (P.roomFox s m)) (R:ℝ) (z:ℤ)
local notation "z'"=>gaugeShift P.par.block z
local notation "X0"=>hat P.par.R.L P.par.x s
local notation "t0"=> Pressure.temp X0
open Mew
local notation "d0"=>pinpr P.par.R.L X0/(Pressure.temp X0)^2
local notation "SP"=>roomFox P s m
def gaugeAccount (P:Spine)(s m:ℕ)(A:Proscenium→ Tapestry.Swatch (P.roomFox s m)) : Family P.calibration:=
 let x:=hat P.par.R.L P.par.x s
 let u:=pinpr P.par.R.L x / (Pressure.temp x)^2
 (u:ℂ) • (Tapestry.render (P.roomFox s m) P.calibration (preVote A))
abbrev Sherbert := mirror M (3:Axis) (gaugeShift P.par.block z) (gaugeAccount P s m G)*gaugeAccount P s m G
-- representation price (SQ/SAT)^2. no uses positivity outside stamped
abbrev eraPrice(s:ℕ)(R:ℝ):=pinpr P.par.R.L (hat P.par.R.L P.par.x s)/(Pressure.temp (hat P.par.R.L P.par.x s))^2/((hat P.par.R.L P.par.x s)*R^4)
abbrev refleN (x:ℤ) (F:Family P.calibration) := P.E s (mirror M 3 x F * F)
-- E reflection. plane pos. any block clock.Not cap lhs. exact co-location proofs.
structure PlentyC (P:Spine)(s m:ℕ)(G: Proscenium→ Tapestry.Swatch (P.roomFox s m))(R C:ℝ)(z:ℤ): Prop where
 room : Tower.region 3 (gaugeShift P.par.block z) P.calibration.ℓ (P.roomFox s m)
 pose : P.gaugeAccount s m G∈ wing P.calibration 3 (gaugeShift P.par.block z)
 debt : C*eraPrice P s R ≤ Real.sqrt (refleN P (s:=s) (gaugeShift P.par.block z) (P.gaugeAccount s m G)).re
 axis : 0 ≤ refleN P (s:=s) (gaugeShift P.par.block z) (P.gaugeAccount s m G)
private lemma gull {R:ℝ} {z A y D x:ℝ}(p:0≤x)(hp:0≤D)(d:y= x^2*z)(u:0<R)(h:0<A)(g:A ≤ R^8*y)(e:0<x) : Real.sqrt A / (x*R^4) ≤ Real.sqrt z:=by
 have hw:0 ≤ y:=by by_contra! t; exact lt_asymm h (lt_of_le_of_lt g (mul_neg_of_pos_of_neg (pow_pos u _) t))
 have hv:0 ≤ z:= nonneg_of_mul_nonneg_right (d ▸ hw) (pow_pos e _)
 rw [div_le_iff₀ (by positivity)]
 have hr:0 ≤ Real.sqrt z:= Real.sqrt_nonneg _; apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
 rw [Real.sq_sqrt h.le,mul_pow,Real.sq_sqrt hv]; exact g.trans_eq (by rw [d]; ring)
lemma PlentyC.instruct {C:ℝ}(u:0<R)(v:0< C)(x:0 < hat P.par.R.L P.par.x s)(h:Tower.region 3 (gaugeShift P.par.block z) P.calibration.ℓ (P.roomFox s m))(g:C ≤ R^8 * (refleN P (s:=s) (gaugeShift P.par.block z) (render (P.roomFox s m) P.calibration (P.XO s m G))).re):PlentyC P s m G R (Real.sqrt C) z:=by
 let U:= render SP M (preVote G); let d:=gaugeAccount P s m G; let j:=z'
 let V':= texture SP M (preVote G); let Y0:ℝ:= (refleN P (s:=s) j U).re
 have hd:0 ≤ d0:= div_nonneg (sq_nonneg _) (sq_nonneg _)
 have ht(B:ℝ): refleN P (s:=s) j ((B:ℂ) • U)=(B:ℂ)^2*refleN P (s:=s) j U:=by
    unfold refleN; rw [mirror_scale, Complex.star_def,Complex.conj_ofReal,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,←mul_smul,E_scale P.run P.large P.law s]; rw [pow_two]; apply aux_test ((axial M 3 j V').mono (show reflectedBox 3 j SP ⊆ reflectedBox 3 j SP ∪ SP from subset_union_left) |>.mul (V'.mono subset_union_right))
 have hm:0 ≤ refleN P (s:=s) j d:=boson_axial P.run P.large P.law s (InTest.smul ((↑(d0:ℝ)):ℂ) V') h
 refine ⟨h,(show d∈ wing M 3 j from ⟨SP,(InTest.smul ((↑(d0:ℝ)):ℂ) V'),h⟩),?_,hm⟩ -- shorthand membership from he
 have hy : R^8*(refleN P (s:=s) j (render SP M (P.XO s m G))).re= R^8*(X0^2*Y0):=by rw [XO,map_smul,ht X0,←Complex.ofReal_pow, Complex.re_ofReal_mul]
 have hc := gull (R:=R) (z:=Y0) (y:=X0^2*Y0) x.le hd rfl u v (g.trans_eq hy) x
 have he: Real.sqrt (refleN P (s:=s) j d).re=d0*(Real.sqrt Y0):=by rw [show d = ((↑(d0:ℝ)):ℂ) • U from rfl,ht d0,← Complex.ofReal_pow,Complex.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hd]
 change _ ≤ Real.sqrt (refleN P (s:=s) _ d).re; rw [he]; unfold eraPrice; refine (mul_le_mul_of_nonneg_left hc hd).trans' (le_of_eq (by ring))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
