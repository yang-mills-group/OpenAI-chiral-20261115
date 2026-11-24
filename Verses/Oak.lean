import LusterS.Anchored
import Verses.Bramble
import YM.SU5.Relativistic.Rebuke
import YM.CF.BPress.Spin.Touches
import Verses.Checkup
import YM.CF.Cubes.Inside
import YM.Work.E08
/-!
# One frame from positive curvature bound on the actually paid sites.
Use Work.E08 axial coarse estimate (works here directly on the gauge grid),
then shift to fixed continuous stencil rather than picking a frame measurably. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate.Pannier
open Work.E08
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
open YM.Pressure YM.Gleam YM.Gleam.Luster YM.Gleam.Luster.Almanac Grade
namespace Flint
abbrev ratioV:ℝ:= tauA/3
abbrev marginV:ℝ:= ratioV/2
abbrev claimV:ℝ:= ratioV/4
abbrev cliffsF (x:ℝ):ℕ:= ⌈x^ratioV⌉₊
abbrev wallsF (L:Side)(x:ℝ):= L.val * cliffsF x
lemma caps_grade (L:Side):Grade ratioV (fun x => (wallsF L x:ℝ)):=by unfold wallsF cliffsF; push_cast; apply Grade.scaleB _ (ceil_float (pitch ratioV) _ (by norm_num [ratioV,tauA])); filter_upwards [eventually_ge_atTop (0:ℝ)] with x h; positivity
lemma elevation :∀ᶠ x in atTop, 1≤cliffsF x ∧ cliffsF x≤cliffs x :=by
 filter_upwards [eventually_ge_atTop (1:ℝ)] with x h
 have hp:1≤x^ratioV:=Real.one_le_rpow h (by norm_num [ratioV,tauA]); refine ⟨Nat.ceil_pos.mpr (zero_lt_one.trans_le hp), Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le h (by norm_num [ratioV,tauA]))⟩
lemma stake_block (L:Side) :∀ᶠ x in atTop, wallsF L x ≤ walls L x:= elevation.mono fun x h=> Nat.mul_le_mul_left L.val h.2
/-- Interior r at w, after margin d=radiusB x. Book proportion. -/
lemma block_bill :∀ᶠ x:ℝ in atTop,∀ w r:ℕ,cliffsF x ≤ 2*w+1→(r+radiusB x+1=w → ((2*w+1:ℕ):ℝ)^4-((2*r+1:ℕ):ℝ)^4 ≤ x^(-marginV)*((2*w+1:ℕ):ℝ)^4) ∧ radiusB x+1 ≤ w:=by
 let d(x):=radiusB x
 have hd: Grade 0 (fun x=>(16:ℝ)*((d x:ℝ)+1)):=Grade.scaleB _ (radiusBill.plus (block 1))
 filter_upwards [hd.cost_p (b:=marginV) (by norm_num [marginV,ratioV,tauA]),eventually_ge_atTop (1:ℝ)] with x h hx w b v
 let z:=(2*w+1:ℝ); have hp:x^ratioV≤z:= (Nat.le_ceil _).trans ((Nat.cast_le (α:=ℝ)).mpr v |>.trans_eq (by unfold z; push_cast; rfl))
 let t:=(d x:ℝ)+1; have ht:1≤t:= by unfold t; simp
 have hg: x^marginV≤ x^ratioV:=Real.rpow_le_rpow_of_exponent_le hx (by norm_num [marginV,ratioV,tauA])
 have hv: 16*t≤x^marginV:= (le_abs_self _).trans h
 have hu:radiusB x+1 ≤ w:=by
    have he:(d x:ℝ)+1 ≤ w:=by unfold z at hp; linarith only [ht,hg,hp,hv]
    exact_mod_cast he
 refine ⟨fun p=>?_,hu⟩
 push_cast
 let y:= (2*b+1:ℝ); have he:z=y+2*t:=by
    unfold z y t d; rw [←p]; push_cast; ring
 have hh:4*x^marginV≤ (4:ℝ)*x^(-marginV)*z:=by
    have hf:= mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (zero_le_one.trans hx) (-marginV)); rw [←Real.rpow_add (zero_lt_one.trans_le hx),show -marginV+ratioV=marginV from (by unfold marginV; ring)] at hf; linarith only [hf]
 have hZ:0≤z:=by unfold z; positivity
 have hY:0≤ y:=by unfold y; positivity
 have h0:y≤z:=by linarith only [he,ht]
 have h₁ : z^3+z^2*y+z*y^2+y^3 ≤4*z^3:=by nlinarith only [hZ,hY,pow_le_pow_left₀ hY h0 2,pow_le_pow_left₀ hY h0 3,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY h0 2) hZ,mul_le_mul_of_nonneg_left h0 (sq_nonneg z)]
 have h₂:0≤x^(-marginV):=by positivity
 change z^4-y^4≤ _*z^4
 rw [show z^4-y^4=(z-y)*(z^3+z^2*y+z*y^2+y^3) from (by ring)]; refine (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr h0)).trans ?_; rw [show z-y=2*t by linarith only [he]]; have hf:= (show 8*t≤x^(-marginV)*z from by linarith only [hh,hv,ht]); nlinarith only [mul_le_mul_of_nonneg_right hf (pow_nonneg hZ 3)]

end Flint
end YM.CF.Pannier.Chancel
