import Bay.D.Silken
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

variable {K:Calibration}{x:ℝ} {d:ℕ}
local notation "ωₒ"=>BPress.drift
local notation "u₊"=>rightD K d

def Panel(K:Calibration)(x:ℝ)(d:ℕ):Prop:=
  2*ωₒ x^99≤rightD K d ∧ (rightD K d:ℝ)≤2*ωₒ x^101

abbrev halfSteps(K:Calibration)(d:ℕ):ℝ:=rightD K d/2

-- Gauge separation. Coefficient unknown; lag chosen independently.
lemma du_meter(u:Panel K x d): ωₒ x^99≤halfSteps K d∧ halfSteps K d≤ ωₒ x^101:=by
 unfold halfSteps;constructor <;> unfold Panel at u <;> linarith
lemma dome_big {a:ℕ}{h:ℝ→ℝ} (w:BPress.PL h)(l:0<a):
 ∀ᶠ x in atTop,h x ≤ ωₒ x ^ a:=by
 have y₀:BPress.NPL (fun x=> ((ωₒ x)^a)⁻¹):=by
    simpa only [Real.rpow_natCast_mul, Real.rpow_natCast] using
      BPress.npl_drift a (Nat.cast_pos.mpr l)
 filter_upwards[(w.times y₀).drop.eventually (ge_mem_nhds zero_lt_one)] with x g
 rw[←div_eq_mul_inv] at g -- beta?
 exact ((div_le_one (pow_pos (BPress.drift_pos _) _)).mp g)

lemma panels(K:Calibration):∀ᶠ x in atTop, ∃d,Panel K x d∧Even d:=by
 have h:BPress.PL (fun _:ℝ=>2*(taps K:ℝ)):= BPress.PL.const ..
 filter_upwards[dome_big (a:=2) h (by norm_num)] with x y
 let w:=ωₒ x^99
 have u:1≤w:=one_le_pow₀ (BPress.drift_one _)
 have v:(1:ℝ)≤(taps K):=by rw[←Int.cast_natCast,←ruler_cast];exact_mod_cast ruler_gene K.B -- exact_mod_cast 0<ℤ
 let n:=⌈w⌉₊
 have L:w≤(n:ℝ):=Nat.le_ceil _
 have G:(n:ℝ)≤2*w:=le_trans (Nat.ceil_lt_add_one (le_trans zero_le_one u)).le (by linarith)
 refine ⟨2*n,?_,even_two_mul _⟩
 unfold Panel rightD
 have W:(↑(taps K * (2*n)):ℝ) = (taps K:ℝ)*(2*n):=by simp[taps]
 rw[W]
 change _ ≤ (ωₒ x)^2 at y
 constructor
 · have q:2*w≤2*n:=by gcongr
   exact le_trans q (le_mul_of_one_le_left (by positivity) v)
 calc
  _ ≤ (taps K:ℝ)*(2*(2*w)):=by gcongr
  _ = (2*(taps K:ℝ))*(2*w):=by ring
  _ ≤ (ωₒ x)^2*(2*w):=by gcongr
  _ = _ := by unfold w;ring

lemma dome_small(C:ℝ)(n:ℕ){a:ℝ}(u:0<a):
  ∀ᶠ x in atTop,C*ωₒ x^n ≤ atRate a x:=by
 have q : 0<thinRate a:=by unfold thinRate; positivity
 have h:= (BPress.npl_drift_g n (2 *thinRate a) (by positivity)).const_mul C
 filter_upwards [eventually_gt_atTop (0:ℝ),h.drop.eventually (ge_mem_nhds zero_lt_one)] with x v t
 have r:BPress.g x ^ (2*thinRate a)=(atRate a x)⁻¹:=by
    change (Real.sqrt x)⁻¹ ^ (_:ℝ)=_
    rw [Real.inv_rpow (by positivity),Real.sqrt_eq_rpow,←Real.rpow_mul v.le,show (1/2:ℝ)*(2*thinRate a)=thinRate a by ring]
 rw [r,Real.rpow_natCast, ←mul_assoc,←div_eq_mul_inv] at t
 exact (div_le_one (Real.rpow_pos_of_pos v _)).mp t

structure Styx(K:Calibration)(x:ℝ)(m d:ℕ):Prop where
 left:Itinerary x
 paid:Able K x
 right:Cowl K (radiusB x) d
 sub:4*(rightD K d:ℝ)≤atRate 12 x
 high:Remote K m (radiusB x/10) d
 in_: (wholeD K d:ℝ)≤reedR x

lemma cowl_price(K:Calibration):∀ᶠ x in atTop,∀d,
  Panel K x d→ Cowl K (radiusB x) d:=by
 filter_upwards[dome_big (a:=99) ((BPress.PL.const (K.ℓ+14)).add BPress.PL.scale)
    (by norm_num)] with x h d l
 unfold Cowl
 have p:(K.ℓ:ℝ)+radiusB x+14≤rightD K d:=by unfold BPress.lscale at h; have:=l.1; linarith
 exact_mod_cast p

lemma styxed(K:Calibration)(m:ℕ):∀ᶠ x in atTop,∀d,Panel K x d→Styx K x m d:=by
 have y:=meander₀ m
 let Y:= meander m
 let v:BPress.PL (fun x=> (BPress.lscale x +12)*Y):=
   (BPress.PL.scale.add (BPress.PL.const _)).mul (BPress.PL.const _)
 filter_upwards [itineraries,able K,cowl_price K,dome_small 8 101 (by norm_num:0<(12:ℝ)),
    dome_big (a:=99) v (by norm_num),dome_small 4 101 (by norm_num:0<(2:ℝ))]
    with x h p t j q k d r
 have ⟨u,z⟩:=r
 refine ⟨h,p,t _ r,by linarith,?_,?_⟩
 · unfold Remote wholeD
   rw [Nat.cast_mul]
   have a:(↑(radiusB x/10):ℝ)≤ BPress.lscale x:= le_trans
       (show _≤ (radiusB x:ℝ) from by exact_mod_cast Nat.div_le_self _ _) (by unfold BPress.lscale;linarith)
   have b: ((↑(radiusB x/10):ℝ)+12)*meander m ≤ωₒ x^99 :=
      (mul_le_mul_of_nonneg_right (add_le_add_left a _) y.le).trans q
   have c: 1≤ωₒ x^99:=one_le_pow₀ (BPress.drift_one _)
   norm_num only[Nat.cast_ofNat];nlinarith only[b,u,c]
 unfold wholeD reedR r_R; rw[Nat.cast_mul,Nat.cast_ofNat];linarith

end YM.CF.Bay.D
