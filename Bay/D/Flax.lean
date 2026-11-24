import Bay.D.Parlor
import Bay.D.Tunic
import Bay.D.Oriole
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

open Push.SectorMeasure
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
 (s i k:ℕ)
open Buffered.Afterglow Sleigh

local notation "N"=>count Y s i
local notation "Hₓ"=>hat P.R.L P.x s
local notation "U"=>gram Y s i k

theorem flax_ratio (c:Pane N→ℂ):
 Journey.compass Y i k s (Hookah.chalkOp c)=
 (∫ x,c x.1 * sealMark Y s i U x ∂Scree.city N)/compensated P.U U (Papal.room Y s i):=by
 let b:= Complex.exp (- (gram Y s i k).v)
 let r:=denZ (gram Y s i k) P.U (Papal.room Y s i)

 have hp(x:Orbit N): c x.1*sealMark Y s i U x =
    b*letterRead (Hookah.chalkOp c ⟨x.1,Papal.room Y s i x⟩) (r x):=by
    dsimp only [letterRead,Hookah.chalkOp,sealMark]
    rw [ContinuousLinearMap.comp_apply,act_smul,act_one,map_smul, mul_left_comm]
    rfl
 simp_rw[hp]
 rw[integral_const_mul,compensated]
 exact (mul_div_mul_left _ _ (Complex.exp_ne_zero _)).symm

abbrev Fly(z:ℂ)(m x:ℝ):= z.re*m+wavePay x
structure Chintz :Prop where

 wind(o d:Seat N)(F:Pane N→ℝ)(W:Chalk (More N) ℝ)
     (t:Lease Y s i k o d F W)
     (z:ℂ)(v:‖z‖≤thetaB Hₓ)
     (L:List (Fabric N))(h:Sylvan (Tunic o d F z) 0 L):
     ‖Journey.compass Y i k s (buffet L)‖ ≤
       Real.exp (L.length*Fly z (beans Y s i k W) Hₓ+6*oar Hₓ*sites N)

lemma flaxCompass (D:DryDock P):∀ᶠ s in atTop,∀ i k:ℕ, (Y.voyage i).kick≤k →
   s≤Y.uv k → Chintz Y s i k:=by
 obtain ⟨p,δ,a,C,b,v,w,G⟩:=D
 filter_upwards [ivory Y,relative_shine Y G (cisternFrom P p) 1 zero_le_one, winters_port P,(stage_slope P.V P.x).eventually_gt_atTop 0,
   (stage_slope P.V P.x).eventually ((skca P.R.L 2 (dev_R P.R).1 (by norm_num: (0:ℝ)<1/2)).pure (b:=-(1/500:ℝ)) (by norm_num))]
    with r₀ t V W' hz hα j Lm l₀ l₁
 let x:=hat P.R.L P.x r₀
 let n:=count Y r₀ j
 let g:=gram Y r₀ j Lm
 let E:=dleaf P.R.L x
 have h: HillSeal Y r₀ j Lm g E:=⟨rfl,rfl,rfl,rfl,rfl,(prices_plot Y r₀ j Lm l₁).2.2.2.2⟩
 obtain ⟨n',r,u⟩:=W' (Y.ir j)

 constructor
 intro o d F W l z f L hL
 change Ion _ _ _ _ _ _ _ _ _ _ _ _ _ at l
 obtain ⟨gs,c,e,H,bill⟩:= Tunic.invoice hL (Mi x) l.limit
 let A:=gusts gs F
 let m:=beans Y r₀ j Lm W
 let M:=Mi x
 let C₀:=L.length*(thetaB x^2*M^2)
 let C₁:=L.length*(z.re*m+titheB x)
 let μ (v:Orbit n):=c v.1*sealMark Y r₀ j g v
 have hA:VisiblePolar Y r₀ j Lm 1 z.re C₁ r A:=by
    have hh:=t j Lm l₁ o d gs F W l e z.re ((Complex.abs_re_le_norm _).trans f) r u
    rw[Fintype.card_fin] at hh;exact hh
 have hh(v: Orbit n):
     ‖μ v‖≤Real.exp (z.re*A v.1+C₀+rink Y r₀ j Lm v.1/2) * ‖sealMark Y r₀ j g v‖:=by
    unfold μ;rw[norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (bill v.1).trans (Real.exp_monotone ((add_le_add le_rfl (mul_le_mul_of_nonneg_left
       (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) f _) (sq_nonneg M)) (Nat.cast_nonneg _))).trans
       (le_add_of_nonneg_right (div_nonneg (rink_free Y r₀ j Lm hz v.1) (by norm_num)))))
 have ht:=V j Lm l₀ l₁ g E h r u A z.re C₁ C₀ hA μ (Eventually.of_forall hh)
 

 rw [H, flax_ratio,norm_div]
 refine ((div_le_div_of_nonneg_right (norm_integral_le_integral_norm (μ:=Scree.city n) μ) (norm_nonneg _)).trans ht).trans (Real.exp_monotone ?_)
 have hE:E≤oar x:= hα
 apply add_le_add ?_ (mul_le_mul_of_nonneg_right
      (show 3*E+3*oar x≤6*oar x by linarith only [hE])
      (zero_le_one.trans (sites_pos _)))
 exact le_of_eq (show C₁+C₀=L.length*Fly z m x from by unfold C₁ C₀ M Fly wavePay;ring)

end YM.CF.Bay.D
