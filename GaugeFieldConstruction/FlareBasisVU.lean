import GaugeFieldConstruction.DazeBootUL
/-!
# Detecting prices of any U4 cold readers directly

 No rotational conclusions needed. Only same-U4 probes applied. phrase in Test costs so ports align true plenum budgets.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
open Wick Mirror Invoice Raster
-- exact testimonies on this blue archive Χ support. X contours. pin rank payments may involve *running* contributions. price convergence diamond.
def FlareΥVU {n:ℕ}(Z:CloudsL)(w:∀ V:Fin n→ΧiMars, ContinuousOn (fun x=>Z n x V) (conf n))(Q:Carat)(f:YM.Test n) : MultilinearMap ℂ (fun _:Fin n=>ΧiMars) ℂ where
 toFun x:= f.applyTo (fun y=> Z n y (fun i=>(Q.G four).c (x i)))
 map_update_add' V i a b:=by
   unfold YM.Test.applyTo; rw [← integral_add (f.smearing (w _)) (f.smearing (w _))]; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_ ; simp only; rw [← mul_add]; congr 1
   let K:= (Z n x).compLinearMap (fun _=> ((Q.G four).c).toLinearMap); exact K.map_update_add ..
 map_update_smul' V i a b:=by
   unfold YM.Test.applyTo; rw[smul_eq_mul,←integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_ ; simp only
   let K:= (Z n x).compLinearMap (fun _=> ((Q.G four).c).toLinearMap); rw[show Z n x (fun j=> (Q.G four).c (Function.update V i (a • b) j))= K (Function.update V i (a • b)) from rfl,K.map_update_smul]; change f x * (a * K _) = a * (f x * K _); rw [mul_left_comm]
variable (Z:CloudsL)
-- work with tests.Roll underneath χ.
/-- Chiral and gauge witness.Its normalization read on the selected vacuum, with cutoff down the stressPrice path. Actual test F applied to PRICE slots scaled by (δˢ)^4. Cousins Vx stamped with that same map. Yields Wick's total determined by (99). -/
def ΘTyre3VU(Ca:ℕ→Carat)(Z:CloudsL):Prop:=∀ (V: Fin 3→ΧiMars)(f:YM.Test 3), tsupport f ⊆ axisRange 3 → Tendsto (fun k=> ((Ca k).u.roll f).applyTo (fun z=> Z 3 z (fun i=> ((Ca k).G four).c (V i)))) atTop (𝓝 (f.applyTo (fun z=>coupe (V 0) (Calibration.lift four (V 1)) (Calibration.lift four (V 2)) z)))
noncomputable abbrev pressκVU (s:ℕ) := u (p.dawn.i s)
noncomputable abbrev LensUVVU (s:ℕ)(x:ΧiMars):= ((pressκVU p s).G four).c x
noncomputable abbrev StretchUVVU (s:ℕ)(f:YM.Test n):=(pressκVU p s).u.roll f
noncomputable abbrev ExtUVVU (s:ℕ)(a b:Axis):= (pressκVU p s).κ^4 • p.J a b
noncomputable abbrev PriorityVU (a b:Axis):= pens (totalIx (payment Stage.All)).val a b
variable (π:ΘTyre3VU u Z)(w:∀ V:Fin 3→ΧiMars,ContinuousOn (fun x=>Z 3 x V) (conf 3))
include π w
lemma ΕΤurnVU (h:Blush S atTop u) (a b:Axis) (x y:ΧiMars) (f:YM.Test 3) (e:tsupport f ⊆ axisRange 3):
 Tendsto (fun s=> (StretchUVVU p s f).applyTo (fun z=> Z 3 z ![ExtUVVU p s a b,LensUVVU p s x,LensUVVU p s y])) atTop (𝓝 (f.applyTo (coupe (PriorityVU a b) (Calibration.lift four x) (Calibration.lift four y)))):=by
 let A:Fin 3→ΧiMars:= ![x,x,y]; let G':= audition (Calibration.lift four x) (Calibration.lift four y) f
 let K s:=(FlareΥVU Z w (u s) ((u s).u.roll f)).toLinearMap A 0 -- tune
 let g := p.dawn.i
 have hg:=p.dawn.mon.tendsto_atTop
 let T'i s k:=(u s).G four|>.c k
 have Au(s:ℕ)(j:ΧiMars): (fun i:Fin 3=> ((u s).G four).c (Function.update A 0 j i))= ![T'i s j,T'i s x,T'i s y]:=by
   funext i; fin_cases i<;>simp [A,T'i]
 have hp(k):Dips ℂ atTop (fun s=> K (g s) k) (G' k):= by
   have ht:= (π (Function.update A 0 k) f e).comp hg; refine seen.mpr ?_; simp only [Function.update_self, Function.update_of_ne (by decide : (1:Fin 3)≠0), Function.update_of_ne (by decide : (2:Fin 3)≠0)] at ht; convert ht using 1
   · ext i; rfl
   rfl
 let B s:=((pressκVU p s).G four).c.symm (ExtUVVU p s a b)
 refine Filter.Tendsto.congr ?_ (seen.mp (trav hp B _ (p.sharp h a b))) -- type check
 intro s; change (StretchUVVU p s f).applyTo (fun z=> Z 3 z (fun i=> ((u (g s)).G four).c (Function.update A 0 (B s) i)))= _; simp_rw [Au]
 rw[show T'i (g s) (B s)=ExtUVVU p s a b from ((pressκVU p s).G four).c.apply_symm_apply _]
#print axioms ΕΤurnVU
end YM.GaugeFieldConstruction.Ember.Volumetric
