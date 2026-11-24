import GaugeFieldConstruction.PewMars
import GaugeFieldConstruction.BrigandL
import GaugeFieldConstruction.DawnMatrixN
import GaugeFieldConstruction.DreamVU
/-! # Physical separation PRICE geometry common Eu & MINK. -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace Matrix
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (Z:CloudsL)(H:SurfCheckL Z)
open Stage.Count Invoice.curvΝ Metric
-- position read shape.sum.
abbrev PinsVU (a b:E4):Points 2:= WithLp.toLp 2 (![a,b])
abbrev PinVU (a:E4): Points 1:= WithLp.toLp 2 (![a])
abbrev SoloΛVU (k:Points 1)(x:ΧiMars):ℂ:= Z 1 k ![x]
abbrev NetΛVU (k:Points 2)(x y:ΧiMars):ℂ:= Z 2 k ![x,y]
abbrev DeeVK (k:Points 2)(x y:ΧiMars):ℂ:= NetΛVU Z k x y-SoloΛVU Z (PinVU (k 0)) x * SoloΛVU Z (PinVU (k 1)) y
include H
lemma precision_shiftVU(x:Points 1)(d:ΧiMars) : SoloΛVU Z x d=SoloΛVU Z (0:Points 1) d:=by
 have hp:= H.even (x 0) ![d] 0 (show _∈conf 1 from fun i j _=>Subsingleton.elim i j); rw [show NSF.Points.across (x 0) (0: Points 1)=x from ?_] at hp; exact hp
 apply PiLp.ext; intro i; fin_cases i; exact zero_add .. -- tune
lemma benefit_shiftVU(x:Points 2)(v:x∈conf 2)(t:E4)(a b:ΧiMars) : DeeVK Z (NSF.Points.across t x) a b=DeeVK Z x a b:=by
 unfold DeeVK; rw [precision_shiftVU Z H _ a, precision_shiftVU Z H _ b,precision_shiftVU Z H (PinVU (x 0)),precision_shiftVU Z H (PinVU (x 1)),NetΛVU, H.even]; exact v -- tune
omit H
noncomputable def IncomeLeftVU(k:Points 2)(y:ΧiMars) : ΧiMars→ₗ[ℂ]ℂ:= (Z 2 k).toLinearMap ![0,y] 0
lemma leftAccVU(k:Points 2)(y x:ΧiMars) : IncomeLeftVU Z k y x=NetΛVU Z k x y:=by
 rw [IncomeLeftVU,MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp [NetΛVU] -- tune
noncomputable def IncomeRightVU(k:Points 2)(x:ΧiMars):ΧiMars→ₗ[ℂ]ℂ:= (Z 2 k).toLinearMap ![x,0] 1
lemma rightAccVU(k:Points 2)(x y:ΧiMars):IncomeRightVU Z k x y=NetΛVU Z k x y:=by
 rw [IncomeRightVU,MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp [NetΛVU] -- tune
noncomputable def SoloLinVU(k:Points 1):ΧiMars→ₗ[ℂ]ℂ:=(Z 1 k).toLinearMap ![0] 0
lemma soloAccVU(k:Points 1)(x:ΧiMars):SoloLinVU Z k x=SoloΛVU Z k x:=by rw [SoloLinVU,MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i; simp -- tune
noncomputable def TierLeftVU(k:Points 2)(y:ΧiMars):ΧiMars→ₗ[ℂ]ℂ:= IncomeLeftVU Z k y - SoloΛVU Z (PinVU (k 1)) y • SoloLinVU Z (PinVU (k 0))
lemma tierLA_VU(k:Points 2)(x y:ΧiMars):DeeVK Z k x y=TierLeftVU Z k y x:=by rw [TierLeftVU,LinearMap.sub_apply,LinearMap.smul_apply,leftAccVU, soloAccVU, smul_eq_mul,mul_comm]
noncomputable def TierRightVU(k:Points 2)(x:ΧiMars):ΧiMars→ₗ[ℂ]ℂ:= IncomeRightVU Z k x - SoloΛVU Z (PinVU (k 0)) x • SoloLinVU Z (PinVU (k 1))
lemma tierRA_VU(k:Points 2)(x y:ΧiMars):DeeVK Z k x y=TierRightVU Z k x y:=by rw [TierRightVU,LinearMap.sub_apply,LinearMap.smul_apply,rightAccVU, soloAccVU, smul_eq_mul]
abbrev XPriceVU (X Y:ClanZN→ΧiMars)(k:Points 2) : SettingZN:=fun i j=> DeeVK Z k (X i) (Y j)
lemma PayTrueVU (k:Points 2)(X: ClanZN→ΧiMars)(a:Axis)(v:ClanZN→ℂ) : let u:= ∑ i,v i • X i; Formsν (XPriceVU Z (TurnupMars a∘ X) X k) v= DeeVK Z k (TurnupMars a u) u:=by
 dsimp only
 rw [tierLA_VU]; unfold TurnupMars; simp only [map_sum,map_smul,map_smulₛₗ,smul_eq_mul]; unfold Formsν; apply sum_congr rfl; intro i h
 rw [←tierLA_VU,tierRA_VU,map_sum]; simp_rw[map_smul,smul_eq_mul, ←tierRA_VU]; rw [mul_sum]; apply sum_congr rfl; intro j h; rw [←mul_assoc]; rfl
variable {A:Axis}{p:Ticket u C}
variable (h: SurfCheckL.boisterL p Z)
include h
open FirstPackMars
lemma TimeShiftVU (x:Points 1)(d:ΧiMars)(s:SO): SoloΛVU Z (motionMoonMars s x) (compassPiMars p s d)=SoloΛVU Z x d:=by
 have hp:=h 1 ![d] x (fun _ _ _=> Subsingleton.elim ..) s; rw [show compassPiMars p s ∘ ![d] = ![compassPiMars p s d] from (by ext1 i; fin_cases i; rfl)] at hp; exact hp
lemma TimeProfitVU (x:Points 2)(q:x∈conf 2)(d f:ΧiMars)(s:SO): DeeVK Z (motionMoonMars s x) (compassPiMars p s d) (compassPiMars p s f)=DeeVK Z x d f:=by
 let T:=compassPiMars p s
 have hp:=h 2 ![d,f] x q s; rw [show compassPiMars p s ∘ ![d,f]=![T d,T f] from (by ext1 i; fin_cases i <;> rfl)] at hp; unfold DeeVK; rw[show NetΛVU Z _ _ _=_ from hp]; rw[show PinVU (motionMoonMars s x 0)=motionMoonMars s (PinVU (x 0)) from ?_,show PinVU (motionMoonMars s x 1)=motionMoonMars s (PinVU (x 1)) from ?_,TimeShiftVU _ h,TimeShiftVU _ h] -- tune
 all_goals apply PiLp.ext; intro i; fin_cases i; rfl
include H
omit h
lemma ContinuousΑVU (X Y:ClanZN→ΧiMars): ContinuousOn (XPriceVU Z X Y) (conf 2):=by
 intro x v; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
 let A:=X i; let B:=Y j
 have hp (k:Points 2):XPriceVU Z X Y k i j= Z _ k ![A,B]-SoloΛVU Z 0 A*SoloΛVU Z 0 B:=by
   change NetΛVU Z k A B-_=_; rw [precision_shiftVU Z H _ (X i),precision_shiftVU Z H _ (Y j)] 
 simp_rw [show XPriceVU Z X Y x i j=_ from hp x]; exact ((H.sm ![A,B]).continuousOn x v |>.sub (continuousWithinAt_const (b:=SoloΛVU Z 0 A*SoloΛVU Z 0 B))).tendsto.congr (fun k=> (hp k).symm)
#print axioms PayTrueVU
end YM.GaugeFieldConstruction.Ember.Volumetric
end
