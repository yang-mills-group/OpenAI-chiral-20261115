import GaugeFieldConstruction.HewlettQc
import GaugeFieldConstruction.GarukaQc
/-!
# Linear allocation on actuality of thresholds
-/
set_option autoImplicit false
set_option synthInstance.maxSize 9100
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S) (v:UpAngleQc Y) (Z:∀ v:UV five,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0)
variable (N:NickleQc)(D:ℕ→ℝ)(H:Floor→ℕ→ℝ)(Q:ℕ→ℝ)
-- θ uses X Four and hinge d+1; Φ means d. expose statuses.Annulus. Orbit durations. Unit d through lift.
local notation "l5"=> Calibration.lift Floor.five
local notation "l4"=> Calibration.lift Floor.four
local notation "ℓ"=> Calibration.lift
structure CornetQc :Prop where
   dp:Tendsto (fun i=> (N.e i)⁻¹*D i) atTop (𝓝 0)
   m3:Tendsto (fun i=> (N.e i)^3*Q i) atTop (𝓝 0)
   m4 d:Tendsto (fun i=> (N.e i)^4*H d i) atTop (𝓝 0)
   T4 (X:UV four): FundsQc (Calibration.lift five) N D Y (Empire.one five) (Calibration.lift _ X)
   K1 (X J:UV four): FundsQc (Calibration.lift five) N Q Y (Calibration.lift _ X) (Calibration.lift _ J)
   K2 (d:Floor)(X:UV d)(J:UV four): FundsQc (Calibration.lift d) N (H d) Y (Calibration.lift d X) (Calibration.lift _ J)
-- issue: local notation H param clashes changed.
variable {H Q D}(p:CornetQc Y N D H Q)
lemma IdentQc (x:l): Calibration.lift five x=x:=rfl
include p Z v
lemma ShedItQc : ∃ P:Axis→Across, Nonempty (Sheds S P):=by
 choose T h using fun i:Axis=>fun x:UV four=> RampQc Y N D l5 (l4 x) Z (l4 x) (Calibration.inject five) rfl (BootTagQc Y l5 _ _ D N (p.T4 x)) p.dp i
 have hx(i x):PierQc (S:=S) i (l4 x) (T i x):= by simpa only [IdentQc] using h i x
 let P(i:Axis):Across:={
    toFun:=T i
    map_add' x y:= pierPaidQc Z _ _ _ i (hx i _) (by intro n a b; rw [map_add,map_add,map_add,map_add,hx i x,hx i y])
    map_smul' a x:= pierPaidQc Z _ _ _ i (hx i _) (by intro n y b; change S.spot y b (a • T i x)=_; rw[map_smul,map_smul,map_smul,map_smul,hx i x]) }
 have e(i x):PierQc (S:=S) i (l4 x) (P i x):= hx i x
 refine ⟨P,⟨{ money:=fun i b=>e i b,tax:=?_,stripe:=?_,realD:=?_ }⟩⟩
 · intro s i x; let H0:= runPierQc Y s v i (l4 x) _ (e i x); rw[← Loft.spin_lift] at H0; rw[← pierPaidQc Z _ _ _ _ H0 (e (s.perm i) (spinFrame four s x)),pay_pay]
 · intro g i x; apply pierPaidQc Z (ℓ four (flavors four g x)) _ _ i _ (e _ _); rw [ColorLiftQc]; exact DyePierQc Y g v i _ _ (e _ _)
 intro i x; apply pierPaidQc Z (ℓ four (shade four x)) _ _ i _ (e _ _); rw [shadeLiftQc]; exact GrayPierQc Y v i _ _ (e _ _)
omit p Z v
-- linear reach assembly.n primera
noncomputable def JobPqc (x:InkQc)(K:Bills): SymT→ₗ[ℂ] UV five→ₗ[ℂ] ℂ:= LinearMap.mk₂ ℂ (fun a y=>HarvestQc S y (prints a) K x) (by -- arguments order tune
 intro u v w; unfold HarvestQc delta; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw[←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; unfold armed prints pens; rw [show (u+v).val _= u.val (ordered i j)+ v.val (ordered i j) from rfl,map_add,map_add,LinearMap.add_apply]) (by
 intro a u v; unfold HarvestQc delta; rw[Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw[Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; unfold armed prints pens; rw [show (a • u).val _= a • u.val (ordered i j) from rfl,map_smul,map_smul,LinearMap.smul_apply]) (by
 intro a u v; unfold HarvestQc delta; rw[← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; let T:=S.spot (Fathom.add (prints a i j) (Fathom.add 0 x.x)) (Fin.succ 0); have h b:S.armed (prints a) (Fathom.add b x.x) i j=T b:=by
    unfold T armed; rw[spot_cost,tagged_cost]; simp only[Fathom.add,← Fin.cons_update, Fin.update_cons_zero]
 rw [h,h,h,map_add,LinearMap.add_apply]) (by
 intro a u v; unfold HarvestQc delta; rw[Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; let T:= S.spot (Fathom.add (prints u i j) (Fathom.add 0 x.x)) (Fin.succ 0); have h b:S.armed (prints u) (Fathom.add b x.x) i j=T b:=by
    unfold T armed; rw[spot_cost,tagged_cost]; simp only[Fathom.add,← Fin.cons_update, Fin.update_cons_zero]
 rw [h,h,map_smul,LinearMap.smul_apply])
lemma JetCostQc (x:InkQc)(K:Bills)(a:SymT)(i j:l)(h:Reaches S (prints a) K i j): S.tagged x.x j x.f=JobPqc (S:=S) x K a i:=by
 let v:=Fathom.add (0:l) x.x; have t:=h (x.n+1) v 0 x.f x.b x.h; unfold v at t; rw[show update (Fathom.add (0:l) x.x) 0 i=Fathom.add i x.x from Fin.update_cons_zero ..] at t; exact t
lemma TickAnglePlusQc (x:InkQc)(Ω Θ: Ortho.Skew)(a:SymT)(b:l): JobPqc (S:=S) x (rpm (Ω+Θ)) a b= JobPqc (S:=S) x (rpm Ω) a b+JobPqc (S:=S) x (rpm Θ) a b:=by
 let V(Ω:Ortho.Skew):= HarvestQc S b (prints a) (rpm Ω) x; change V _=V _+V _; unfold V HarvestQc delta; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw[←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; rw[←map_add]; congr 1; ext1 y; change _= testcut _ _ _ _ i j y+ testcut _ _ _ _ i j y; simp_rw[testcut_v,rpm,angle]; simp only[M4.at_coord,Submodule.coe_add,Matrix.add_apply,add_mul,Finset.sum_add_distrib,mul_add,add_smul]
lemma TickAngleScaleQc (x:InkQc)(c:ℝ)(Ω:Ortho.Skew)(a: SymT)(b:l): JobPqc (S:=S) x (rpm (c • Ω)) a b= (c:ℂ) • JobPqc (S:=S) x (rpm Ω) a b:=by
 let V(Ω:Ortho.Skew):= HarvestQc S b (prints a) (rpm Ω) x; change V _= _ • V _; unfold V HarvestQc delta; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw[Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; rw [←map_smul]; congr 1; ext1 y; change _=(c:ℂ) • testcut _ _ _ _ i j y; simp_rw[testcut_v,rpm,angle,M4.at_coord,Submodule.coe_smul]
 simp only[Matrix.smul_apply, smul_eq_mul,mul_assoc, ←Finset.mul_sum, Complex.real_smul]; push_cast; ring
#print axioms ShedItQc
end YM.GaugeFieldConstruction.Ember.Hulse
