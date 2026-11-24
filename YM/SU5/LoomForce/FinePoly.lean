import YM.SU5.LoomForce.FaceReflect
import YM.SU5.LoomForce.Meter
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Buffered Pannier.Chancel.Rous Next.Rank Spindle
variable (B:ℕ) (h: 2*(B+1)<(More N).val) (x:Site N)
local notation "I"=> Sheds B
local notation "A"=> FrameA B
local notation "Ξ"=> node x
local notation "J"=>install B Ξ ∘L collectF B Ξ h
local notation "R"=> Turn B

def snapFace (x:FrameA B)(i:Sheds B):ℝ:= x i.1 i.2
lemma snapAll (X:A): ∑ i:I,snapFace B X i • Stern i=X:=by
 rw [Fintype.sum_prod_type]; funext i; apply PiLp.ext; intro j; simp [snapFace,Stern,Finset.sum_apply,Pi.single_apply] -- tune
variable (E:Pattern P T r d a v) (k:ℕ)
def coins (i j:Sheds B) := stepValue B (node x) h (untouched (E.A x) k) i j
-- sym average since Ward quadratic gauge. Using star for physical reflection and later estimator
noncomputable def cashY (i j:Sheds B) := (coins B h x E k i j+coins B h x E k j i) /2
local notation "c"=> cashY B h x E k
lemma cashYaw(i j:Sheds B): c i j=c j i:=by unfold cashY; rw [add_comm (coins ..)]

def fineY (U : Sheds B→ℝ): ℂ:= ∑ u:Sheds B,∑ v:Sheds B,cashY B h x E k u v*(U u:ℝ)*(U v:ℝ)

lemma polynomial (X:FrameA B): lapAsset x k B h E X=fineY B h x E k (snapFace B X):= by
 let V:=snapFace B X; let t(i:I):= J (Stern i); let Z:=taxpayer (k:=k) x E
 let M:= J X; let U:=coins B h x E k
 have ht:M=∑ i:I,V i • t i:=by rw [←Finset.sum_congr rfl (show ∀ i:I,i∈univ→ J (V i • Stern i)=V i • t i from fun i _=>map_smul ..),← map_sum]; exact congrArg (fun P:A=> J P) (snapAll B X).symm
 have hf: Z M M=∑ i:I,∑ j:I,(U i j)*(V i:ℝ)*(V j:ℝ):= by
    rw [ht,map_sum Z,_root_.sum_apply]; refine sum_congr rfl fun i _=>?_ ; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul Z]; change (V j) • (V i) • (U i j)= _; simp [Complex.real_smul]; ring
 let b(i j:I):=U i j * (V i:ℝ)*(V j:ℝ); let Q(i j:I):=U j i * (V i:ℝ)*(V j:ℝ)
 unfold fineY; change Z M M= _; rw [hf]
 have he(i j:I):c i j*(snapFace B X i:ℝ)*(snapFace B X j:ℝ)=(b i j+Q i j)/2:=by unfold cashY b Q V U; ring
 simp_rw [he]; rw [show Q=fun i j=> b j i from funext₂ (fun i j=>by unfold Q b; ring)]
 simp_rw [←sum_div,sum_add_distrib]; rw [sum_comm (f:=fun i j:I=> b j i)] -- maybe syntax
 change _=_; ring

lemma charge_lease : ∑ i:I,∑ j:I, ‖c i j‖ ≤ charges B Ξ h (untouched (E.A x) k):= by
 let f(i j:I):= ‖coins B h x E k i j‖; let V:=∑ i:I,∑ j:I,f i j; change _ ≤ V
 have he(i j:I): ‖c i j‖ ≤ (f i j+f j i)/2:=by unfold cashY; rw [norm_div,Complex.norm_ofNat]; exact div_le_div_of_nonneg_right (norm_add_le ..) (by norm_num)
 refine le_trans (sum_le_sum (fun i _=> sum_le_sum (fun j _=> he i j))) (Eq.le ?_); simp_rw [←sum_div,sum_add_distrib]; rw [sum_comm (f:=fun i j:I=> f j i)]; change (V+V)/2=V; ring

open Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Regis.Wake (Paint)

private lemma meterSum {β γ:Type*}[Fintype β]{K:ℕ}(L:Finset γ)(g: γ→ (β→ℝ)→ℂ)(C:γ→ℝ)(v:∀ i, Paint (g i) K (C i)) : Paint (fun X=>∑ i∈L,g i X) K (∑ i∈L,C i):=by
 induction L using Finset.induction_on with | empty=>simpa using meterConst (α:=β) 0 K| insert i L p H=>simpa only [sum_insert p] using meterPlus (v i) H -- syntax

lemma paintReap {v:ℝ}(T: charges B Ξ h (untouched (E.A x) k) ≤ v) : Paint (fineY B h x E k) 2 (2*v):= by
 let Q:= ∑ i:I,∑ j:I, ‖c i j‖
 let A':=fun i j (U:I→ℝ)=> c i j *((U i:ℝ)*(U j:ℂ))
 have ha : fineY B h x E k=fun U=>∑ i:I,∑ j:I,A' i j U := by funext x; unfold fineY A'; simp_rw [mul_assoc]
 have hv :∑ i:I,∑ j:I,‖c i j‖ ≤v:=(charge_lease B h x E k).trans T
 rw [ha]
 apply meterInc (e:=2) (d:=2) (C:=2*v) (B:=∑ i:I,∑ j:I,‖c i j‖*(1*1+1*1)) ?_ le_rfl ?_
 · exact meterSum _ _ _ fun i=> meterSum _ (A' i) _ fun j=> meterScale (c i j) (meterMul (meterCoordinate i) (meterCoordinate j)) -- wrong notation
 norm_num [←sum_mul]; -- inspect
 linarith only [hv]

local notation "f"=>fineY B h x E k

abbrev Panels (B:ℕ):= Bool × Sheds B
local notation "ΠQ"=> Panels B → ℝ
-- hurricane `s`, literal true is reflection channel. Poses on S electrodes.
noncomputable abbrev peeler (B:ℕ)(b:Bool)(X:Panels B→ℝ): Sheds B→ℝ := fun x=> if b then realDir x.1.val.2*X (b,x) else X (b,x)
noncomputable abbrev ζPay (b:Bool)(k:ℂ) := if b then star k else k
noncomputable def polynomialPad (w:ℝ)(b:Bool)(X:ΠQ) := (w:ℂ)* ζPay b (f (peeler B b X))
-- lipschitz and scale.
lemma peeler_diff (b:Bool)(X Y:ΠQ): peeler B b (X-Y)= peeler B b X-peeler B b Y:=by
 cases b; rfl
 funext i; simp [peeler,mul_sub]
lemma peeler_le (b:Bool)(X:ΠQ): ‖peeler B b X‖≤ ‖X‖:= by
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; cases b
 · exact norm_le_pi_norm X (false,i)
 change ‖realDir _ * _‖ ≤ _; unfold realDir; split <;> simp only [neg_mul,one_mul,norm_neg] <;> exact norm_le_pi_norm X (true,i)

lemma enforce (w D:ℝ)(d:0≤w)(b:Bool)(T: charges B Ξ h (untouched (E.A x) k) ≤ D) :
    Paint (polynomialPad B h x E k w b) 2 (w*(2*D)):=by
 have hp:= paintReap B h x E k T
 have hv(z:ℂ):‖ζPay b z‖=‖z‖:=by cases b; rfl; change ‖star z‖=‖z‖; exact norm_star _
 have H0:=hp.nonneg
 have hm: Paint (fun X=>ζPay b (f (peeler B b X))) 2 (2*D):= {
    bright:= by
      have he:ContDiff ℝ 1 (f ∘ peeler B b):=hp.bright.comp (contDiff_pi.mpr (fun i=> by cases b <;> unfold peeler <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> fun_prop))
      cases b; exact he; exact ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff).comp he
    worth:=fun K p X g=> (hv _).le.trans (hp.worth K p _ ((peeler_le _ _ _).trans g))
    price:=fun K p' X Y g k'=> by
      have hx (v w):ζPay b v-ζPay b w=ζPay b (v-w):=by cases b; exact rfl; exact (star_sub v w).symm
      simp_rw [hx,hv]; apply (hp.price K p' _ _ ((peeler_le _ _ _).trans g) ((peeler_le _ _ _).trans k')).trans; rw [←peeler_diff]; gcongr; apply peeler_le }
 let u:= meterScale (w:ℂ) hm; rw [Complex.norm_real,Real.norm_of_nonneg d] at u; exact u
lemma evaluator_roll (ρ:ℝ)(X:I→ℝ): f (ρ • X)=(ρ:ℂ)^2 * f X:=by
 unfold fineY; simp_rw [mul_sum, Pi.smul_apply, smul_eq_mul,Complex.ofReal_mul]; refine sum_congr rfl fun i _=>sum_congr rfl (fun j _=>?_); ring
#print axioms enforce
end YM.CF.LitCurrent.Surplus
