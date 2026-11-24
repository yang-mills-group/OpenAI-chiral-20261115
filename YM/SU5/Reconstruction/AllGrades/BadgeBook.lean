import YM.SU5.Reconstruction.AllGrades.Sparks
import YM.SU5.Reconstruction.AllGrades.Caption
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open OS.Semigroup
open SelectionAnalysis LightBudget
open Nymph Chambers ConePrice.Session Roy
local notation "S" b:max=> studio (tent Y H) a 0 b
local notation "A₀"=> regime Y H V G D a b P
variable (A:Impetus Y H V G D a b P)
local notation "R"=> wheelTimes Y H V G D a b P A
local notation "Dt"=> (dainty Λ)
local notation "Gt"=> marks Dt
local notation "S₀"=> Coupon a Gt
-- pose chronology support for Momentum fees.Strong form.Γ flag.
variable (x y:studio (tent Y H) a 0 b) (d: Lattice.Cover)
noncomputable def functor (t:List (Trans a)): Sc →ₗ[ℂ] Sc:= t.foldr (fun i m => (turnLane Y H a b i (d i.val)).comp m) (LinearMap.id)
local notation "L₁"=> functor Y H a b d
lemma garage(t:List (Trans a))(v:S₀)(p:∀ j, notch Dt s (d j) = v.stamp j):
    (A₀).raw t (fun i=> v.stamp i.val) ((Bp s) x)=(Bp s) (L₁ t x):=by
    induction t with
    | nil=>rfl
    | cons i l ih=> unfold functor; rw [Germ.Alliance.raw_step, ContinuousLinearMap.comp_apply, ih,← p i.val, regime_value, atLane]; rfl
local notation "Sl"=> ticket Y H G s
local notation "Wq" n:max=> walkC Y H a b n
noncomputable def vectorPose(d:Cover): Sc →ₗ[ℂ] Sc := (Wq (d a).toNat).comp (functor Y H a b d (look a))
local notation "Vq"=> vectorPose Y H a b
lemma lore_wise (t:S₀)(p:∀ j, notch Dt s (d j) = t.stamp j):
    Lore (R) (A₀) ((Bp s) x) t= Ω s (poleForm (tent Y H) a 0 b x.val (Vq d x).val):=by
    let n:=(d a).toNat; let d':ℝ≥0:= whenly Dt s n
    have h:0 ≤ d a:= (bell_le Dt s 0 (d a)).1 (by rw [show bell Dt s (d a)=_ from congrArg Subtype.val (p a), show bell Dt s 0=0 from by simp [bell]]; exact t.ground)
    have hn : (n:ℤ)=d a:= Int.toNat_of_nonneg h
    have ht: t.dt=d':=by unfold Coupon.dt d'; rw [← p,←hn, show (notch Dt s (n:ℤ):ℝ)=(whenly Dt s n:ℝ) from natural_time ..,Real.toNNReal_coe]
    change inner ℂ _ (((R).E t.dt) ((A₀).raw (look a) (fun i=> t.stamp i.val) ((Bp s) x)))= _; rw [ht,garage Y H V G D a b s P x d (look a) t p]; unfold d'; rw [ages_pose, measures_here]; rfl
lemma pay_horizon(v:S₀):∀ᶠ s:ℕ in atTop, ∃ d:Cover,∀ x:Axis, notch (dainty Λ) s (d x)=v.stamp x:=by
 have hx:∀ᶠ s:ℕ in atTop, ∀ x:Axis, ∃ n:ℤ, notch (dainty Λ) s n=v.stamp x:= Filter.eventually_all.mpr fun x=>eventually_toned _
 filter_upwards [hx] with s p; exact Classical.axiomOfChoice p
-- now multiplication & sign:
noncomputable def multiplyG(x y:studio (tent Y H) a 0 b): S false :=
 ⟨x.val*y.val,by
    obtain ⟨S',v,h⟩:=atSouth Y H a b x; obtain ⟨U,w,p⟩:=atSouth Y H a b y; have ht:= InTest.mul (v.mono (Finset.subset_union_left (s₂:=U))) (w.mono Finset.subset_union_right); rw [Bool.xor_self] at ht; exact ⟨S'∪U,ht,fun i t=> (Finset.mem_union.mp t).elim (h i) (p i)⟩⟩
local notation "multiC"=> multiplyG Y H a b
lemma cart_mulG (k:Axis)(t:ℤ)(p:a=k→0 ≤ t): multiC (cart Y H a b k t p x) (cart Y H a b k t p y)= cart Y H a false k t p (multiC x y) := Subtype.ext (chime_product K k t).symm
lemma funcOperate (t:List (Trans a)): functor Y H a false d t (multiC x y)= multiC (L₁ t x) (L₁ t y) :=by
    induction t with
    | nil=>rfl
    | cons i l ih=> change (turnLane Y H a false i (d i.val)) (functor Y H a false d l (multiC x y))= multiC (turnLane Y H a b i (d i.val) (L₁ l x)) (turnLane Y H a b i (d i.val) (L₁ l y)); rw [ih]; exact (cart_mulG Y H a b ..).symm
lemma pose_mulG: vectorPose Y H a false d (multiC x y)= multiC (Vq d x) (Vq d y):=by unfold vectorPose; simp_rw [LinearMap.comp_apply,funcOperate]; exact (cart_mulG Y H a b ..).symm
variable (j:Trans a)(r:ℤ)
local notation "Τ"=> turnLane Y H a b
lemma funcComm (t:List (Trans a)): L₁ t (Τ j r x) = Τ j r (L₁ t x):= by
 induction t with
 | nil=>rfl
 | cons i l h=> change Τ i (d i.val) (L₁ l (Τ j r x))=Τ j r (Τ i (d i.val) (L₁ l x)); rw [h]; unfold turnLane; rw [cart_comm]
lemma poseComm : Vq d (Τ j r x)=Τ j r (Vq d x):=by unfold vectorPose; simp_rw [LinearMap.comp_apply,funcComm]; change cart _ _ _ _ _ _ _ (Τ j r _) =Τ j r (cart _ _ _ _ _ _ _ _); unfold turnLane; rw [cart_comm] -- tune cart change
lemma oddPower : poleForm (tent Y H) a 0 false (multiC x (Τ j r x)).val (multiC y (Τ j r y)).val= (W x.val y.val) * (C₀ j.val (2*r) (W x.val y.val)) := by
 -- works both grades: chord square is -1 for Odd, accounts ONE crossing of two ODD words
 let X:= Τ j r x; let Y':= Τ j r y
 let p:=(atSouth Y H a b x).choose_spec.1; let p':=(atSouth Y H a b X).choose_spec.1; let v:=(atSouth Y H a b y).choose_spec.1
 unfold poleForm; change Reflect.chord false • (mirror K a 0 (x.val*X.val)*(y.val*Y'.val))=(Reflect.chord _ • (mirror _ a 0 x.val*y.val))*_
 rw [mirror_times,chime_scale,chime_product,straddle j.val a j.property (2*r) 0 p]
 simp only [show Reflect.chord false=1 from rfl,one_smul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul]
 change (mirror K a 0 x.val*mirror K a 0 X.val)*(y.val*Y'.val)=(Reflect.chord b * Reflect.chord b) • ((mirror K a 0 x.val*y.val)*(mirror K a 0 X.val*Y'.val))
 let e:=axial _ a 0 p'; cases b
 · have k:= even_tests K (aux_test e) (aux_test v); change _=( (1:ℂ)*1) • _; rw [one_mul,one_smul]; calc
      _= Θ a 0 x.val * ((Θ a 0 X.val*y.val)*Y'.val):=by simp only [mul_assoc]
      _=_:=by rw [k]; simp only [mul_assoc]
 · have k: Θ a 0 X.val*y.val= -(y.val*Θ a 0 X.val) := by
      funext m k; let i:=Θ a 0 X.val
      have he:= ((e.support m).mono (Finset.subset_univ _)).allV k; have hg:= ((v.support m).mono (Finset.subset_univ _)).allV k; change i m k * _= -(_* i m k); simpa [Fock.Sector.grainB, i] using he.sign_com hg
   change _ = (Complex.I*Complex.I) • _; calc
      _= Θ a 0 x.val * ((Θ a 0 X.val*y.val)*Y'.val):= by simp only [mul_assoc]
      _=_:=by rw [k]; simp only [Complex.I_mul_I,neg_one_smul,neg_mul,mul_neg,mul_assoc]

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.pose_mulG
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.poseComm
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.oddPower
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.lore_wise
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.pay_horizon
