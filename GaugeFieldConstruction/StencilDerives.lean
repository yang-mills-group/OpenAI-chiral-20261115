import GaugeFieldConstruction.StencilSlotsStress
import GaugeFieldConstruction.RegaliaRT
/-!
# A creator on derivative fields (no assumption derivative is already one of the input labels)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 420000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric.FirstPackMars
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n:ℕ} {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C){A:CloudsL}(H:SurfCheckL A)
variable {W:NSF.Boundary.Surface (SurfRimL A)}{X:NSF.Boundary.Wightman (SurfRimL A)} (k:Fin n)
open StressLaw

namespace StLaw
local notation "d_" i:max=> DmoveRT i
local notation "δ_" z:max i:max=>DriftΛL (NSF.Points.direction z i)
local notation "μ"=> H.TinCanL
local notation "Tν"=> CoffΜΛ H p
local notation "Φ"=> X.operators.field
local notation "op"=>X.operators.domain →ₗ[ℂ] X.operators.domain
variable (F:Axis→ΧiMars)(c:Axis→ℂ)(V:Fin n→ΧiMars)
local notation "v" j:max=> Function.update V k (F j)
local notation "α" j:max => μ ∘ Function.update V k (F j)
local notation "Θ" b:max i:max=> addXRT k (H.TinCanL ∘ V) ( (CoffΜΛ H p) i b)
open YM.Boundary (Joint.materialize)
noncomputable def derivativeCreator (X:NSF.Boundary.Wightman (SurfRimL A))(F:Axis→ΧiMars)(c:Axis→ℂ): Test4→ₗ[ℂ] X.operators.domain →ₗ[ℂ] X.operators.domain:=∑ i:Axis,c i • X.operators.field (H.TinCanL (F i)) ∘ₗ (DmoveRT i).toLinearMap -- precedence infix ∘
lemma derivA (f:Test4): derivativeCreator H X F c f=∑ i:Axis,c i • (Φ (μ (F i)) ((d_ i) f)):= by unfold derivativeCreator; rw [LinearMap.sum_apply]; rfl
noncomputable abbrev shiftWard (j:Axis):Distn (Points n):=∑ i:Axis,c i• (RotateCostΛL H W (Function.update V k (F i)) k j ∘L DriftΛL (NSF.Points.direction k i))
noncomputable abbrev curtainWard (a b:Axis): Distn (Points (n+1)):=∑ i:Axis,c i•(CommΘRt p H (Y:=W) (Function.update V k (F i)) k a b ∘L DriftΛL (NSF.Points.direction k.succ i))

variable (e:LocalWardRT p H W X)
include e
lemma derive_wage (a:Axis): wageUnit k (shiftWard (W:=W) H k F c V a) (curtainWard (W:=W) p H k F c V a) (-(ΛSignXRt a)):=by
 have h(j:Axis):= wage_derivation k (RotateCostΛL H W (v j) k a) (CommΘRt p H (Y:=W) (v j) k a) (-(ΛSignXRt a)) (fun f b h q=>by rw [e.endorses n (v j) k a b h q,WorkWatchRT]; rfl) j
 intro f b g eq
 let M:=χTestRT k; unfold shiftWard curtainWard; simp_rw [_root_.sum_apply,smul_apply]; rw[Finset.sum_comm,Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [← Finset.smul_sum,smul_comm]; exact congrArg (c j • ·) (h j f b g eq) -- ℂ as Id
local notation "CR"=> derivativeCreator H X F c
noncomputable abbrev stressReceipt (a b:Axis)(f:Fin (n+1)→Test4)(x:Module.End ℂ X.operators.domain): Fin (n+1)→Module.End ℂ X.operators.domain:= Function.update (wage X (Θ a b) f) k.succ x
local notation "Tξ" => stressReceipt p H (X:=X) k V
lemma stress_comm (a b:Axis)(f:Fin (n+1)→ Test4): (curtainWard (W:=W) p H k F c V a b) (Joint.materialize (n+1) f)=
    operatorPays X (Tξ a b f (CR (f k.succ))) - operatorPays X (Tξ a b f (CR (f k.succ)) ∘ (τNearRT k).s) :=by
 let J:=Joint.materialize (n+1); let f₁(i:Axis):=Function.update f k.succ ((d_ i) (f k.succ)); let B(i:Axis):=Φ (μ (F i)) ((d_ i) (f k.succ)); let Xp(i:Axis):=v i
 let Z:= DmoveRT; let K:= wage X (Θ a b) f; let r(i:Axis):= CommΘRt p H (Y:=W) (Xp i) k a b; let H':=(τNearRT k).s
 let G(D:Equiv.Perm (Fin (n+1))) :=changeBill k.succ X D K; let t: Equiv.Perm (Fin (n+1)) := Equiv.refl _
 have hp(i: Axis): r i (DriftΛL (NSF.Points.direction k.succ i) (J f))=G t (B i)-G H' (B i):=by
    let P:= addXRT k (μ ∘ Xp i) (Tν b a)
    have hP:P k.succ=μ (F i):=by simp [P,insertSelfRT,Xp]
    have hx(j:Fin (n+1))(e:j≠k.succ): P j= (Θ a b) j:=by
       unfold P; cases j using Fin.succAboveCases k.castSucc with
       | x=> simp [addXRT]
       | p j=> simp only [addXRT,Fin.insertNth_apply_succAbove,Function.comp_apply,Xp]; rw [Function.update_of_ne]; rintro rfl; exact e (tNextRT ..)
    let Rι:= Xp i; let Q:= WordνRt p H Rι k a b (f₁ i)
    have he(D:Equiv.Perm (Fin (n+1))) : CostXtRt X (List.ofFn (Q ∘ D))= (G D) (B i):=by
       unfold CostXtRt; rw [employed]; change operatorPays X (wage X P (Function.update f k.succ ((d_ i) (f k.succ))) ∘ D)=_; unfold B; rw [←hP]; apply wage_advance; intro j y; unfold K wage; rw [hx _ y]
    unfold J; rw [spotTestΛL]; exact Eq.trans ((e.knows n (Xp i) k a b (r i)).2 rfl (f₁ i)) (congrArg₂ (·-·) (he t) (he H')) -- fix binder
 unfold curtainWard; rw [_root_.sum_apply]; simp_rw [smul_apply]; change ∑ i:Axis,c i• r i (DriftΛL (NSF.Points.direction k.succ i) (J f))= (G t) (CR (f k.succ)) - G H' _; simp_rw [hp,smul_sub]; rw [sum_sub_distrib, derivA,map_sum,map_sum]; simp_rw [map_smul]; rfl
omit e
variable {R:(SurfRimL A).Rotation}{s:(SurfRimL A).RealSpin}{B:CloudsL}
variable (Q:X.Realizes (W:=W) R s)
include Q
lemma weight_field (j:Axis)(f: Test4)(x:X.operators.domain) : HasDerivAt (fun t:ℝ=> (DragΛL X Q (Mink.Poincare.translation (t • basis j)) (CR f) x).val) ((CR (-(ΦshiftΛ (basis j) f)) x).val) 0 := by
 let z:= -(d_ j) f; let H'(t:ℝ):=DragΛL X Q (Mink.Poincare.translation (t • basis j)); let V(i:Axis)(f:Test4):= (Φ (μ (F i)) ((d_ i) f)); let r(t:ℝ)(i:Axis): X.operators.H:= c i • ((H' t) (V i f) x).val; have h(i:Axis): HasDerivAt (fun t:ℝ=> r t i) (c i • (V i z x).val) 0:= by
    unfold V z; rw [map_neg,commute_shifts]; unfold r; exact (LeafActΛL j ((d_ i) f) X Q (μ (F i)) x).const_smul (c i) -- lemma signature
 have hX : ∀ (f:Axis→Module.End ℂ X.operators.domain), ((∑ i:Axis,c i • f i) x).val = ∑ i:Axis,c i•(f i x).val:=by intro f; rw [LinearMap.sum_apply,Submodule.coe_sum]; rfl
 simp_rw [derivA,drag_price,hX]; exact HasDerivAt.sum (u:=Finset.univ) (fun i _=>h i)
lemma field_receipt (j:Axis)(f:Fin n→Test4) : (shiftWard (W:=W) H k F c V j) (Joint.materialize n f)= operatorPays X (Function.update (wage X (μ ∘ V) f) k (CR (-(d_ j) (f k)))) := by
 let J:=Joint.materialize n; let Qp:= Equiv.refl (Fin n); let K:= wage X (μ ∘ V) f; let B(i:Axis):= Φ (μ (F i)) ((d_ i) (-(d_ j) (f k))); let Xp(i:Axis):= v i
 let w:= changeBill k X Qp K; let R(i:Axis):= RotateCostΛL H W (Xp i) k j
 have hp(i:Axis): R i (DriftΛL (NSF.Points.direction k i) (J f))= w (B i):=by
    let g:= Function.update f k ((d_ i) (f k)); let D:= Function.update g k (-(d_ j) (g k)); let d:= -(d_ j) ((d_ i) (f k)); let I(t): NSF.Boundary.Letter (SurfRimL A) := (μ ((Xp i) t),D t)
    have hd : Function.update g k (-(d_ j) (g k))=Function.update f k d:=by funext a; by_cases p:a=k <;> simp [p,g,d]
    have hv : D= Function.update f k d:=hd; unfold J; rw [spotTestΛL]; change - (W.W n (μ ∘ Xp i) ((DriftΛL (NSF.Points.direction k j)) (J g)))=_; unfold J; rw [← LeafWHereΛL, ← Q.meets]; change inner ℂ X.operators.vacuum (X.operators.vector (List.ofFn (I ∘ Qp)))= _; rw [employed]; change operatorPays X (wage X (μ ∘ Xp i) D ∘ Qp)=_; unfold B; rw [hv,map_neg, commute_shifts]; change operatorPays X _= w (Φ (μ (F i)) d); rw [← show (μ ∘ Xp i) k= μ (F i) from by simp [Xp]]; apply wage_advance; intro i h; unfold wage K Xp; simp[h]; rfl -- tune
 unfold shiftWard; rw [_root_.sum_apply]; simp_rw [smul_apply]; change ∑ i:Axis,c i• R i (DriftΛL (NSF.Points.direction k i) (J f))= w (CR _); simp_rw[hp]; rw [derivA,map_sum]; simp_rw[map_smul]; rfl
#print axioms derive_wage
#print axioms field_receipt
#print axioms weight_field
#print axioms stress_comm
end StLaw
end YM.GaugeFieldConstruction.Ember.Volumetric.FirstPackMars
end
