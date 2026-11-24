import GaugeFieldConstruction.BrigandL
import GaugeFieldConstruction.PewMars
import GaugeFieldConstruction.NereidΛL
/-!
# Twice flipped parity for a true spatial J sign
- preserves real (ordinary) time order exactly; flips two spatial axes including the chosen mu.
- sends the entire staggered product domain of symmetric operators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open Mink FirstPackMars NSF.Boundary
variable {n m:ℕ} {Q: City} {P:Axis→Across} {L:Sheds Q P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Z:CloudsL) (F:ΧiMars) (j k b:Axis)
local notation "s" x:max => Signed.mirror x
abbrev flips (a j:Axis):ℝ:=if a=j then -1 else 1
abbrev bothSign (a b j:Axis):ℝ:= flips a j*flips b j
lemma spinCoil (j k:Axis) : Ortho.move ((s j * s k).ortho) = Ortho.move (Signed.reflect j) ∘ Ortho.move (Signed.reflect k):=by
 rw [show (s j*s k).ortho=Signed.reflect j*Signed.reflect k from map_mul Signed.inclusionO _ _]; exact funext (fun x=> Ortho.move_mul _ _ x)
lemma turnsTwice j k : signBit (s j * s k)=false:=by simp [signBit_mul]
abbrev foldRim j k:= signMot (s j * s k) (turnsTwice j k)
set_option quotPrecheck false
local notation "Φ"=> Ortho.move ((s j*s k).ortho)
lemma flip_at (x:E4) : Φ x b= bothSign j k b*x b:=by
 rw [spinCoil]; by_cases h:j=b<;> by_cases e:k=b<;> simp [*,flips,bothSign,Ne.symm] 
lemma doubleSign : bothSign j k b * bothSign j k b=1:=by unfold bothSign flips; split_ifs <;> norm_num
lemma still_space (h:j≠3)(t:k≠3): Lorentz.spatialTurn (foldRim j k).val:= ⟨show LinearMap.det (Matrix.toEuclideanLin (foldRim j k).val.val)=1 by rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]; exact (covers_all _).mp (foldRim j k).property, fun x=> by change Φ x 3=x 3; simp [flip_at,flips,bothSign,h,t]⟩
variable (h:j≠3)(t:k≠3)
abbrev flipLocationSt (a b:Axis)(y:a≠3)(w:b≠3) := Poincare.motion (Lorentz.room (foldRim a b).val (still_space a b y w))
local notation "ρ" => flipLocationSt j k h t
lemma motion_equal (x:E4): (ρ).sends x=Ortho.move (foldRim j k).val x:=by rw [flipLocationSt,Poincare.as_active]; rfl
lemma go_equal (x:E4): (ρ).sends x=Φ x:=motion_equal ..
lemma come_equal: (ρ)⁻¹=ρ:=by
 apply inv_eq_of_mul_eq_one_right; exact Poincare.by_placement _ _ (fun x=>by rw [Poincare.sends_mul, Poincare.sends_one]; exact test x)
where
  test (x:E4): (ρ).sends ((ρ).sends x)=x:=by rw [go_equal,go_equal]; apply PiLp.ext; intro b; rw[flip_at,flip_at,←mul_assoc,doubleSign,one_mul]

lemma mirrorLabel (f:ΧiMars)(a:ℝ) : TurnupMars j ((a:ℂ) • f)= (a:ℂ) • TurnupMars j f:=by rw[TurnupMars,map_smulₛₗ,map_smul,starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
lemma turn_coins (c:ΧiMars) : TurnupMars j (TurnupMars k c) = compassPiMars p (foldRim j k) c:=by unfold TurnupMars; rw [PiProperMoon,Calibration.comp_s,Calibration.clear]; exact (congrArg (fun f:_→ₗ[ℂ]_=> f c) (map_mul (spinFrame four) (s j) (s k))).symm
local notation "Y" => SurfRimL Z
variable {W:Surface (SurfRimL Z)} {X:Wightman (SurfRimL Z)} {H:(SurfRimL Z).RealSpin} (D:SurfCheckL Z)
variable (c:X.Realizes (W:=W) (SurfCheckL.VesselPL p D) H)
include c
lemma priceTurn (s0:SO)(i:Lorentz.spatialTurn s0.val)(v:ΧiMars): X.spin.rail (Lorentz.room s0.val i) (D.TinCanL v)=D.TinCanL (compassPiMars p s0 v):=by
 obtain ⟨z,rfl⟩:= (D.HingeL 0).surjective v
 rw [D.tinRiseL,c.letters.ties,c.letters.spatial,← D.tinRiseL,SurfCheckL.prepareL,LinearEquiv.apply_symm_apply]
lemma field_turn_st (F:Axis→ ΧiMars)(f:Test4)(hv:∀ a b, TurnupMars a (F b)= ((flips a b:ℝ):ℂ) • F b) : DragΛL X c ρ (X.operators.field (D.TinCanL (F b)) f)= ((bothSign j k b:ℝ):ℂ) • X.operators.field (D.TinCanL (F b)) (Joint.push ρ f):=by
 rw [MeadΛL]; change X.operators.field (X.spin.rail (Lorentz.room _ (still_space _ _ h t)) _) (Joint.push _ _)= _; rw [priceTurn p Z D c _ (still_space _ _ h t) _, ← turn_coins p j k,hv,mirrorLabel,hv,smul_smul, mul_comm,map_smul,map_smul]; unfold bothSign; rw [Complex.ofReal_mul,LinearMap.smul_apply]
omit c in
lemma direction_turn_st : (foldRim j k).val.motion (basis b)= bothSign j k b • basis b:=by ext l; change Φ (basis b) l=bothSign j k b * (basis b l); rw [flip_at]; by_cases h:l=b<;> simp [h] 
omit c
abbrev ΦpaySt(b:Axis):Test4→L[ℂ] Test4:= ΦshiftΛ (basis b)
lemma shift_fold (f:Test4): ΦpaySt b (Joint.push ρ f)= ((bothSign j k b:ℝ):ℂ) • Joint.push ρ (ΦpaySt b f):=by
 ext1 x
 let I:= (foldRim j k).val.motion.toContinuousLinearEquiv
 have hx: ((Joint.push ρ f):E4→ℂ)= fun x=> f (I x):= funext fun x=>by rw [Joint.push_at,come_equal,motion_equal]; rfl
 unfold ΦpaySt; rw [ΦsΛKnownL,hx,show fderiv ℝ (fun x=> f (I x)) x= (fderiv ℝ f (I x)).comp I.toContinuousLinearMap  from (by have hq:= fderiv_comp x ((f.smooth 1).differentiable (by simp) (I x)) I.differentiable.differentiableAt; rw [I.fderiv] at hq; exact hq),
  ContinuousLinearMap.comp_apply, show I.toContinuousLinearMap (basis b)= _ from direction_turn_st j k b,map_smul]; change _= ((bothSign j k b:ℝ):ℂ) • (Joint.push ρ (ΦshiftΛ (basis b) f)) x; rw [Joint.push_at,come_equal,motion_equal,ΦsΛKnownL, Complex.coe_smul]; rfl
lemma push_linear_st (b:ℂ)(f:Test4): Joint.push ρ (b • f)= b • Joint.push ρ f:=by ext1; simp [Joint.push_at]
include c
abbrev weightedTestSt (F:Axis→ΧiMars)(m0:Axis→ℂ)(f:Test4): Module.End ℂ X.operators.domain:=∑ i:Axis, m0 i • X.operators.field (D.TinCanL (F i)) (ΦshiftΛ (basis i) f)
abbrev authSt (F:Axis→ΧiMars):Prop:=∀ a b:Axis,TurnupMars a (F b)=((flips a b:ℝ):ℂ) • F b
lemma gauge_turn_st (F:Axis→ΧiMars)(m0:Axis→ℂ)(f:Test4)(hv: authSt F) : DragΛL X c ρ (weightedTestSt Z D (X:=X) F m0 f)=weightedTestSt Z D (X:=X) F m0 (Joint.push ρ f):=by
 let J(i)(f):= X.operators.field (D.TinCanL (F i)) f
 have hF(i:Axis): DragΛL X c ρ (J i (ΦshiftΛ (basis i) f))=J i (ΦshiftΛ (basis i) (Joint.push ρ f)):=by unfold J; rw[field_turn_st p Z j k _ h t D c F _ hv]; rw [show ΦshiftΛ (basis i) (Joint.push ρ f)= _ from shift_fold j k i h t f,map_smul]
 let Y'(s0:Module.End ℂ X.operators.domain):= DragΛL X c ρ s0
 have k': ∀ x:Axis, Y' (J x (ΦshiftΛ (basis x) f)) = J x (ΦshiftΛ (basis x) (Joint.push ρ f)) := hF
 unfold weightedTestSt; unfold Y' J DragΛL at k'; unfold DragΛL; apply LinearMap.ext; intro x; simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]; exact sum_congr rfl (fun i _=> congrArg (m0 i • ·) (DFunLike.congr_fun (k' i) x))
lemma turn_omega (g:Poincare): LocalActΛL X c g X.operators.omega= X.operators.omega:=Subtype.ext (c.covariance.vacuum g)
lemma turn_read (g:Poincare)(x y:X.operators.domain): inner ℂ (LocalActΛL X c g x) (LocalActΛL X c g y)=inner ℂ x y:=LinearIsometry.inner_map_map (𝕜:=ℂ) (show X.operators.domain →ₗᵢ[ℂ] _ from {LocalActΛL X c g with norm_map':= fun x=> X.action.usual g x.val}) x y
lemma turn_wake (g:Poincare)(A:Module.End ℂ X.operators.domain) (x) : DragΛL X c g A (LocalActΛL X c g x)= LocalActΛL X c g (A x):=by change LocalActΛL X c g (A (LocalActΛL X c g⁻¹ (LocalActΛL X c g x)))=_; rw[show LocalActΛL X c g⁻¹ (LocalActΛL X c g x)= x from by nth_rw 2 [←inv_inv g]; exact LocalHomeΛL X c g⁻¹ x]
lemma turnover_st (g:Poincare)(J M :Module.End ℂ X.operators.domain):
 let B(h: Poincare):= DragΛL X c h
 let v:= X.operators.omega
 inner ℂ v ((B g J) v)=inner ℂ v (J v) ∧ inner ℂ v ((B g M) v)=inner ℂ v (M v) ∧
 inner ℂ v (((B g J)*(B g M)) v)=inner ℂ v ((J*M) v):=by
 let Q:= LocalActΛL X c g; let v:= X.operators.omega; have h0:Q v=v:= turn_omega p Z D c g; have hr:= turn_read p Z D c g (X.operators.omega); have he₀ (v):inner ℂ X.operators.omega (Q v)=inner ℂ X.operators.omega v:=by  exact (congrArg (fun z=>inner ℂ z (Q v)) h0).symm.trans (hr v)
 intro B v' -- lets
 have h(M':Module.End ℂ X.operators.domain): B g M' v'=Q (M' v):=by rw [show v'=Q v from h0.symm]; exact turn_wake p Z D c g M' v
 rw [h,h, Module.End.mul_apply,h]; change _∧_∧ inner ℂ v (DragΛL _ _ _ _ (Q (M v)))=_; rw [turn_wake]; exact ⟨he₀ _,he₀ _,he₀ _⟩
#print axioms turnover_st
omit c
lemma fare_other_st (j:Axis):∃ k:Axis,k≠3∧ k≠j:=by
 by_cases e:j=(0:Axis); · exact ⟨1,by decide, e.symm ▸ (by decide : (1:Axis)≠0)⟩
 exact ⟨0,by decide,Ne.symm e⟩
abbrev SmallDoseSt (f: Test4):Prop:= f≠0 ∧ HasCompactSupport (f:E4→ℂ) ∧ (∫ x:E4,f x)=1 ∧ Probe.bar f = f ∧ ∀ x:E4,0 ≤(f x).re
local notation "Φθ" => (foldRim j k).val.motion
lemma FlipFold (x:E4) : (ρ).sends x= Φθ x := motion_equal ..
lemma foldPush (f:Test4):(fun x:E4=>Joint.push ρ f x)= f ∘ (Φθ):=funext fun x=>by rw[Joint.push_at,come_equal,FlipFold]; rfl
lemma in_folded (f:Test4) (x):x∈ tsupport (Joint.push ρ f)↔ Φθ x∈ tsupport f:=by
 rw [show ((Joint.push ρ f):E4→ℂ)= _ from foldPush ..]; exact Iff.of_eq (congrArg (x∈·) (tsupport_comp_eq_preimage f (Φθ).toHomeomorph))
lemma foldMark_st (f:Test4)(p:SmallDoseSt f) : SmallDoseSt (Joint.push ρ f):=by
 have hb:MeasurePreserving ((Φθ):E4→E4) volume volume:=by rw[show ((Φθ):E4→E4)= (ρ).sends from (funext (FlipFold j k h t)).symm]; exact (ρ).preserving
 have he:(∫ x:E4, Joint.push ρ f x)=1:= by simp_rw[Joint.push_at,come_equal,FlipFold]; rw[hb.integral_comp ((Φθ).toHomeomorph).measurableEmbedding,p.2.2.1]
 refine ⟨fun h=> ?_, ?_,he,?_ , fun x=>?_⟩
 · rw [h] at he; simp at he
 · rw [show ((Joint.push ρ f):E4→ℂ)= _ from foldPush ..]; exact p.2.1.comp_homeomorph ((Φθ).toHomeomorph)
 · ext1 x; simp only [Probe.bar_at,Joint.push_at]; exact Eq.trans (Probe.bar_at f _).symm (DFunLike.congr_fun p.2.2.2.1 _) 
 rw [Joint.push_at]; exact p.2.2.2.2 _
abbrev Apart_st (a:ℝ)(f g:Test4):Prop:=∀ x∈ tsupport f,∀ y∈ tsupport g, a< YM.time y - YM.time x ∧ x-y∈ spacelike
lemma fold_locale_st (a:ℝ)(f g:Test4)(u:Apart_st a f g) : Apart_st a (Joint.push ρ f) (Joint.push ρ g):=by
 intro x p y e; let P:= (Φθ); let L:= Lorentz.room (foldRim j k).val (still_space j k h t); have hz(w:E4): time (P w)= time w:= (still_space j k h t).2 w
 obtain ⟨q,q'⟩:= u (P x) ((in_folded j k h t ..).1 p) (P y) ((in_folded j k h t ..).1 e)
 rw [hz,hz] at q; rw [← map_sub] at q'; refine ⟨q,?_⟩; change Mink.m _<0; rw [← L.keeps]; exact q'
include c
abbrev pairPriceSt (A B:Module.End ℂ X.operators.domain):= let v:= X.operators.omega; inner ℂ v ((A*B) v)-inner ℂ v (A v)*inner ℂ v (B v)
omit c in
lemma payScaledSt (a:ℂ)(A B:Module.End ℂ X.operators.domain): pairPriceSt Z (X:=X) (a • A) B=a*pairPriceSt Z (X:=X) A B:=by simp only [pairPriceSt,smul_mul_assoc,LinearMap.smul_apply,inner_smul_right,mul_sub,mul_assoc] 
lemma oppositeBillSt (A:Test4→Module.End ℂ X.operators.domain)(B:Test4→Module.End ℂ X.operators.domain)(f g:Test4)(q: DragΛL X c ρ (A f)=-(A (Joint.push ρ f)))(e:DragΛL X c ρ (B g)= B (Joint.push ρ g)):
 pairPriceSt Z (X:=X) (A f) (B g) = -(pairPriceSt Z (X:=X) (A (Joint.push ρ f)) (B (Joint.push ρ g))):=by obtain ⟨z,x,b⟩:=turnover_st p Z D c ρ (A f) (B g); dsimp only [pairPriceSt] at * ; rw[←z,← x,← b,q,e]; simp only [Module.End.mul_apply,LinearMap.neg_apply,inner_neg_right]; ring 
lemma familiarSt (F:Axis→ ΧiMars)(f g:Test4)(σ:Axis→ℂ)(x: authSt F)(a:k≠j)(r:ℂ):
 pairPriceSt Z (X:=X) (r • X.operators.field (D.TinCanL (F j)) f) (weightedTestSt Z D (X:=X) F σ g)= -(pairPriceSt Z (X:=X) (r • X.operators.field (D.TinCanL (F j)) (Joint.push ρ f)) (weightedTestSt Z D (X:=X) F σ (Joint.push ρ g))):=by
 have h': DragΛL X c ρ (X.operators.field (D.TinCanL (F j)) f)= -(X.operators.field (D.TinCanL (F j)) (Joint.push ρ f)):=by rw[field_turn_st p Z j k _ h t D c F _ x]; apply LinearMap.ext; intro; rw [LinearMap.smul_apply,LinearMap.neg_apply]; simp [bothSign,flips,a]
 rw [payScaledSt,payScaledSt,oppositeBillSt p Z j k h t D c (X.operators.field (D.TinCanL (F j))) (fun s0=> weightedTestSt Z D (X:=X) F σ s0) f g h' (gauge_turn_st p Z j k h t D c F σ g x),mul_neg] 
#print axioms fold_locale_st
#print axioms foldMark_st
#print axioms familiarSt
end YM.GaugeFieldConstruction.Ember.Volumetric
end
