import GaugeFieldConstruction.RhojiQc
import GaugeFieldConstruction.Aerie
/-!
# Signed and spin-real orientation cost conventions
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8400
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S)
variable (s:Signed)
abbrev BoxmoveQc (s:Signed):= Ortho.motion s.ortho
def CozioQc (n:ℕ)(s:Signed): Points n≃ₗᵢ[ℝ] Points n where
 toFun x:=points (fun i: Fin n=> BoxmoveQc s (x i)); invFun x:=points (fun i:Fin n=> (BoxmoveQc s).symm (x i))
 left_inv x:= PiLp.ext (fun i=> by simp only [points_apply, LinearIsometryEquiv.symm_apply_apply])
 right_inv x:= PiLp.ext (fun i=> by simp only [points_apply,LinearIsometryEquiv.apply_symm_apply])
 map_add' x y:= PiLp.ext (fun i=> by change BoxmoveQc s (x i+y i)=BoxmoveQc s (x i)+BoxmoveQc s (y i); rw [map_add])
 map_smul' a x:= PiLp.ext fun i=> (BoxmoveQc s).map_smul a (x i)
 norm_map' x:= by rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]; exact Finset.sum_congr rfl fun i _=>by change ‖BoxmoveQc s (x i)‖^2=_; rw[LinearIsometryEquiv.norm_map]
lemma CozyPqc (x:Points n)(i): CozioQc n s x i=BoxmoveQc s (x i) :=rfl
lemma CordonQc (x:Points n)(v:CozioQc n s x∈ conf n): x∈conf n:= fun i j h=> v ((CozyPqc s x i).trans ((congr_arg (BoxmoveQc s) h).trans (CozyPqc s x j).symm))
def flipTestQc (q:Test n): Test n:= pullLinear (CozioQc n s).toContinuousLinearEquiv (fun _ h=> CordonQc s _ h) q
lemma flipAtQc (p:Test n)(x): flipTestQc s p x=p (CozioQc n s x):=rfl
lemma flipSupQc (p:Test n) : tsupport (flipTestQc s p)= (CozioQc n s) ⁻¹' tsupport p:= ts_pull _ p
noncomputable def moveBulbQc (b:Bulb):Bulb where
 f x:= b (BoxmoveQc s x)
 d:= b.d.comp (BoxmoveQc s).contDiff
 c:=b.c.comp_homeomorph (BoxmoveQc s).toHomeomorph
lemma maskRunQc (b:Bulb): run (moveBulbQc s b)=(BoxmoveQc s) ⁻¹' run b:= ((BoxmoveQc s).toHomeomorph.preimage_closure (support b.f)).symm
lemma MakerQc (b:Bulb)(p:Test n)(k)(r:b.Works p k): Works (moveBulbQc s b) (flipTestQc s p) k:=by
 have ht:=flipSupQc s p
 refine ⟨fun x h=> ?_,fun x h i e=>?_⟩
 · rw [ht] at h; exact (BoxmoveQc s).continuous.continuousAt.tendsto.eventually (show b.f =ᶠ[𝓝 (BoxmoveQc s (x k))] fun _=>1 from r.bulb (CozioQc n s x) h)
 rw[ht] at h; rw[maskRunQc]; exact r.direct _ h i e -- type tune
lemma zBoxQc (x:E4)(i): BoxmoveQc s x (s.perm i)= pay (s.flip i) (x i):=by rw [BoxmoveQc,Ortho.motion_at,Signed.ortho_move]; simp only [PiLp.toLp_apply, Signed.act_at,pay] -- tune
lemma SparkQc (i:Axis): BoxmoveQc s (basis i)=pay (s.flip i) (basis (s.perm i)):=by
 ext1 j; obtain ⟨b,rfl⟩:= s.perm.surjective j; rw[zBoxQc]; cases h:s.flip i <;> by_cases v:b=i <;> first| subst b; simp [h]| simp [h,v,s.perm.injective.ne v] -- tune
lemma DirPasteQc (k:Fin n)(a:Axis): CozioQc n s (direction k a)=pay (s.flip a) (direction k (s.perm a)):=by
 ext1 j; rw [CozyPqc]; by_cases h:j=k
 · subst j; rw[show direction k a k=basis a by simp[direction],SparkQc]; cases s.flip a <;> simp [direction]
 cases v:s.flip a <;> simp [direction,h] <;> exact map_zero (BoxmoveQc s) -- tune
lemma tiltPayQc (k:Fin n)(p:Test n)(a): tilt (direction k a) (flipTestQc s p)=pay (s.flip a) (flipTestQc s (tilt (direction k (s.perm a)) p)):=by
 let V:= (CozioQc n s).toContinuousLinearEquiv.toContinuousLinearMap
 ext1 x; rw [tilt_pays]; change fderiv ℝ (p ∘ V) x _=_; rw [fderiv_comp _ (diffT p _) V.differentiableAt,V.fderiv,ContinuousLinearMap.comp_apply]; rw [show V (direction k a)=pay (s.flip a) _ from DirPasteQc s k a]; cases q:s.flip a
 · rw [pay_false,pay_false,flipAtQc,tilt_pays]; rfl
 change fderiv ℝ (p:Points n→ℂ) (V x) _ = Neg.neg (flipTestQc _ _ x); rw [pay_true,map_neg,flipAtQc,tilt_pays]; rfl
lemma tiltmuQc (b:Bulb)(x:E4)(a): D (basis a) (moveBulbQc s b).f x= pay (s.flip a) (D (basis (s.perm a)) b.f (BoxmoveQc s x)):=by
 let V:= (BoxmoveQc s).toContinuousLinearEquiv.toContinuousLinearMap
 change fderiv ℝ (b.f ∘ V) x _=_; rw [fderiv_comp _ (b.d.differentiable (by simp) _) V.differentiableAt,V.fderiv,ContinuousLinearMap.comp_apply,show V (basis a)=pay (s.flip a) _ from SparkQc s a]
 cases q:s.flip a
 · rw[pay_false,pay_false]; rfl
 rw [pay_true,pay_true,map_neg]; rfl
-- S status. Polar price orientation exact. On plenum only. Need area may fill at f with exact Δ。
structure UpAngleQc {S:City}(Y:AreaQc S):Prop where
   rotation (s:Signed)(n:ℕ)(x:Fin n→UV five) (t:Points n): t∈ generic n→ Y.fee n (fun i=>spinFrame five s (x i)) (CozioQc n s t)= Y.fee n x t
   paper (n:ℕ)(x:Fin n→UV five)(t:Points n)(p: t∈ generic n): Y.fee n (fun i=>shade five (x i)) t=Cauchy.Conj.bar (Y.fee n x t)
   flavor (n:ℕ)(g:Flavor)(x:Fin n→UV five)(t:Points n)(p:t∈ generic n):Y.fee n (fun i=>flavors five g (x i)) t=Y.fee n x t
variable (v:UpAngleQc Y)
local notation "H"=> spinFrame five s
include v
lemma HermesQc (L:Fin n→l)(p: Test n): S.fee n (fun i=> (H) (L i)) p=S.fee n L (flipTestQc s p):=by -- include v
 rw[Y.price,Y.price]; unfold Test.applyTo; rw [← (CozioQc n s).measurePreserving.integral_comp (CozioQc n s).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding]; apply integral_congr_ae; filter_upwards [rooted_genericQc n] with x t; exact congr_arg _ (v.rotation s n L x t) -- annotation
lemma HermSpotQc (x:l)(L:Fin n→l)(k:Fin n)(p:Test n): S.spot (fun i=> H (L i)) k (H x) p=S.spot L k x (flipTestQc s p):=by
 rw [spot_cost,spot_cost,← HermesQc Y s v]; congr 2; ext1 i; by_cases h:i=k <;> simp[h]
#print axioms HermSpotQc
end YM.GaugeFieldConstruction.Ember.Hulse
