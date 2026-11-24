import GaugeFieldConstruction.VitaVenusMars
/-!
 # Reynolds-improvement tensor on the same U4 readers. (Beyond manuscript)
 Retains all c, theta_k, orientation even on improper Signed, fixed flavor etc;
 uses this very physical array.Many later W specs. Eu contour intertwiners next.
 Not imposing a simultaneous action of orthogonal on all typeof E in grade-5 heats. `tensionsMoon` may differ symbolically from p.J; p identifies gate comparisons of p.J, and (132) rotates *those* prices to compute canonical SO contour below. This keeps charge normalization without needing the gate comparisons to align the smooth pi at every f. Stay mean throughout.
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
variable {p:Ticket u C}{Y:AreaQc S}
namespace FirstPackMars
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y))
open Loft
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg


local instance closedR : CompactSpace Stage.SO:= by
  letI : CompactSpace Ortho := YM.Work.A15.compact_ortho
  apply isCompact_iff_compactSpace.mp
  have t : Continuous fun i: Ortho=> i.val.det:=continuous_subtype_val.matrix_det -- check
  have he :(Stage.orbit:Set Ortho)={p| p.val.det=1}:= Set.ext fun i=>covers_all i
  rw [he]; exact (isClosed_eq t continuous_const).isCompact

local instance : SecondCountableTopology Stage.SO:= by
  haveI : SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology (Axis→Axis→ℝ))
  haveI : SecondCountableTopology Ortho:= inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ:Set M4)))
  exact inferInstanceAs (SecondCountableTopology ↥((Stage.orbit:Set Ortho)))
local instance : MeasurableSpace Stage.SO := borel Stage.SO
local instance : BorelSpace Stage.SO:=⟨rfl⟩
private def freeze : TopologicalSpace.PositiveCompacts Stage.SO:=⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
private def μ : Measure Stage.SO:= Measure.haarMeasure freeze
local instance : μ.IsHaarMeasure:=by unfold μ; infer_instance
local instance : IsProbabilityMeasure μ:= ⟨Measure.haarMeasure_self⟩ -- adjust


-- shift from Pach data and assembly
variable (p)
abbrev SumMoonMars := Axis→Axis→ΧiMars
abbrev parcelMars (g:Ortho) (i j:Axis):ℂ:=ofReal (g.val i j)
def pileMoonMars (g:Ortho) (F:SumMoonMars) : SumMoonMars:=fun i j => ∑ a:Axis,∑ b:Axis,(parcelMars g i a*parcelMars g j b) • F a b
lemma pileThirdMars (g h:Ortho)(F:SumMoonMars) : pileMoonMars g (pileMoonMars h F) = pileMoonMars (g*h) F:=by
 have ht (u v:Axis): parcelMars (g*h) u v=∑ i:Axis,parcelMars g u i*parcelMars h i v:=by
    change ofReal ((g.val*h.val) u v)=_; rw[Matrix.mul_apply,Complex.ofReal_sum]; exact sum_congr rfl fun i _=> ofReal_mul ..
 funext i j; unfold pileMoonMars; simp_rw [ht, Finset.smul_sum, smul_smul]; simp_rw [sum_mul,mul_sum,Finset.sum_smul]
 let X(a b u v:Axis):=(parcelMars g i a*parcelMars g j b*(parcelMars h a u*parcelMars h b v)) • F u v
 -- reorder RHS into uv ab. column symm. use abstract
 have wind {A:Type}[AddCommMonoid A](Z:Axis→Axis→Axis→Axis→A): (∑ a:Axis,∑ b:Axis,∑ i:Axis,∑ j:Axis,Z a b i j)=∑ i:Axis,∑ j:Axis,∑ a:Axis,∑ b:Axis,Z a b i j:=by
    rw[show (∑ a:Axis,∑ b:Axis,∑ i:Axis,∑ j:Axis,Z a b i j)=(∑ t:Axis×Axis,∑ r:Axis×Axis,Z t.1 t.2 r.1 r.2) from ?_, Finset.sum_comm]; all_goals simp_rw [Fintype.sum_prod_type]
 change (∑ a:Axis,∑ b:Axis,∑ i:Axis,∑ j:Axis,X a b i j)=_; rw [wind X]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; apply sum_congr rfl; intro w _; apply sum_congr rfl; intro s _; unfold X; congr 1; ring
lemma pile_endMars (Z:End ℂ ΧiMars)(g:Ortho)(F:SumMoonMars): (fun i j=> Z (pileMoonMars g F i j))=pileMoonMars g (fun i j=>Z (F i j)):=funext fun i=> funext fun j=> by simp [pileMoonMars]
lemma pile_oneMars (F:SumMoonMars): pileMoonMars 1 F=F:=by
 funext i j; unfold pileMoonMars parcelMars
 rw[sum_eq_single i]
 · rw [sum_eq_single j]
   · simp
   · intro b _ h; simp [Matrix.one_apply,Ne.symm h]
   simp
 · intro b _ h; simp [Matrix.one_apply,Ne.symm h]
 simp
lemma parcelInvMars (s:Ortho)(i j): parcelMars s⁻¹ i j=parcelMars s j i:=rfl
def TensPitchMars (g:SO)(F:SumMoonMars):SumMoonMars:= pileMoonMars g.val fun a b=> compassPiMars p g (F a b)
lemma tensMulMars (g h:SO)(F:SumMoonMars): TensPitchMars p g (TensPitchMars p h F)= TensPitchMars p (g*h) F:=by simp_rw [TensPitchMars,pile_endMars,pileThirdMars,← sailMulMars]; rfl
lemma tens_oneMars (F:SumMoonMars): TensPitchMars p 1 F=F:=by unfold TensPitchMars; simp_rw [sailOneMars]; exact pile_oneMars F
-- read controls
abbrev unitsMars (g:SO):=TensPitchMars p g p.J
lemma unitsSymMars (g:SO)(a b):unitsMars p g a b=unitsMars p g b a:=by
 unfold unitsMars TensPitchMars pileMoonMars; rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_comm]; dsimp only; rw[p.strict]
lemma parcelContMars (i j:Axis): Continuous (fun g:SO=>parcelMars g.val i j):= by
 let h: Continuous (fun a:SO=>a.val.val):= continuous_subtype_val.comp continuous_subtype_val; change Continuous (fun a:SO=> ofReal (a.val.val i j)); exact continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp h))
lemma unitsContMars (a b):Continuous (fun s:SO=>FreightMars (unitsMars p s a b)) :=by
 simp_rw[unitsMars,TensPitchMars,pileMoonMars,map_sum,map_smul]; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; exact ((parcelContMars a i).mul (parcelContMars b j)).smul (PiContinueMars p (p.J i j))
-- global avg cost
private def SpinPulseMars (f:SO→ΧiMars):ΧiMars:= FreightMars.symm (∫ g:SO,FreightMars (f g) ∂μ)
private lemma SpinReadMoon {B:Type*} [NormedAddCommGroup B][NormedSpace ℝ B][CompleteSpace B](f:SO→ΧiMars)(h:Continuous (FreightMars ∘ f))(A: ΧiMars→ₗ[ℝ] B) : A (SpinPulseMars f)=∫ g:SO,A (f g) ∂μ := by
 let P : grainMars →L[ℝ] B := LinearMap.toContinuousLinearMap (A ∘ₗ (FreightMars.symm.toLinearMap.restrictScalars ℝ))
 change P _=_; rw [← P.integral_comp_comm (show Integrable (fun g=>FreightMars (f g)) μ from h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; exact integral_congr_ae (Eventually.of_forall fun g=> congrArg A (FreightMars.symm_apply_apply _)) -- tune
-- keep μ private
noncomputable def TotalStarsMars (i j:Axis):ΧiMars:= SpinPulseMars (fun s=> unitsMars p s i j)
lemma totalSymMars (i j:Axis): TotalStarsMars p i j=TotalStarsMars p j i:=congrArg SpinPulseMars (funext fun g=> unitsSymMars p g i j)
-- real shade Linear test
private def MRI (s:Floor): UV s →ₗ[ℝ] UV s where
 toFun:= Calibration.shade s
 map_add':=map_add _
 map_smul' a x:=by change Calibration.shade _ (a • x)=a • _; rw [real_pay,map_smulₛₗ,show Cauchy.Conj.bar _=(a:ℂ) from Complex.conj_ofReal a]; exact (real_pay a _ _).symm
lemma unitsCMars (g:SO)(i j):Calibration.shade four (unitsMars p g i j) = unitsMars p g i j:=by
 unfold unitsMars TensPitchMars pileMoonMars; simp_rw [map_sum]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; rw [← Complex.ofReal_mul,map_smulₛₗ,show Cauchy.Conj.bar _=(Complex.ofReal (_*_:ℝ)) from Complex.conj_ofReal _,← shadePiMoon,p.real_form]
lemma totalCMars (a b):Calibration.shade four (TotalStarsMars p a b)=TotalStarsMars p a b:= by
 apply FreightMars.injective
 let P:=FreightMars.toLinearMap.restrictScalars ℝ ∘ₗ MRI four
 change P (SpinPulseMars _)= FreightMars _; rw[SpinReadMoon _ (unitsContMars p a b) P,TotalStarsMars,SpinPulseMars,LinearEquiv.apply_symm_apply]; exact integral_congr_ae (Eventually.of_forall fun i=> congrArg FreightMars (unitsCMars p i a b))

section spend
variable {B:Type*}[NormedAddCommGroup B][NormedSpace ℝ B][CompleteSpace B]
private lemma rateCompMars (a b)(Y: ΧiMars→ₗ[ℝ] B): Integrable (fun g:SO=> Y (unitsMars p g a b)) μ:=by
 let P:= LinearMap.toContinuousLinearMap (Y ∘ₗ (FreightMars.symm.toLinearMap.restrictScalars ℝ))
 have e: Continuous (fun g:SO=> Y (unitsMars p g a b)):= (P.continuous.comp (unitsContMars p a b)).congr fun g=> congrArg Y (FreightMars.symm_apply_apply _)
 exact e.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private lemma rateSumMoon (Y: Axis→Axis→(ΧiMars→ₗ[ℝ] B)) : (∑ a:Axis,∑ b:Axis,Y a b (TotalStarsMars p a b))=∫ g:SO, (∑ a:Axis,∑ b:Axis,Y a b (unitsMars p g a b)) ∂μ:=by
 have hi (a:Axis) : Integrable (fun g:SO=>∑ b:Axis,Y a b (unitsMars p g a b)) μ := integrable_finsetSum _ fun i _=> rateCompMars p _ _ _
 rw [integral_finsetSum _ (fun a _=>hi a)]; apply sum_congr rfl; intro a _; rw[integral_finsetSum _ (fun b _=>rateCompMars p a b (Y a b))]; apply sum_congr rfl; intro i _; exact SpinReadMoon _ (unitsContMars p a i) _
lemma totalRateMars (Z:Axis→Axis→(ΧiMars→ₗ[ℝ] B))(v:B)(h:∀ g:SO, ∑ a:Axis,∑ b:Axis,Z a b (unitsMars p g a b)=v) : ∑ a:Axis,∑ b:Axis,Z a b (TotalStarsMars p a b)=v:=by rw [rateSumMoon]; simp_rw [h]; simp
end spend
private lemma pitchRateMars (K: End ℂ ΧiMars)(g:Ortho)(i j) : FreightMars (pileMoonMars g (fun a b=> K (TotalStarsMars p a b)) i j)=∫ s:SO, FreightMars (pileMoonMars g (fun a b=>K (unitsMars p s a b)) i j) ∂μ := by
 let F(a b:Axis):= parcelMars g i a*parcelMars g j b
 let Z(a b:Axis): ΧiMars →ₗ[ℝ] grainMars:= (FreightMars.toLinearMap ∘ₗ (F a b • K)).restrictScalars ℝ
 unfold pileMoonMars; simp_rw[map_sum] -- tune
 exact rateSumMoon p Z
lemma totalTurnMars (s:SO) : TensPitchMars p s (TotalStarsMars p)=TotalStarsMars p:=by
 funext a b; apply FreightMars.injective
 unfold TensPitchMars; rw[pitchRateMars]; simp_rw [show ∀ g:SO,pileMoonMars s.val (fun a b=> compassPiMars p s (unitsMars p g a b))=unitsMars p (s*g) from fun g=>tensMulMars p s g _]; unfold TotalStarsMars SpinPulseMars; rw [LinearEquiv.apply_symm_apply]; exact (measurePreserving_mul_left μ s).integral_comp (Homeomorph.mulLeft s).measurableEmbedding (fun g=>FreightMars (unitsMars p g a b))
lemma totalFrameMars (s:SO)(i j):compassPiMars p s (TotalStarsMars p i j)= pileMoonMars s.val⁻¹ (TotalStarsMars p) i j:= by
 conv_rhs=> rw [←totalTurnMars p s]; unfold TensPitchMars; rw [pileThirdMars,inv_mul_cancel,pile_oneMars]
private lemma hueContinuous (s:Ortho): Continuous (HueTurnsMars s):= by
 change Continuous (fun g:SO=> (⟨s*g.val*s⁻¹,_⟩:SO)); exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
private def huesMoon (s:Ortho): SO ≃ₜ* SO where
 toFun:=HueTurnsMars s
 invFun:= HueTurnsMars s⁻¹
 left_inv g:= Subtype.ext (by simp[HueTurnsMars,mul_assoc])
 right_inv g:=Subtype.ext (by simp[HueTurnsMars,mul_assoc])
 continuous_toFun:= hueContinuous _
 continuous_invFun:=hueContinuous _
 map_mul':= map_mul _
private lemma hueMeasureMars (s:Ortho) : MeasurePreserving (HueTurnsMars s) μ μ:=by
 let V:=huesMoon s
 haveI : IsProbabilityMeasure (μ.map V) := ⟨by rw [Measure.map_apply (show Measurable (V:SO→SO) from V.continuous.measurable) MeasurableSet.univ,Set.preimage_univ,measure_univ]⟩ -- tune
 haveI:=V.isHaarMeasure_map μ
 exact ⟨V.continuous.measurable,Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map V) μ⟩
lemma preBodyMars (s:Signed): (fun a b=> spinFrame four s (p.J a b)) = pileMoonMars s.ortho⁻¹ p.J:=by
 funext a b; rw [stressTurnMars]; unfold pileMoonMars; simp_rw[parcelInvMars]; rw[sum_eq_single (s.perm a)]
 · rw[sum_eq_single (s.perm b)]
   · unfold parcelMars; change _=(ofReal (s.matrix _ a) * ofReal (s.matrix _ b)) • _; simp only [Signed.matrix_at,↓reduceIte]; cases s.flip a <;> cases s.flip b <;> simp
   · intro i _ h; unfold parcelMars; change (ofReal _ * ofReal (s.matrix i b)) • _=_ -- precedence tune
     simp[Signed.matrix_at,Ne.symm h]
   simp
 · intro i _ h; unfold parcelMars; have e: s.ortho.val i a=0:=by rw[show s.ortho.val=s.matrix from rfl]; simp[Signed.matrix_at,Ne.symm h]; -- tune
   simp_rw[e]; simp
 simp
lemma hypeMoonMars (s:Signed)(g:SO): pileMoonMars s.ortho (fun i j=> spinFrame four s (unitsMars p g i j))=unitsMars p (HueTurnsMars s.ortho g) :=by
 let A:= s.ortho; let V:=HueTurnsMars s.ortho g; let T:=compassPiMars p
 unfold unitsMars TensPitchMars; rw [pile_endMars]; change pileMoonMars A (pileMoonMars g.val fun i j=> spinFrame four s (compassPiMars p g (p.J i j)))=_
 simp_rw [DutyPiiotMars p s]; rw [pileThirdMars]; have he(a b): spinFrame four s (p.J a b)=pileMoonMars A⁻¹ p.J a b:=congr_fun (congr_fun (preBodyMars p s) a) b
 simp_rw [he]; rw [pile_endMars,pileThirdMars]; rfl -- tune
lemma totalSignedMars (s:Signed): pileMoonMars s.ortho (fun a b=>spinFrame four s (TotalStarsMars p a b))=TotalStarsMars p:=by
 funext a b; apply FreightMars.injective; rw [pitchRateMars]; simp_rw [hypeMoonMars]; unfold TotalStarsMars SpinPulseMars; rw [LinearEquiv.apply_symm_apply]; exact (hueMeasureMars s.ortho).integral_comp (huesMoon s.ortho).toHomeomorph.measurableEmbedding (fun g=> FreightMars (unitsMars p g a b))
lemma totalImproperMars (s:Signed)(i j): spinFrame four s (TotalStarsMars p i j)=pileMoonMars s.ortho⁻¹ (TotalStarsMars p) i j:=by
 conv_rhs=> rw[←totalSignedMars p s]; rw[pileThirdMars, inv_mul_cancel,pile_oneMars]
lemma unitsFlavorMars (g:SO)(V:Flavor)(i j): flavors four V (unitsMars p g i j)=unitsMars p g i j:=by
 unfold unitsMars TensPitchMars pileMoonMars
 simp_rw [map_sum,map_smul, ← DayFlavorMars, show ∀ i j, flavors four V (p.J i j)=p.J i j from fun i j=>(p.taste i j).2 _]
lemma totalFlavorMars (V:Flavor)(i j): flavors four V (TotalStarsMars p i j)=TotalStarsMars p i j:=by
 apply FreightMars.injective
 let Z:= FreightMars.toLinearMap ∘ₗ (flavors four V)
 change Z _=FreightMars _; refine (SpinReadMoon (B:=grainMars) _ (unitsContMars p i j) (Z.restrictScalars ℝ)).trans ?_
 unfold TotalStarsMars SpinPulseMars; rw[LinearEquiv.apply_symm_apply]; exact integral_congr_ae (Eventually.of_forall fun q=>congrArg FreightMars (unitsFlavorMars p q V i j))
#print axioms totalSignedMars
#print axioms totalFrameMars
#print axioms totalRateMars
#print axioms totalCMars
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
