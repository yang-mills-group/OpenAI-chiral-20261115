import GaugeFieldConstruction.LotusTensorMars
import GaugeFieldConstruction.SunfireCell
/-!
# Lorentz stress multiplet. In actual field space. No covariance hypothesis on Eu T-boosts. Keep plus energy and absolute scale.
 Contrav indices: star, transforms as inverse (Ua field(x) Va = ...), below Ward and D.Spatial. Wickγ=−i on clock,1 in space. Thus T^tt=− TE_tt. No improprer Lor assertions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Mink Cell
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)

abbrev BinΛL:= Axis × Axis
abbrev DeckΛL:= UnitV.wings UnitV
abbrev RideΛL:= PilotCellL.spar PilotCellL
noncomputable def ErosΛL : Cauchy.J BinΛL→ₗ[ℂ]ΧiMars:= jet (fun k=>TotalStarsMars p k.1 k.2)
lemma ErosEuΛL (g:SO): compassPiMars p g ∘ₗ ErosΛL p= ErosΛL p ∘ₗ rotate DeckΛL g.val:=by
 apply ket_ext; intro i; rw [LinearMap.comp_apply,LinearMap.comp_apply]; unfold ErosΛL; rw [on_ket,totalFrameMars]; unfold rotate; simp only [MonoidHom.coe_mk,OneHom.coe_mk,Cell.bill,on_ket,map_sum,map_smul]; unfold DeckΛL wings UnitV pileMoonMars; simp only [MonoidHom.coe_mk,OneHom.coe_mk,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,ofReal_mul,parcelInvMars]
lemma ΦErosΛL (Ω:Ortho.Skew): (scorePathL p Ω) ∘ₗ ErosΛL p= ErosΛL p ∘ₗ DeckΛL.beta Ω:=by
 apply LinearMap.ext; intro i
 apply FreightMars.injective; ext1 j
 let X:= (LinearMap.proj (φ:=fun _ : SpeckMars=>ℂ) j) ∘ₗ FreightMars.toLinearMap
 let c:ℝ→ΧiMars:= fun t=> compassPiMars p (Angles.rise Ω t) (ErosΛL p i)
 have h:HasDerivAt (X ∘ c) (X (scorePathL p Ω (c 0))) 0:= sailPiMars p (ErosΛL p i) Ω 0 X
 have he:c 0= ErosΛL p i:=by unfold c; rw [show Angles.rise Ω 0=1 from Subtype.ext (YM.Work.A13.oneParameter_zero _), map_one]; rfl
 rw[he,show c=ErosΛL p ∘ (fun t=> DeckΛL.rotate (Ortho.oneParameter Ω t) i) from funext fun j=> LinearMap.congr_fun (ErosEuΛL p (Angles.rise Ω j)) i] at h
 exact h.unique (Stage.posts (DeckΛL.north Ω i) (ErosΛL p) X)
lemma CapeErosΛL (g:Lorentz): SpheruleL p g ∘ₗ ErosΛL p= ErosΛL p ∘ₗ rideL RideΛL g :=by
 apply SeenLorL g
 · rw [map_one,map_one]; rfl
 · intro i j u v; rw [map_mul,map_mul,show ∀ (A B:Module.End ℂ ΧiMars), A*B=A ∘ₗ B from fun _ _=>rfl, LinearMap.comp_assoc,v,← LinearMap.comp_assoc,u,LinearMap.comp_assoc]; rfl
 · intro i h; rw[SpheruleParkL p i h,IdleRideL]; exact ErosEuΛL p (parkLorL i h)
 intro a t; apply LinearMap.ext; intro i
 let Y:ℝ→ΧiMars:=fun t=> SpheruleL p (γBeamL a t) (ErosΛL p i)
 let Z:ℝ→ΧiMars:= fun t=> ErosΛL p (rideL RideΛL (γBeamL a t) i)
 let U:=ThriveL p a
 have he:Y 0=Z 0:=by unfold Y Z γBeamL; rw [Ray.boost_start,map_one,map_one]; rfl
 refine congr_fun (Stage.captain U Y Z (ovalL (SpheruleL p) (ThriveL p) a (fun x=>glowersL p x a) _) (fun q=>?_) he) t
 have hw(r) :ErosΛL p (NightL DeckΛL a r)= U (ErosΛL p r) := by unfold U ThriveL NightL; rw [LinearMap.smul_apply,LinearMap.smul_apply,map_smul]; congr 1; exact LinearMap.congr_fun (ΦErosΛL p (pVecΩL a)).symm r
 have h' := Stage.posts (ovalRideL RideΛL a i q) (ErosΛL p)
 rw [hw] at h'; exact h'

lemma LampEuΛL (g:Lorentz)(i j:Axis): SpheruleL p g (TotalStarsMars p i j) = ∑ a:Axis,∑ b:Axis, ((σVecL g a i)*(σVecL g b j)) • TotalStarsMars p a b:= by
 have h:= LinearMap.congr_fun (CapeErosΛL p g) (ket (i,j)); simp only[LinearMap.comp_apply,ErosΛL,rideL,MonoidHom.coe_mk,OneHom.coe_mk,codeL,on_ket,map_sum,map_smul,Fintype.sum_prod_type] at h; exact h

abbrev costΛ (g:Lorentz)(i j:Axis):ℂ:= ofReal (g.act (basis j) i)
def MinkΛM (i:Axis):ℝ:=if i=timeAxis then 1 else -1
lemma ΦMinkΛ (i:Axis): (Wickγ i)^2= - (ofReal (MinkΛM i)):=by by_cases h:i=timeAxis <;> simp[Wickγ,h,MinkΛM]
lemma MinkRowΛ (x:E4)(a:Axis): General.walk Lorentz.reverseL x a= MinkΛM a*x a := by
 rw [Lorentz.reversing]; refine Fin.lastCases ?_ (fun i=> ?_) a -- use explicit
 · change time _=(if timeAxis=timeAxis then 1 else -1)*_; rw [time_position,if_pos rfl,one_mul]; rfl
 change spatial (position (-spatial x) (time x)) i=MinkΛM _*_; rw [spatial_position]; simp only [MinkΛM]; rw [if_neg (show i.castSucc≠timeAxis from ?_)]; · rw [neg_mul,one_mul]; rfl
 exact Fin.castSucc_ne_last i
lemma MinkBasisΛ (a:Axis): General.walk Lorentz.reverseL (basis a)= MinkΛM a • basis a:= by ext1 i; rw [MinkRowΛ]; by_cases h:i=a <;> simp[h,Ne.symm,basis_eq]
lemma MinkSwapΛ (g:Lorentz)(i j:Axis): MinkΛM i * (g.act (basis j)) i * MinkΛM j= (Lorentz.act g⁻¹ (basis i)) j:= by
 have z:inner ℝ (basis i) (g.dual.act (basis j))=inner ℝ (basis j) (Lorentz.act g⁻¹ (basis i)):=by rw [Lorentz.dual_adjoint,ContinuousLinearMap.adjoint_inner_right,real_inner_comm]
 simp only [basis_inner] at z
 change General.walk (Lorentz.reverseL * g.val*Lorentz.reverseL) (basis j) i= _ at z
 rw [General.walk_mul, General.walk_mul,MinkRowΛ,MinkBasisΛ, map_smul] at z
 change MinkΛM i * (MinkΛM j*(g.act (basis j) i))= _ at z
 rw[←z]; ring
lemma MinkSwapPhaseΛ (g:Lorentz)(a i:Axis): (Wickγ i)⁻¹ * (σVecL g a i) = costΛ g⁻¹ i a * (Wickγ a)⁻¹:=by
 change _ * (Wickγ a* _ * (Wickγ i)⁻¹)= _; unfold costΛ; rw[← MinkSwapΛ g a i]; push_cast
 change (Wickγ i)⁻¹*(Wickγ a* _ *(Wickγ i)⁻¹)= _
 field_simp [wickLiveL]
 -- algebra tune
 rw [ΦMinkΛ, ΦMinkΛ]
 have he: ((ofReal (MinkΛM i))^2:ℂ)=1:=by by_cases h:i=timeAxis<;> simp [MinkΛM,h]
 change -ofReal (MinkΛM a) * ofReal (g.act (basis i) a) = _; grind
-- physical inverse-index multiplet
abbrev SkylineΜΛ (i j:Axis):ΧiMars:= ((Wickγ i)⁻¹*(Wickγ j)⁻¹) • TotalStarsMars p i j
lemma ΛμErosL (g:Lorentz)(i j:Axis): SpheruleL p g (SkylineΜΛ p i j) = ∑ a:Axis,∑ b:Axis,(costΛ g⁻¹ i a * costΛ g⁻¹ j b) • SkylineΜΛ p a b:=by
 simp_rw [SkylineΜΛ,map_smul,LampEuΛL,Finset.smul_sum,smul_smul]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; congr 1; calc
    _=((Wickγ i)⁻¹*(σVecL g a i))*((Wickγ j)⁻¹*(σVecL g b j)):=by ring
    _=_:=by rw [MinkSwapPhaseΛ,MinkSwapPhaseΛ]; ring
lemma ΜΛSymL (i j:Axis): SkylineΜΛ p i j=SkylineΜΛ p j i:=by unfold SkylineΜΛ; rw [totalSymMars,mul_comm]
lemma ΛFlip (a i:Axis): parcelMars (Signed.mirror timeAxis).ortho i a=if i=a then (-ofReal (MinkΛM i):ℂ) else 0:=by
 change ofReal ((Signed.mirror timeAxis).matrix _ _)=_; rw [Signed.matrix_at]; by_cases p:i=a
 · subst i; by_cases v:a=timeAxis <;> simp [Signed.mirror,v,MinkΛM,eq_comm]
 simp [Signed.mirror,p, Ne.symm p]
lemma ΛShade (i j:Axis): asterL (SkylineΜΛ p i j)=SkylineΜΛ p i j:=by
 unfold SkylineΜΛ; rw [map_smulₛₗ]; change (star _) • spinFrame _ _ (Calibration.shade four _)=_
 rw[totalCMars,totalImproperMars]; simp_rw [pileMoonMars, parcelInvMars,ΛFlip]
 rw[sum_eq_single i]
 · rw[sum_eq_single j]
   · simp only [if_true,smul_smul,Matrix.map_apply] -- tune
     congr 1
     by_cases h:i=timeAxis<;> by_cases v:j=timeAxis<;> simp [Complex.star_def,Wickγ,h,MinkΛM,v]
   · intro b _ h; simp [h]
   simp
 · intro a _ h; simp [h]
 simp
#print axioms ΛμErosL
#print axioms ΛShade
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
