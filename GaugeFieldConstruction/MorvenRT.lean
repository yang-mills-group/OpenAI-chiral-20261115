import GaugeFieldConstruction.ErisonRT
import GaugeFieldConstruction.ItorRT
/-!
 # interior Ward shutter bill. Resolve Vfg all $x along possible p+u+i t. B.∆ positivity only at PathUL verdict. PriceProof Costs.s
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
noncomputable abbrev shiftDoorRt (y:E4): Space3 ×ℝ ≃ₜ E4:= divide.symm.toHomeomorph.trans (Homeomorph.addLeft y)
@[simp] lemma shiftDoorChargeRT (y:E4)(z:Space3×ℝ): shiftDoorRt y z=y+position z.1 z.2:=rfl
lemma shiftDoorPresRT(y:E4):MeasurePreserving (shiftDoorRt y):=by
 have h:MeasurePreserving divide.symm.toHomeomorph:= (MeasurePreserving.symm (divide.toHomeomorph.toMeasurableEquiv) volume_divide)
 exact (measurePreserving_add_left volume y).comp h
noncomputable def φInXRt (f:ContDiffBump (0:Space3)):= ofRealCLM ∘ ↑f
lemma φtasteRt (f:ContDiffBump (0:Space3))(i:Fin 3)(x:Space3): dxTRt i (φInXRt f) x=↑(fderiv ℝ f x (skyIRT i)):=by
 unfold dxTRt φInXRt; rw [(Complex.ofRealCLM.hasFDerivAt.comp x (f.contDiff.differentiable (n:=∞) (by simp) x).hasFDerivAt).fderiv]; rfl
#print axioms shiftDoorPresRT
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "Φ_H"=> H.TinCanL ∘ V
local notation "Τh" => TouchMΛ H (N:=N)
local notation "Ξ"=> CoffΜΛ H p
local notation "$ΐ"=> RespiteΛL H (N:=N)
variable (k:Fin n)(a:Axis)(B:ContDiffBump (0:ℝ))(f:ContDiffBump (0:Space3))(x:Points n)
local notation "Φ_T"=> UpShadeRt B f (x k)
variable (w:BreatherMars (UpShadeRt B f (x k)) k x)(m:x∈NSF.Work.C20.ordered n)
noncomputable def NormLRT (i:Axis):ℂ:= -(MinkΛM a:ℂ)*Wickγ i
noncomputable abbrev ILIrt (i:Axis) (y:E4):= (YM.Analysis.D (basis i) (UpShadeRt B f (x k)).f y) • RespiteΛL H (N:=N) (Fin.cons (SkylineΜΛ p i a) V) (YM.Points.cons y x)
local notation "Vvals"=> ILIrt p H (N:=N) V k a B f x
noncomputable abbrev EuQtyTRt (i:Axis)(s:ℝ):= ∫ u:Space3, ILIrt p H (N:=N) V k a B f x i (shiftDoorRt (x k) (u,s))
local notation "Fcost"=> EuQtyTRt p H (N:=N) V k a B f x
include w G hz hv e
lemma FluxBlessRT (i:Axis): Integrable ((Vvals i) ∘ shiftDoorRt (x k)):= ((shiftDoorPresRT _).integrable_comp_emb (shiftDoorRt _).measurableEmbedding).2 (SimpleFluxΛL p H G hz hv e V k a i (Φ_T) w)
lemma FluxPaidRT (i:Axis): (∫ y:E4,ILIrt p H (N:=N) V k a B f x i y)= (∫ s:ℝ,EuQtyTRt p H (N:=N) V k a B f x i s):=by
 let J:= shiftDoorRt (x k); rw [← (shiftDoorPresRT _).integral_comp J.measurableEmbedding (Vvals i)]; exact integral_prod_symm ((Vvals i) ∘ J) (FluxBlessRT p H G hz hv e V k a B f _ w i)
lemma FluxPermitRT (i:Axis): Integrable (EuQtyTRt p H (N:=N) V k a B f x i):=(FluxBlessRT p H G hz hv e V k a B f _ w i).integral_prod_right
omit e w
variable (s:ℝ)(g:Bool)(U:∀ u:Space3,QchIRt k g (PαXRT s (wickSlice n x)) u∈tube (n+1))
local notation "wₓ"=> PαXRT s (wickSlice n x)
local notation "Φ_ν"=> φInXRt f
include U
lemma ColdβRt : EuQtyTRt p H (N:=N) V k a B f x timeAxis s= (deriv B s:ℝ)* PanProjRT (X:=N) k (Ξ) (Φ_H) a (φInXRt f) timeAxis g (PαXRT s (wickSlice n x)):=by
 unfold EuQtyTRt ILIrt PanProjRT; rw [← integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun u=>?_
 dsimp only []; rw [shiftDoorChargeRT,reactorTRt p H G hz hv V k a _ g x s u (U u),ΦshadeTIRT]
 simp only [add_sub_cancel_left,time_position,spatial_position, Complex.real_smul,ofReal_mul,mul_assoc]; rfl
lemma ColdSideRt (i:Fin 3): EuQtyTRt p H (N:=N) V k a B f x i.castSucc s= (B s:ℝ)* PanProjRT (X:=N) k (Ξ) (Φ_H) a (dxTRt i (φInXRt f)) i.castSucc g (PαXRT s (wickSlice n x)):=by
 unfold EuQtyTRt ILIrt PanProjRT; rw [← integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun u=>?_
 dsimp only []; rw [shiftDoorChargeRT,reactorTRt p H G hz hv V k a _ g x s u (U u),ΦshadeSIRT,φtasteRt]; simp only [add_sub_cancel_left,time_position,spatial_position,Complex.real_smul,ofReal_mul,mul_assoc]
-- simplify total
noncomputable abbrev ΛSignXRt (a:Axis):ℂ:= I*(MinkΛM a:ℂ)
noncomputable abbrev ΛPaidRT (s:ℝ):= ∑ i:Axis, NormLRT a i * EuQtyTRt p H (N:=N) V k a B f x i s
local notation "Τbill"=> ΛPaidRT p H (N:=N) V k a B f x
lemma ΨAetnaRt: ΛPaidRT p H (N:=N) V k a B f x s= ΛSignXRt a * ((deriv B s:ℝ)*PanProjRT (X:=N) k (Ξ) (Φ_H) a (φInXRt f) timeAxis g (PαXRT s (wickSlice n x)) + (B s:ℝ) * I * DawnSideRt (X:=N) k (Ξ) (Φ_H) a (φInXRt f) g (PαXRT s (wickSlice n x))) :=by
 unfold ΛPaidRT; rw [Fin.sum_univ_castSucc, ← show timeAxis=Fin.last 3 from rfl,ColdβRt p H G hz hv V k a B f _ _ _ U, mul_add,add_comm]; congr 1
 · unfold NormLRT ΛSignXRt Wickγ; simp only [↓reduceIte]; ring
 unfold DawnSideRt; rw [Finset.mul_sum,Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [ColdSideRt p H G hz hv V k a B f _ _ _ U]; unfold NormLRT ΛSignXRt Wickγ; simp [Fin.castSucc_ne_last]; ring_nf; simp
omit G hz hv U
lemma AnsonOutRT (s:ℝ)(r:s∉closedBall (0:ℝ) B.rOut): ΛPaidRT p H (N:=N) V k a B f x s=0:=by
 apply sum_eq_zero; intro i _; rw [show Fcost i s=0 from ?_,mul_zero]
 unfold EuQtyTRt; rw [← setIntegral_univ]; apply setIntegral_eq_zero_of_forall_eq_zero
 intro y _; dsimp only []; unfold ILIrt; rw [shiftDoorChargeRT]
 let q:= x k + position y s
 change Analysis.D (basis i) (UpShadeRt B f (x k)).f q • (_:ℂ)=_; rw[show Analysis.D (basis i) (UpShadeRt B f (x k)).f q=0 from ?_,zero_smul]; refine image_eq_zero_of_notMem_tsupport ?_; intro h; have he:= ΦboundRt B f (x k) q (Bulb.strands (Bulb.cone (Φ_T) i h)); exact r (by simpa [q] using he)
include e hz w hv G
lemma AnsonTaxRT:Integrable (ΛPaidRT p H (N:=N) V k a B f x):= integrable_finsetSum _ fun i _=> (FluxPermitRT p H G hz hv e V k a B f _ w i).const_mul _
include m
lemma handValueRt:TouchMΛ H (N:=N) V k a (wickSlice n x)=∫ s, ΛPaidRT p H (N:=N) V k a B f x s:=by
 rw[HonestWardΛL p H G hz hv e V k a m _ w,show (∫ s:ℝ,Τbill s) = ∑ i:Axis,(∫ s:ℝ, NormLRT a i* Fcost i s) from integral_finsetSum _ (fun i _=>(FluxPermitRT _ H G hz hv e V k a B f _ w i).const_mul _)]
 exact sum_congr rfl fun i _=> by rw [integral_const_mul, ← FluxPaidRT _ H G hz hv e V k a B f _ w i]; rfl
#print axioms ΨAetnaRt
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
