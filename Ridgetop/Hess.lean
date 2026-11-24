import Ridgetop.Flower
import Ridgetop.Catalog
import Ridgetop.Wicks
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
namespace Ridgetop
variable (H)
abbrev East(n:Side):Matrix (Body 1 n) (Body 1 n) ℝ:=Precision.K (H.metric.acts n)
local notation "δH"=> East H n
abbrev port_price(a b: form 1 n):ℝ:=dotProduct a (δH *ᵥ b)
abbrev Vectorable (j: form 1 n):Prop:=∃ z:form 1 n,δH *ᵥz=j
noncomputable def answer (j:form 1 n): form 1 n:=if h:Vectorable H j then h.choose else 0
lemma answered(j:form 1 n)(h:Vectorable H j): δH *ᵥanswer H j=j:=by rw [answer,dif_pos h,h.choose_spec]
/-- one-color covariance east ordering -/
abbrev finger (i j:form 1 n):ℝ:=dotProduct i (answer H j)
variable {H}
include L
lemma sgV(a b:form 1 n):port_price H a b=port_price H b a:=by
 have he:(δH).transpose=δH:=by unfold East Precision.K; simp only [Matrix.transpose_mul,L.symmetric.1,Matrix.transpose_transpose,Matrix.mul_assoc]
 exact ((congrArg (fun x=>dotProduct a (x *ᵥ b)) he).symm.trans (dotProduct_transpose_mulVec (δH) a b))
lemma finger_wr {i j:form 1 n}(hi:Vectorable H i){z:form 1 n}(he:δH *ᵥz=j): finger H i j = dotProduct i z:=by
 let x:=answer H i; have hx:δH *ᵥx=i:= answered H _ hi
 unfold finger; rw [←hx,dotProduct_comm,_root_.dotProduct_comm _ z]; exact (sgV L _ _).trans ((congrArg (dotProduct x) ((answered H j ⟨_,he⟩).trans he.symm)).trans (sgV L _ _))
lemma weave_pos(o:Site n)(i:PlaqAxes)(g:0<δ): Vectorable H (loadM o i):= _root_.Factory.milk _ _ L.symmetric.1 g (fun i=> L.uniform.1 i|>.1) _
-- bilinear on raw via polarization
lemma gauge_core(a b:fieldDir G n 1): inner ℝ (tiler B P a) (tiler B P b) =∑ j:G.ColorIndex, port_price H (parts G 1 a j) (parts G 1 b j):=by
 have he(j:G.ColorIndex): parts G 1 (a+b) j=parts G 1 a j+parts G 1 b j:=rfl
 have h0:=face_map B P L (a+b); rw [map_add,norm_add_sq_real,face_map B P L _,face_map B P L _] at h0; unfold Bid.gaugeFiscal at h0; simp_rw [he,add_dotProduct,Matrix.mulVec_add,dotProduct_add,show ∀ j:G.ColorIndex,dotProduct (parts G 1 b j) (Precision.K (H.metric.acts n)*ᵥ parts G 1 a j)=_ from (fun j=> (show port_price H (parts G 1 b j) (parts G 1 a j)=port_price H (parts G 1 a j) (parts G 1 b j) from sgV L _ _)),Finset.sum_add_distrib] at h0
 unfold port_price East at *; linarith only [h0]
abbrev trunkR(o:Site n)(i:PlaqAxes):form 1 n:=answer H (loadM o i)
abbrev quench(o:Site n)(i:PlaqAxes)(j:G.ColorIndex):fieldDir G n 1:=fun e=> WithLp.toLp 2 (Pi.single j ( (@trunkR n H o i : form 1 n) e))
noncomputable abbrev fibreR(o:Site n)(i:PlaqAxes)(j:G.ColorIndex):stamen B P n:=(tiler B P).rangeRestrict (quench (H:=H) o i j)
lemma quench_coord(o:Site n)(i:PlaqAxes)(j h:G.ColorIndex): parts G 1 (@quench n G H o i j) h=if h=j then trunkR (H:=H) o i else 0:=by funext k; unfold parts quench trunkR; split_ifs with p; subst h; simp; simp [Pi.single_eq_of_ne p]
-- fibreR represents heeled on stamen all; no meas cost here
open _root_.Factory
open scoped RealInnerProductSpace
variable (o:Site n)(i:PlaqAxes)(j:G.ColorIndex)(hx:0 <δ)
include B P L hx
lemma interests (x:stamen B P n): heeled (q:=q) o i x.val j= webV (fibreR B P o i j) x:=by
 obtain ⟨z,hz⟩: ∃ z:fieldDir G n 1,(tiler B P) z=x.val:= x.property
 rw [show x=(tiler B P).rangeRestrict z from Subtype.ext hz.symm]; change heeled _ _ (tiler B P z) j=inner ℝ (tiler B P (quench (H:=H) o i j)) (tiler B P z)
 rw [heeled_tiler,estate_tick,gauge_core B P L]; simp_rw [quench_coord L]; rw [Finset.sum_eq_single j]; rw [if_pos rfl]
 unfold trunkR; rw [sgV L]; unfold port_price; rw [answered H _ (weave_pos L o i hx)]; exact dotProduct_comm _ _
 · -- bullet issue. to solve aux below order. sum_eq_single creates goals after current.
   intro p _ hp; rw [if_neg hp]; exact zero_dotProduct _ -- tune
 simp
lemma accounts(b:Site n)(y:PlaqAxes)(k:G.ColorIndex): ⟪fibreR B P o i j,fibreR B P b y k⟫=(if j=k then finger H (loadM o i) (loadM b y) else 0):=by
 change webV (fibreR B P o i j) (fibreR B P b y k)=_; rw [←interests B P L o i j hx]; change heeled _ _ (tiler B P (quench (H:=H) b y k)) j=_
 rw [heeled_tiler,estate_tick,quench_coord L]; split_ifs <;> simp [finger,trunkR]
/-- scalar squared.D -/
lemma fibre_pair (b:Site n)(y:PlaqAxes)(k:G.ColorIndex): (∫ x:stamen B P n,(@heeled n _ q o i x.val j)^2 * (@heeled n G q b y x.val k)^2 ∂ stdGaussian (stamen B P n))=(finger H (loadM o i) (loadM o i))*finger H (loadM b y) (loadM b y)+ (if j=k then 2*finger H (loadM o i) (loadM b y)^2 else 0) :=by
 simp_rw [interests B P L _ _ _ hx, wick,← real_inner_self_eq_norm_sq]; simp_rw [accounts B P L _ _ _ hx]; split_ifs <;> simp
#print axioms gauge_core
#print axioms fibre_pair
end Ridgetop
end Risa
end YM.Gleam.Luster
