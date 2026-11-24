import YM.SatinExist.Faceted
import YM.SatinExist.SliceBill
set_option autoImplicit false
set_option maxHeartbeats 390000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey Six OneCup Xara
open CF.Lamour CF.Lamour.Bridge.Celeste
namespace Spine
variable (P:Spine)
local notation "W"=>P.calibration
local notation "Λ"=>P.par
local notation "Ψ"=>P.run
local notation "π"=>P.width
local notation "H"=>P.large
local notation "ℒ"=>P.law
variable (S T:Finset Cover)(s i:ℕ) (E:P.Test→ₗ[ℂ]ℂ)(r:MatterWard P.calibration E)
local notation "m" i:max=> momentm Ψ (P.nomadic i) (s+1)
local notation "U!" S:max=> wingspan Λ π S
local notation "Σ" F:max=> slice W E F
local notation "ℳ" i:max=> side Ψ (P.nomadic i) s
local notation "t" i:max=> side Ψ (P.nomadic i) (s+1)
local notation "τ" i:max F:max=> distribute Ψ H (s+1) (P.nomadic i) F
open Hierarchy
open CF.Lamour.Bridge.Celeste.SpotP
variable (a c:Cover)(A B:GemUT)(z:ℝ) (p:nodeC a∈ S)(l:nodeC c∈ T)(d:Navy.Sizing P.par s)(q:Disjoint (wingspan P.par P.width S) (wingspan P.par P.width T))(v:0<z)
local notation "Fi"=>sheen W a A
local notation "Gi"=>sheen W c B
def duoMask (s:ℕ)(F G:P.Test):P.Test:= P.conveying s 1 F * P.conveying s 1 G
-- compare budget
variable (h:∀ x:Cover,nodeC x∈wingspan P.par P.width S→∀ y:Cover,nodeC y∈wingspan P.par P.width T→∀ J Q:GemUT, ‖E (sheen P.calibration x J*sheen _ y Q)‖≤ z)
def Recommend := 25 * DiamondX+1
lemma normRpos:0< Recommend:= by unfold Recommend; have hp:= diaPlus; positivity
local notation "φ" a:max => slice W E a
include h v r p l q d
lemma socorro : P.EvSmall (s+1) (((Recommend*z:ℝ):ℂ)⁻¹ • (φ (P.duoMask s Fi Gi))):=by
 let Q:= U! S∪ U! T
 let X:= P.duoMask s Fi Gi
 let G(i:ℕ):P.Test:= P.grown s i S Fi* P.grown s i T Gi
 have hg:= (P.shippingStd S s Fi (shine_local W S a A p)).multiply (P.shippingStd T s Gi (shine_local W T c B l))
 have hv:= P.cutsave Q E G X hg -- tune
 let η:= Recommend*z; have hη:0<η:=mul_pos normRpos v
 let w':P.Test:= ((↑η:ℂ)⁻¹) • (Σ X)
 have he:= ((P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop).eventually (turning Ψ H (s+1) Q)
 filter_upwards [he,hv.saved z v,P.doubts S T s E r a c A B z p l d v.le q h] with i hr hp e
 intro V; let U:=portLX Ψ H (s+1) (P.nomadic i) V
 obtain ⟨I,t'⟩:=examinator (Y:=Ψ) H Q (s+1) _ E hr.hosp
 let Y:= I (U X); have hy: U (Σ X) = Y • 1:= termBy (Y:=Ψ) H Q (s+1) _ E I t' hg.landing V
 let k:ℂ:= (↑η:ℂ)⁻¹
 refine ⟨k*Y,?_,?_⟩
 · change U w'= _; rw [show w'= k • _ from rfl,map_smul, hy,smul_smul]
 rw [norm_mul,show ‖k‖=η⁻¹ from (by unfold k; rw [norm_inv,Complex.norm_real, Real.norm_eq_abs,abs_of_pos hη])]
 have hz: ‖(τ i ((Σ X).val)) V‖= ‖Y‖:=by change ‖U _‖=_; rw [hy,norm_smul,norm_one,mul_one]
 obtain ⟨a,e,h'⟩:=e V; have hl: ‖U (Σ (G i))‖ ≤25*DiamondX*z:=by change ‖distribute _ _ _ _ _ _‖ ≤ _; rw [e,norm_smul,norm_one,mul_one]; exact h'
 have hu: ‖U (Σ (G i))-U (Σ X)‖≤ z:= by rw [← map_sub]; change ‖ship _ _ _‖≤ _; exact send_le (terrain Ψ H _ _) _ z (hp _) _ -- tune
 have hb: ‖U (Σ X)‖ ≤ η:=by
    have h:= norm_le_norm_sub_add (U (Σ X)) (U (Σ (G i))); rw [norm_sub_rev] at h; unfold η Recommend; change _ ≤ _ at hu; nlinarith only [hl,h,hu]
 change ‖U (Σ X)‖=‖Y‖ at hz; rw [hz] at hb
 exact (mul_le_mul_of_nonneg_left hb (inv_pos.mpr hη).le).trans_eq (inv_mul_cancel₀ hη.ne')
where send_le {x y:Side}(p:x=y)(q:Mark x)(z:ℝ)(w:∀ V, ‖q V‖≤z)(v:Fields y): ‖ship p q v‖≤z:=by subst y; exact w _
omit h v r p l q d
open Ballad Ballad.Chalice -- tune
lemma shine_kept (a:Cover)(A:GemUT) : sheen P.calibration a A∈ enclave W:=by
 let V:= audience a (stoneOf A) 1; have hz:-P.tuneK V=sheen P.calibration a A:=by
    apply Subtype.ext; funext U; change -Wort a (stoneOf A) 1 (P.calibration.c U)=_; rw [goldletter]; unfold Twah.gold; simp
 rw [←hz]; exact (enclave W).neg_mem (P.celebrity V)
variable (y:P.Spectrum0 3)
def LLz (P:Spine)(S:Finset Cover)(s:ℕ)(x:P.Spectrum0 3):Prop:=∀ F:P.Test, F∈enclave P.calibration → F∈bay _ S true →P.EvSmall s F→ ‖P.singleState 3 s x F‖ ≤ Real.sqrt (RedD+3)
local notation "W!"=> P.singleState 3 (s+1) y
include h v r p l q d
lemma liberty (he:E = P.singleState 3 (s+1) y)(h':LLz P (U! S ∪ U! T) (s+1) y)(L:P.Test→ₗ[ℂ]ℂ)(F:Comparison W E L) : ‖L (P.duoMask s Fi Gi)‖ ≤ Recommend*z*Real.sqrt (RedD+3):=by
 subst E; let V:= P.duoMask s Fi Gi; let U:=slice W W! V; let η:= Recommend*z; let k:ℂ:= (η:ℂ)⁻¹; have hη:0<η:=mul_pos normRpos v
 let J:= k • U; let N:=enclave P.calibration; have hb: J∈N:= N.smul_mem (slicing_enclave r V (N.mul_mem (P.refine_keeps _ _ (P.shine_kept _ _) _) (P.refine_keeps _ _ (P.shine_kept _ _) _))) k -- order args
 let M:=U! S ∪ U! T; let D:=bay W M true
 have hp: J∈D:=D.smul_mem (cuts_local W! M V ((P.shippingStd S s Fi (shine_local W S a A p)).multiply (P.shippingStd T s Gi (shine_local W T c B l))|>.landing)) k
 have hx:= h' _ hb hp (P.socorro S T s W! r a c A B z p l d q v h); -- tune
 rw [OneCup.slicing F]; let A':= W! U; rw [show J=k • U from rfl,map_smul] at hx -- expandable hm
 change ‖k • A'‖ ≤ _ at hx
 rw [norm_smul, norm_inv,Complex.norm_real, Real.norm_of_nonneg hη.le] at hx; change ‖A'‖ ≤ η*_
 calc
    _ ≤ η*(η⁻¹ * ‖A'‖):=le_of_eq (by rw [←mul_assoc,mul_inv_cancel₀ hη.ne',one_mul]) -- tune
    _ ≤ _ := mul_le_mul_of_nonneg_left hx hη.le
#print axioms liberty
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
