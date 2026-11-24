import YM.SatinExist.LineTests
import YM.SatinExist.Ferrite
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 340000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open _root_.YM.SatinExist Lancet
namespace Spine
open Six Xara Aria Casting
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)(s:ℕ)
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Φ"=> P.singleState 3 s x
local notation "Λ"=> P.par
local notation "R"=> P.par.R.L.val
local notation "Z"=> reserve P.par P.width
variable (D:P.Test→ₗ[ℂ] ℂ)(h:Comparison P.calibration (P.singleState 3 (s+1) x) D)
variable {S T:Finset Cover} (F G:P.Test)(k:ℤ){U V:Finset Axis}
local notation "U!" S:max=>wingspan Λ P.width S
abbrev hostX := P.conveying s 1
local notation "sc" x:max => P.shifts j x
lemma hostMove (z:ℤ) : P.hostX s (P.shifts j z F)=P.shifts j (R*z) (P.hostX s F):=by
 rw [←P.halfDouble,←P.halfDouble]; apply Subtype.ext
 change stream Y H P.projection.refine s 1 (chime (tent Y H) j (gaugeShift P.par.block (2*z)) F.val)=chime _ j (gaugeShift P.par.block (2*((R:ℤ)*z))) (stream Y H P.projection.refine s 1 F.val)
 rw [chime_X P.run P.large P.law s j _ P.history.circuit ((marque ..).1 F.property)] -- tune parameter lists; halfDouble occurrences careful
 congr 2; ring
include j in
lemma through_past (p:F∈bay K S true)(q:G∈bay K T true)(e:0≤k)(t:Punctus (P:=P) false U k S)(v:Punctus (P:=P) true V k T) : P.hostX s (F*G)=P.duoMask s F G:=by
 let A:= P.reflectTest j F; have ha:A∈bay K (reflectedBox j 0 S) true:= P.canFlip S j p
 have hp:region j 0 Z (reflectedBox j 0 S):=by
    intro x g; obtain ⟨w,g,h⟩:= reflect_stays j 0 S g; rw [h,if_pos rfl]; have u:=t w g j; simp only [Bool.false_eq_true,ite_false] at u; change 0+ (P.calibration.ℓ:ℤ) ≤ _; split at u<;> omega
 have hv:region j 0 Z T:=by intro x g; have h:= v x g j; simp only [ite_true] at h; change 0+ (P.calibration.ℓ:ℤ) ≤ _; split at h<;>omega
 have hx:= P.conveys_form j s 1 ha q hp hv; have hA: P.reflectTest j A=F:=aureoleTwice ..; rw [show aureole K j 0 A=F from hA, mul_zero] at hx; unfold hostX duoMask; refine hx.trans (congrArg (fun a=> a*P.hostX s G) ?_); apply Subtype.ext
 rw [←hA]
 change mirror (tent Y H) j 0 (stream Y H P.projection.refine s 1 A.val)= stream Y H P.projection.refine s 1 (mirror (tent Y H) j 0 A.val); rw [stream_flipped Y H P.history.circuit s 1 j 0 ((marque ..).1 A.property),mul_zero]
lemma unitsWing (e:0 ≤ k)(t:Punctus (P:=P) false U k S)(q:Punctus (P:=P) true V k T) : Punctus (P:=P) true ∅ 0 (U! T) ∧ Punctus (P:=P) false ∅ 0 (U! S) := by
 let ρ:=R*gross (aliasLaw Λ) (distanceLaw P.width) P.par.R.J; have hR:0<R:=P.par.R.L.property; have he: (Z:ℤ)+1+ρ≤(R:ℤ)* (Z:ℤ) :=by exact_mod_cast width_margin Λ P.width
 constructor
 · intro x g a
   obtain ⟨y,v,G⟩:=mem_biUnion.mp g; obtain ⟨y,u₀,rfl⟩:=mem_image.mp v; obtain ⟨z,h,rfl⟩:= mem_image.mp G
   have h:= (box_test.mp h).1 a; have hv: (Z:ℤ)< y a:=by change (P.calibration.ℓ:ℤ) < _; have hx:=q y u₀ a; simp only [ite_true] at hx; split at hx<;>omega
   change (if true=true then (Z:ℤ)+(if a∈(∅:Finset Axis) then (0:ℤ) else 0)< _ else _); simp only [Finset.notMem_empty,ite_true,ite_false,add_zero]; change (Z:ℤ)< z a+(R:ℤ)* (y a); change -(ρ:ℤ) ≤ _ at h; nlinarith
 intro x g a
 obtain ⟨y,v,G⟩:=mem_biUnion.mp g; obtain ⟨y,u₀,rfl⟩:=mem_image.mp v; obtain ⟨z,h,rfl⟩:= mem_image.mp G
 have h:= (box_test.mp h).2 a; have hv: y a < -(Z:ℤ):=by change _ < -(P.calibration.ℓ:ℤ); have hx:=t y u₀ a; simp only [Bool.false_eq_true,ite_false] at hx; split at hx<;>omega
 simp only [Finset.notMem_empty, Bool.false_eq_true,ite_false, add_zero, neg_zero]; change z a+(R:ℤ)* (y a)+(Z:ℤ)<0; change _ ≤ (ρ:ℤ) at h; nlinarith
include h
lemma seasonFwd (p:F∈bay K S true)(q:G∈bay K T true)(e:0≤k)(t:Punctus (P:=P) false U k S)(v:Punctus (P:=P) true V k T) : ChargesX (fun i:ℕ=> D (P.duoMask s F ((sc (i:ℕ)) G))):=by
 obtain ⟨Z',H'⟩:=P.unitsWing k e t v
 let A:=U! S; let Q:=U! T; let f:=P.hostX s F; let g:=P.hostX s G
 have hp:f∈bay K A true:= (P.shippingStd S s F p).landing; have he:g∈ bay K Q true:=(P.shippingStd T s G q).landing
 let h':= P.costSplitX x j (s+1) A Q _ _ D h hp he (le_of_eq (rfl:(0:ℤ)=0)) H' Z' R P.par.R.L.property
 apply (Eq.mp ?_ h'); apply congrArg ChargesX; funext i; change D (f* _)= D (f * P.hostX s (P.shifts j (i:ℤ) G)); rw [hostMove]; norm_cast -- tune
lemma seasonTrade (z:ℤ): D (P.duoMask s (P.shifts j z F) G) = D (P.duoMask s F (P.shifts j (-z) G)):=by
 change D (P.hostX s _ * P.hostX s _)=D (P.hostX s _* P.hostX s _)
 rw [hostMove P j, ← P.stamp_comparison x j (s+1) D h (_ * _) ((R:ℤ)* -z),map_mul,P.shifts_sum,show (R:ℤ)* -z+R*z=0 from (by ring), P.shifts_zero,P.hostMove]
omit h
#print axioms seasonTrade
#print axioms seasonFwd
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
