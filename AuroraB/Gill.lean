import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
local notation "ℑ"=> (3:Axis)
local notation "ε" s=>P.macroStep s
-- forward positive shift
abbrev shuf (A:SampleDose)(h:ℝ):=dealt A (-aislePt ℑ h)
lemma shufPay(A:SampleDose)(b:A.Normalized)(h:ℝ): (shuf A h).Normalized:= ⟨fun _=>b.1 _,(integral_add_right_eq_self ..).trans b.2⟩
lemma shuf_iff (A:SampleDose)(h:ℝ)(x:Vantage):x∈tsupport (shuf A h).val ↔ x-aislePt 3 h ∈ tsupport A.val:=by
 rw [show tsupport (shuf A h).val=(Homeomorph.addRight (-aislePt 3 h)) ⁻¹' tsupport A.val from ((Homeomorph.addRight (-aislePt 3 h)).preimage_closure (Function.support A.val)).symm]
 change x+ -(aislePt 3 h) ∈ tsupport A.val ↔ _; rw [sub_eq_add_neg]
lemma star_iff (A:SampleDose)(h x:Vantage) : x∈tsupport (dealt A h).val ↔ x+h ∈ tsupport A.val:=by rw [show tsupport (dealt A h).val=(Homeomorph.addRight h)⁻¹' _ from ((Homeomorph.addRight h).preimage_closure (Function.support A.val)).symm]; rfl
lemma shuf_add (A:SampleDose)(a b:ℝ):shuf (shuf A a) b=shuf A (a+b):=by
 obtain ⟨f,q,h⟩:=A; unfold shuf dealt; congr 1; funext i; apply congrArg f; ext j; by_cases v:j=ℑ<;>simp [aislePt,v,Pi.single_eq_of_ne]; ring
lemma shuf_base(A:SampleDose) : shuf A 0=A:=by obtain ⟨f,q,h⟩:=A; unfold shuf dealt; congr 1; ext i; change f _= f i; congr; ext j; by_cases v:j=ℑ<;>simp [aislePt,v,Pi.single_eq_of_ne]
lemma location (i:Axis) (h:ℝ): aislePt ℑ h i= if i=3 then h else 0:= by by_cases v:i=3<;> simp [aislePt,v,Pi.single_eq_of_ne]
lemma location₁(h:ℝ): aislePt ℑ h 3=h:=by rw [location]; rfl
lemma location_h(h:ℝ)(v:0 ≤ h)(j:Axis):|aislePt ℑ h j| ≤ h:=by rw [location]; split_ifs <;> simp [abs_of_nonneg v,v]
-- lattice ratio and sample reindex
variable (P)
def cursor(s t:ℕ):Cover:=fun j=> if j=3 then ((P.par.R.L.val^(t-s):ℕ):ℤ) else 0
lemma verse(s t:ℕ)(h:s≤t)(i:Cover): P.meshPose t (i+cursor P s t)=P.meshPose t i+aislePt ℑ (P.macroStep s):=by
 have hp:P.macroStep t=(P.spotMesh t):=rfl
 have hx: ((P.par.R.L.val:ℝ)^(t-s))*P.macroStep t=P.macroStep s:= by
    unfold macroStep mill; rw [NNReal.coe_div,NNReal.coe_div]; push_cast; let L:=(P.par.R.L.val:ℝ); change L^(t-s)*(_/L^t) = _/L^s
    have he:L^t=L^s*L^(t-s):=by rw [← pow_add,Nat.add_sub_of_le h]
    have hl:0<L:=by unfold L; exact_mod_cast P.par.R.L.property
    rw [he]; field_simp
 funext j; change P.gridSpot t _ j = P.gridSpot t _ j+ _; simp_rw [P.gridSpot_mul,←hp,location,Pi.add_apply,Int.cast_add, cursor]; by_cases v:j=3 <;> simp only [v,↓reduceIte,Int.cast_zero,add_zero, Nat.cast_pow,add_mul]; push_cast; rw [hx]
lemma beams(F:SampleDose)(s t:ℕ)(h:s≤t)(r:Vantage)(i:Cover):
 P.activation t (dealt (shuf F (P.macroStep s)) r) (i+cursor P s t) = P.activation t (dealt F r) i:=by
 have he:=verse P s t h i; unfold activation shuf dealt; rw [he]; dsimp only; rw [show P.meshPose t i + aislePt ℑ (P.macroStep s) + r + -aislePt ℑ (P.macroStep s)=P.meshPose t i +r from by abel]
lemma fore(F:SampleDose)(s t:ℕ)(h:s≤t)(r:Vantage):
 P.usedGrid t (dealt (shuf F (P.macroStep s)) r)= (P.usedGrid t (dealt F r)).map (Equiv.addRight (cursor P s t)).toEmbedding :=by
 apply Finset.ext; intro i
 have he:= verse P s t h (i-cursor P s t)
 rw [P.usedPose,star_iff,shuf_iff]; rw [sub_add_cancel] at he; rw [he,show P.meshPose t (i-cursor P s t)+aislePt ℑ (P.macroStep s)+r- aislePt ℑ (P.macroStep s)=P.meshPose t (i-cursor P s t)+ r from (by abel),←star_iff,←P.usedPose]
 rw [Finset.mem_map]
 constructor
 · intro p; exact ⟨_,p,sub_add_cancel _ _⟩
 rintro ⟨j,p,rfl⟩; change (j+cursor P s t)-cursor P s t ∈ _; rwa [add_sub_cancel_right]
#print axioms verse
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
