import YM.SU5.Selected.Euro.Plume
import YM.SU5.Selected.Euro.Mingle

/-!
# Singlet probes (Dome level-wide) suffice for ALL vectors in unselected H, all phase
words and selected states. Includes relations between neutral and general marked algebra.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)

open Tapestry
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false

namespace Palate
open YM.CF.Pannier.Chancel
open Ether Mingle
variable (s:ℕ)
local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "L₀" s:max => prepare Y H V Q Qc j false C s
local notation "L" => basisRoom Y H V Q j false C
local notation "P" => pipeline Y H V Q Qc j false C
local notation "M" s:max => liftCap Y H V Q Qc j false C s
local notation "Fₛ" s:max => asLeg Y H V Q Qc j false C s

section invoice
include V Q C Qc
variable {x : Type*} [MeasurableSpace x] {μ:Measure x} [IsProbabilityMeasure μ]
variable {S T:Finset Cover} {w:x→Family (tent Y H)}
-- registered support in future slab. Any positive buffers are real.
omit V Q C Qc in
lemma region_apart (h:Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S)(k:Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ T) : Disjoint S (reflectedBox j 0 T) := by
 refine Finset.disjoint_right.mpr (fun i t z=>?_); obtain ⟨x,f,rfl⟩:=mem_image.mp t
 rw [area0] at h k; specialize k _ f; specialize h _ z; rw [reflected_coord] at h; have hh:0 < (K).ℓ:= margin_good ..; omega
lemma warmly_leg (f f':F₊ s) (p:∀ g, ∃ u: Cover→SU.E,Circular S u f.val (w g))(u:Warm μ K w f'.val) (e: InTest K true S false f.val) (e': InTest K true S false f'.val) (h:Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) : (φ s) f= (φ s) f':= by
 have he(x:F₊ s) : inner ℂ ((φ s) x) ((φ s) f - (φ s) f')=0:= by
    obtain ⟨T,t,v⟩:= ((purpose_ok ..).1 x.property).1; rw [inner_sub_right,stems Y H V,stems Y H V,area0]; exact sub_eq_zero.mpr (E_admit Y H V s (region_apart Y H j s h v) p u e e' (axial K j 0 t))
 apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw [inner_sub_left,he,he,sub_self]
lemma before_ready {f f': (P)}(e:f.val Ω=f'.val Ω) : f=f':= by
 let U:P:=f-f'; let y:B:=⟨U.val.adjoint.comp U.val,owns_each Y H V Q Qc j false C U U⟩
 have ht : U.val Ω=0:=sub_eq_zero.mpr e -- may need change
 have h:y=0:= distinguish Y H V Q Qc j false C _ _ (by change U.val.adjoint (U.val Ω)=0; rw [ht,map_zero])
 apply sub_eq_zero.mp; apply Subtype.ext; show U.val=0; ext1 p; change U.val p=0; rw [← inner_self_eq_zero (𝕜:=ℂ),←ContinuousLinearMap.adjoint_inner_left]; change inner ℂ (y.val p) p=0; rw [h]; change inner ℂ (0:(R)) p=0; simp -- 0 subtype 
-- exact neutrality on *support-local* (no other presentations assumed); refinement by supply
-- pointwise at resolution, leg as approximated atom (if need unbounded geometry prices elsewhere)
lemma available {s':Side} (p:Hosp S ((K).c s')) (f:Swatch S): -- need s'
    let z:=fun i=>render S K (ocelli K S (repeats ((K).c s') i) f)
    (∀ i, InTest K true S false (z i) ∧ ∃ u,Circular S u (render S K f) (z i)) ∧ Warm (domeLaw _) K z (render S K (naturalHue K S s' p f)) := by
 intro z; exact ⟨fun i=>⟨texture ..,_,decorates K S _ f⟩,fun k=>⟨manyHue K S s' p f k,funext (allPrint K S s' p f k)⟩⟩

variable {s':Side} (p:Hosp S ((tent Y H).c s'))(f:Swatch S) -- move before
local notation "ν" => naturalHue (tent Y H) S s' p f
local notation "FΨ" h:max => atomField Y H j s S h
lemma neutral_leg (h: Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) : (Fₛ s) ((FΨ h) f) = (Fₛ s) ((FΨ h) ν) := by
 obtain ⟨a,b⟩:= available Y H V Q Qc j C p f -- check omit
 apply before_ready Y H V Q Qc j C; exact (planted Y H V Q Qc j false C s _).trans ((warmly_leg Y H V Q Qc j C s ((FΨ h) f) ((FΨ h) ν) (fun i=> (a i).2) b (texture ..) (texture ..) h).trans (planted Y H V Q Qc j false C s _).symm)

-- cap identity support same S even before move; need leg for moved. using Warm.move
abbrev atomObs (K':Calibration)(S:Finset Cover)(x:Swatch S):Vacancy.observable K' false:=⟨render S K' x,aux_test (texture S K' x),fun p=>by cases p⟩
lemma hue_cap : (M s) (atomObs K S f) = (M s) (atomObs K S ν):= by
 obtain ⟨z,w⟩ := canStart Y H j s S
 let x:=atomObs K S f; let x' := fromCover Y H j false s z x (texture S K f) w
 let y:=atomObs K S ν; let y' := fromCover Y H j false s z y (texture S K ν) w
 obtain ⟨a,b⟩:= available Y H V Q Qc j C p f
 have he:(φ s) x'=(φ s) y':=warmly_leg Y H V Q Qc j C s x' y' (fun i=>by
    obtain ⟨U₁,g⟩:=(a i).2; exact ⟨_,relocate_gauge j S U₁ z g (a i).1⟩) (b.move j z) (flow_port K j _ (texture S K f)) (flow_port K j _ (texture S K ν)) w
 apply distinguish Y H V Q Qc j false C
 exact (cap_via_actor Y H V Q Qc j false C s x z x' rfl).trans ((congrArg π₀ he).trans (cap_via_actor Y H V Q Qc j false C s y z y' rfl).symm)
end invoice

local notation "rF" s:max => Tower.Field Y H s j 0 true
local notation "TestOnly" => Vacancy.observable (tent Y H) true
-- maps to all. Linear as needed. Preserves support and unread Mark data.
def dash : rF s→ₗ[ℂ] F₊ s where
 toFun x:= ⟨x.val, (show _ from (purpose_ok ..).mpr ⟨((purpose_ok ..).mp x.property).1,fun p=>by cases p⟩)⟩
 map_add' x y:= rfl
 map_smul' z x:= rfl
local notation "d" s:max => dash Y H j s
abbrev feel (x:TestOnly) : Test := ⟨x.val,x.property.1,fun p=>by cases p⟩
local notation "fₑ" => feel Y H
lemma reach (x: rF s) : fₑ (toTest Y H j true s x)= toTest Y H j false s ((d s) x):= rfl
lemma glint (x:TestOnly) : Neutral K x.val:= x.property.2 rfl

include V C Qc
lemma taste (x:F₊ s) (S:Finset Cover) (t:InTest K true S false x.val)(h: Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) : ∃ y:rF s, InTest K true S false y.val∧ (Fₛ s) ((d s) y)= (Fₛ s) x := by
 obtain ⟨f,v⟩:= rendered S K t; obtain ⟨s',p⟩:= (separates K S).exists; let u:= naturalHue K S s' ⟨p⟩ f; let f':=render S K u; have ht:= texture S K u
 let y:rF s:=⟨f',(show _ from (purpose_ok ..).2 ⟨(show _ from ⟨S,ht,h⟩),fun _=>hue_neutral K S s' ⟨p⟩ f⟩)⟩
 exact ⟨y,ht,(neutral_leg Y H V Q Qc j C s (s':=s') (S:=S) ⟨p⟩ f h).symm.trans (congrArg (Fₛ s) (Subtype.ext v))⟩ -- order
lemma tastes (x:F₊ s) : ∃ y:rF s, (Fₛ s) ((d s) y)=(Fₛ s) x:=by obtain ⟨S,t,p⟩:= ((purpose_ok ..).1 x.property).1; obtain ⟨y,g,h⟩:= taste Y H V Q Qc j C s x S t p; exact ⟨y,h⟩
-- every chosen distribution on Spectrum restricts to a normalized allowance on singlet resolution positive marks and PCs; proof on one axis here Dense.
lemma cap_approach (x:Test) (S:Finset Cover) (t:InTest K true S false x.val):∃ y:TestOnly, InTest K true S false y.val ∧ (M s) (fₑ y)= (M s) x:=by
 obtain ⟨f,v⟩:= rendered S K t; obtain ⟨s',p⟩:= (separates K S).exists; let ν:= naturalHue K S s' ⟨p⟩ f; let f':=render S K ν; have ht:= texture S K ν
 exact ⟨(⟨f',aux_test ht,fun _=> hue_neutral K S s' ⟨p⟩ f⟩: TestOnly),ht,(hue_cap Y H V Q Qc j C s (S:=S) (s':=s') ⟨p⟩ f).symm.trans (congrArg (M s) (Subtype.ext v))⟩
lemma single_legs : LinearMap.range ((Fₛ s).comp (d s))=LinearMap.range (Fₛ s):= le_antisymm (by rintro _ ⟨t,rfl⟩; exact ⟨_,rfl⟩) (fun _ g=>by
 obtain ⟨t,rfl⟩:=g; exact tastes Y H V Q Qc j C s t)
lemma already (m:ℕ) (x : P) : ∃ (s':ℕ)(g: rF s'), m≤ s'∧ (Fₛ s') ((d s') g)=x:=by obtain ⟨t,y,v,h⟩:=leg_available Y H V Q Qc j false C x m; obtain ⟨g,e⟩:= tastes Y H V Q Qc j C t y; exact ⟨t,g,v,e.trans (Subtype.ext h.symm)⟩
lemma prices_migrate (t:ℕ)(ν:s≤t)(x:rF s): (Fₛ t) ((d t) (Raise Y H Q.circuit j 0 true s t ν x))= (Fₛ s) ((d s) x):=by
 rw [show (d t) _= Raise Y H Q.circuit j 0 false s t ν ((d s) x) from Subtype.ext ?_, common_leg]
 -- need lemma Raise data. maybe rfl
 first| rfl | exact ?_
end Palate
end YM.CF.Buffered.Afterglow.Tower.Selection
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Palate
#print axioms glint
#print axioms hue_cap
#print axioms neutral_leg
#print axioms taste
#print axioms already
#print axioms prices_migrate
end YM.CF.Buffered.Afterglow.Tower.Selection.Palate
