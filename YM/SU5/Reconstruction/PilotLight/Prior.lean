import YM.SU5.Reconstruction.PilotLight.Steady
import YM.SU5.Reconstruction.PilotLight.Landsdale
/-! Every physical test even costing receives gauge--matter expansion references. WIDE for the Early.Height tests. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted Sound
section atoms
variable {J:Calibration}{S:Finset Cover}
structure Syntax (J:Calibration)(S:Finset Cover) (g m:Dome J) : Prop where
  wide : ∃ y: PairsC→ℂ, Coeff true S y ∧ g.val=scalar J y
  choir : ∃ u: Chorus, staves u S ∧ treble u = false ∧ m.val=sing J u
variable {g m x:Dome J}
lemma Syntax.afford (p : Syntax J S g m): InTest J true S false g.val ∧ InTest J true S false m.val:=by
 obtain ⟨⟨f,u,hf⟩,⟨t,h,v,e⟩⟩:=p; exact ⟨hf.symm ▸ (InTest.seed u),e.symm ▸ (v ▸ sung J t h)⟩  -- cast confusion
lemma script_span (h:InTest J true S false x.val): x ∈ Submodule.span ℂ {p:Dome J | ∃ g m:Dome J, Syntax J S g m ∧ p=g*m } :=by
 let T:= Submodule.span ℂ {p:Dome J | ∃ g m:Dome J, Syntax J S g m∧ p=g*m }
 refine Submodule.span_induction (p:=fun q _=> ∀ x:Dome J, x.val=q → x∈ T) ?_ (fun x p=> (show (0:Dome J)=x from Subtype.ext p.symm) ▸ T.zero_mem) ?_ ?_ (Sound.whole h) x rfl
 · intro _ k; obtain ⟨f,u,h,v,t,rfl⟩:=k; let i:Dome J:=⟨scalar J f,aux_test (.seed h)⟩; let m:Dome J:= ⟨sing J u,aux_test (t ▸ sung J u v)⟩; exact fun x p=> Submodule.subset_span ⟨i,m,⟨⟨f,h,rfl⟩,⟨u,v,t,rfl⟩⟩,Subtype.ext p⟩
 · intro x y h k hx hy v p
   let i:Dome J:=⟨x,aux_test (Sound.test_span (S:=S) h)⟩; let m:Dome J:=⟨y,aux_test (Sound.test_span (S:=S) k)⟩; exact (show v=i+m from Subtype.ext p).symm ▸ T.add_mem (hx i rfl) (hy m rfl)
 intro a x h t v p; let i:Dome J:=⟨x,aux_test (Sound.test_span (S:=S) h)⟩; exact (show v=a • i from Subtype.ext p).symm ▸ T.smul_mem a (t i rfl)
end atoms

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(C:Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "Ω₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "Θ"=> doorstep Y H V G.history G.clipped j false C χ
local notation "F"=> osValue Y H V G j C χ
local notation "Os"=> OSvector Y H V G j C χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false C χ
local notation "Ps"=> Follows Y H V G j C χ
variable {x y: Dome (tent Y H)} (S:Finset Cover) (s:ℕ)(u: marks (timeMesh Λ))(r:ℝ)
local notation "Kb"=> insideAt Λ l K
/- early, temporal alignment. Passport solely a support request (no activation). Can choose v offset once after each so augmentation interpretable in this sense. r≥0 Eu future dendral. -/
structure Passport :Prop where
 cost : bufferedHull Λ l s S ⊆ Chambers.strip j r u
 high : 0<(u:ℝ)
 base : 0≤r
-- λ l not used explicitly in data? struct args
local notation "P'"=> Passport (Λ:=Λ) (l:=l) j S s u r
variable (h:Passport (Λ:=Λ) (l:=l) j S s u r)
include h
lemma admission (p:InTest K true S false x.val) : x∈ (Kb false (Chambers.strip j r u) s) := by
 exact (mem_insideAt ..).2 ⟨⟨S,p,(supported_iff ..).2 h.cost⟩,nofun⟩
lemma earnsFront (p:InTest K true S false x.val) : x∈ Kb false (Chambers.strip j 0 u) s:= insideAt_mono (U:=Chambers.strip j r u) (W:= Chambers.strip j 0 u) (fun i a=>⟨h.base.trans a.1,a.2⟩) (admission Y H j S s u r h p)
local notation "Fₚ"=> insideAt Λ l K false (Chambers.strip j 0 u) s
omit h
noncomputable def startLensMap (p:0<(u:ℝ)) : insideAt Λ l K false (Chambers.strip j 0 u) s →ₗ[ℂ] (Ω₀).Op:= by
 let A(x:Fₚ):=stripOp Y H V G j C χ u p (ticket Y H G s x.val) (ticket_mem Y H G x.property)
 have he(x:Fₚ):Ps (ticket Y H G s x.val) u (A x):= stripOp_follows Y H V G j C χ u p ..
 exact {toFun:=A,map_add':=(by
   intro x y; apply unique_op Y H V G j C χ u (he (x+y)); rw [Subalgebra.coe_add,map_add]; exact addScore Y H V G j C χ (he x) (he y)), map_smul':= (by intro r x; apply unique_op Y H V G j C χ u (he (r•x)); rw [Subalgebra.coe_smul,map_smul]; exact scaleScore Y H V G j C χ (he x) r)}
noncomputable def startLens (p:0<(u:ℝ)): Dome K →ₗ[ℂ] (indoor Y H V G.history G.clipped j false C χ).Op := (startLensMap Y H V G j C χ s u p).comp ((Fₚ).toSubmodule.subtype.leftInverse)
include h
lemma onset (p:InTest K true S false x.val) : Ps (ticket Y H G s x) u (startLens Y H V G j C χ s u h.high x):=by
 have hp:=earnsFront Y H j S s u r h p; unfold startLens; rw [LinearMap.comp_apply,show ((Fₚ).toSubmodule.subtype.leftInverse x) = ⟨x,hp⟩ from LinearMap.leftInverse_apply_of_inj (Fₚ).toSubmodule.ker_subtype (x:=⟨x,hp⟩)] -- named x ok
 exact stripOp_follows  Y H V G j C χ u h.high _ (ticket_mem Y H G hp)
omit h
-- actual housing of kets (TRUE) any
variable {t:Sky (tent Y H)}
lemma applyCell (p:t∈ D true (flank j r)) (g:0≤r) : ∃ (S:Finset Cover) (s:ℕ)(b: marks (timeMesh Λ))(x:Dome (tent Y H)), InTest K true S false x.val ∧ CovCover K x.val ∧ Passport (Λ:=Λ) (l:=l) j S s b r ∧ t= ticket Y H G s x:=by
 obtain ⟨s,q,u,rfl⟩:= p; obtain ⟨⟨S,e,v⟩,x⟩:= (mem_insideAt ..).1 u
 let A:=bufferedHull Λ l s S
 obtain ⟨b,p⟩:= ((compact_hull Λ l s S).image (continuous_apply j)).bddAbove
 obtain ⟨u,q'⟩:= reach_height (Λ:=Λ) (max r b)
 refine ⟨S,s,u,q,e,x rfl, ⟨fun x h => ⟨(supported_iff ..).1 v h,?_⟩, lt_of_le_of_lt g ((le_max_left ..).trans_lt q'),g⟩,rfl⟩
 exact le_trans (p ⟨x,h,rfl⟩) ((le_max_right ..).trans q'.le)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.onset
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.applyCell
