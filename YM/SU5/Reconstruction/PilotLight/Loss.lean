import YM.SU5.Reconstruction.PilotLight.Prefix
/-! The other spectator always online. For illumination, interest also genuine.
Consider these as physical *position* claims, no time-step costs across different Spin frames. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 370000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Lat Fock
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "Ω₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "Θ"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "Os"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Ps"=> Follows Y H V G j (c j) χ
local notation "Sₚ"=> splice Y H V G j (c j) χ
variable (s t w n:ℕ) (u : marks (timeMesh Λ)) (S:Finset Cover) (r δ:ℝ)(p:placement Λ)
local notation "B₁" => alcove (hAll Λ t w n)
local notation "Σ" => bufferedHull Λ l s S
local notation "O" => slides (coordinates Λ p) (alcove (hAll Λ t w n))
variable {x y:Dome (tent Y H)}(t1:0<w)(t2:0<n)
variable (T:Finset Cover){q:ℕ} (a:Fin q → Cover) (z:SU.Slot)
local notation "Z"=> salute Y H G s t p
/- Thinking about solving the momentum price task on interacted probes only.
 Explicit comparison for Wide EARLY: every time compare costs, would have this meaning.
 No calling earlier g-pure AT Senate the first field only (still allows joint pair gauge).
 Factorization tested in the indicated CP1 inquiry--so can pin different heights,
 NO requirement that lifting them maintains any factorization into Gauge-Matter.
 Test every such `Θ[(EARLY gx) & (Late φ)] * [(EARLY gx) & (Late φ)]` with
 its own purported G/M marginals paid at those exact aperture prices. Also `φ` as
 funded AT cliques. This does not say terms `g,m` of either type are themselves
 local gauge-invariant, don't use `Region with floor Mink value` without Lens
 analytic calibration etc later. Doesn't require a Mink lift here, just actual law.
 These are nonfactorizing probe investigations of EXACT same type CP1, now multi.
 Includes price inside Physics units where required.
-/
section loss
variable (h:ReadySet (l:=l) j s u S r δ p)(σ:0<δ)
local notation "GN"=> historyGram Y H V G j c χ s t w n u p h.buys.high t1 t2
local notation "Gb"=> witnessedKet Y H V G j c χ s t w n u p h.buys.high t1 t2
def lostCause (hk:0<(u:ℝ))(t1:0<w)(t2:0<n): Prop :=
   ∀ (g m e f: Dome (tent Y H)), Syntax (tent Y H) S g m → Clause (tent Y H) z T a w n true e f →
      historyGram Y H V G j c χ s t w n u p hk t1 t2 (g*m) (e*f)=
         historyGram Y H V G j c χ s t w n u p hk t1 t2 g e * historyGram Y H V G j c χ s t w n u p hk t1 t2 m f

include h
lemma unlit (ha:∀ j:Axis, Between (tent Y H) j 0 (ruler Λ.block*w) T)(hx:Injective a)(v:x∈fieldBook z T a (tent Y H) w n)(k:InTest K true S false y.val)(u':lostCause Y H V G j c χ s t w n u S p T a z h.buys.high t1 t2) : GN y x=0:=by
 suffices w1: Gb y x=0 by unfold historyGram; rw [w1,inner_zero_right]
 refine Submodule.span_induction₂ (p:=fun x y _ _=> Gb x y=0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (script_span k) v
 · rintro _ _ ⟨g,b,l,rfl⟩ ⟨c0,y,hu,rfl⟩; have ht:=u' g b c0 y l hu; have hL:=exactly_here Y H V G j c χ t w n t1 t2 (clause_permitted Y H t w t1 ha hu).2 (every_cold Y H V G j c χ t w ha hx t1 hu rfl)
   have hy:Gb b y=0:=by unfold witnessedKet; rw [hL,ContinuousLinearMap.zero_apply,map_zero,map_zero]
   unfold historyGram at ht; rw [hy,inner_zero_right,mul_zero] at ht; exact inner_self_eq_zero.mp ht
 · intro _ _; unfold witnessedKet; rw [map_zero]; rfl
 · intro _ _; unfold witnessedKet; rw [map_zero, ContinuousLinearMap.zero_apply,map_zero,map_zero]
 · intro x y z a b t hu hx; unfold witnessedKet at *; rw [map_add,ContinuousLinearMap.add_apply,hu,hx,add_zero]
 · intro x y z a b t hu hx; unfold witnessedKet at *; rw [map_add,ContinuousLinearMap.add_apply,map_add,map_add,hu,hx,add_zero]
 · intro k x y p e hu; unfold witnessedKet at *; rw [map_smul,ContinuousLinearMap.smul_apply,hu,smul_zero]
 intro s x y p e hu; unfold witnessedKet at *; rw [map_smul,ContinuousLinearMap.smul_apply,map_smul,map_smul,hu,smul_zero]
-- clarify historyGram interpreted as same Ψ reading at THIS leg.
local notation "Aₚ"=> flank j r
local notation "P₀"=>LightBudget.gram j (tent Y H)
include σ
lemma authenticated (ha:∀ j:Axis, Between (tent Y H) j 0 (ruler Λ.block*w) T)(p':Syntax (tent Y H) S x y){e f:Dome (tent Y H)}(k:Clause K z T a w n true e f):
   let R(c d:Dome (tent Y H)):= Z c d∈D false (Σ∪O) ∧ Z c d∈ D false (flank j r) ∧ ∃ h:(P₀ (Z c d))∈ D false Set.univ, F ⟨P₀ (Z c d),h⟩=GN c d -- fix notation `cχ` captured
   R x e ∧ R y f ∧ R (x*y) (e*f):=by
 intro Kx; have hz(T T':Dome (tent Y H))(p: InTest K true S false T.val)(ht:T'∈insideAt Λ l K false B₁ t): Kx T T':=⟨coherent_product (q₀:=false) Y H V G j s t w n u S r δ _ h σ p nofun ht,highEnoughₚ (q₀:=false) Y H V G j s t w n u S r δ _ h σ p nofun ht, authority Y H V G j c χ s t w n u S r δ _ h σ t1 t2 p ht⟩
 obtain ⟨q,g⟩:= p'.afford; obtain ⟨w1,w2⟩:= clause_permitted Y H t w t1 ha k
 exact ⟨hz _ _ q w1,hz _ _ g w2,hz _ _ (q.mul g) ((insideAt ..).mul_mem w1 w2)⟩
lemma glistens (hO:InTest K true S false x.val)(hF:Traveler Y H V G c t w z T a y)(p': 1≤ (historyGram Y H V G j c χ s t w n u p h.buys.high t1 t2 x (lantern K y w n)).re) :
   ¬ lostCause Y H V G j c χ s t w n u S p T a z h.buys.high t1 t2 :=by
 intro e; rw [unlit Y H V G j c χ s t w n u S r δ p t1 t2 T a z h hF.carnet hF.real_ (allIlluminated w z T a n hF.basis) hO e] at p'; norm_num at p' -- tune
end loss
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.glistens
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.authenticated
