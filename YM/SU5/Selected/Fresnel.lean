import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Lights
import YM.SU5.Selected.Corridor
/-!
# CP5. Rank pack exposing consultations on resolving & locally charting readings.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "S"=> turnstile Y H V Q Qt j strict C f
local notation "R" => ride Y H V Q Qt j strict C f
local notation "P" k:max => (S).crew k
local notation "T" => look j
open Germ SelectionAnalysis Sunbelt
local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
open Repertoire
set_option maxHeartbeats 500000
variable {J : Type*} [Fintype J]
-- literal readers, not requiring equality of operators for different verandae; all labels multiple use possible
variable (X:J→ Marks (tent Y H) strict) (P' : ∀ i, Veranda Y H s j strict (X i))
variable (C' : ∀ j, Arena Y H Q.circuit j 0 strict)(c:∀ j,(displayAlgebra Y H V Q Qt j strict (C' j)) →⋆ₐ[ℂ]ℂ)(hi:∀ j k s x,response Y H V s Q Qt j strict (C' j) (c j) x=response Y H V s Q Qt k strict (C' k) (c k) x)
variable (p:List J)
local notation "B" n:max=> newLevel Y H s Q strict X n
local notation "Z" j:max=> Arena Y H Q.circuit j 0 strict
local notation "V₀" n:max j:max b:max=> bandstand Y H V n Q Qt j strict (C' j) (c j) (B n) b
local notation "Q₀" t:max k:max=> ∀ i:J, Veranda Y H t k strict ((B t) i)
local notation "fΛ"=> J→Axis→ℝ
local notation "L" k:max=> Request Y H s Q strict X p k
variable (r: Request Y H s Q strict X p j)
local notation "pV"=> Globe Y H V s Q Qt strict X C' c p
local notation "HA" j:max=> HAI Y H V s Q Qt strict X C' c p j
local notation "T₀" u:max j:max=> V₀ (u).grade j (u).ringT
local notation "U" u:max=> T₀ u j
variable [DecidableEq J] -- only for chart continuity stuff; density over arbitrary labels I maybe anyway
local notation "K'" k:max p:max=> bandstand Y H V s Q Qt k strict (C' k) (c k) X p
local notation "ι" x:max=> Repertoire.clearAbove x
local notation "Ξ₀"=> unify Y H V s Q Qt strict X C' c p
local notation "P₀"=> pavilion Y H V s Q Qt strict X C' c p
open Filming
local notation "Eξ" n:max a:max=> response Y H V n Q Qt a strict (C' a) (c a)
structure RankService : Prop where
  real_region : IsOpen pV ∧ IsOpen P₀
  moves_all (u : J→Axis→ℝ)(d : Axis→ℝ)(hu:u∈pV): (fun i=>u i+d)∈pV ∧ Ξ₀ (fun i=>u i+d)=Ξ₀ u ∧ ContinuousAt Ξ₀ u
  rank_score : ∀ (j: Axis) (r: Request Y H s Q strict X p j) (u:J→Axis→ℝ), u∈ (T₀ r j).planeOK r.year →
    Ξ₀ u=(T₀ r j).reading r.year u
  raw_score (q : List J)(j:Axis) (W : ∀ i, Veranda Y H s j strict (X i))(u:J→Axis→marks Μ)(p':(ι u) ∈ (K' j W).planeOK q) (r:ℕ) (u':s ≤ r)(z:J→ Cover)(h:draft Λ r z=u) :
    ((K' j W).ranking q u []= (Eξ r j) (answersAt Y H strict (newLevel Y H s Q strict X r) q z))
  projection_price (p:List J) (i: Axis) (W:∀ i',Veranda Y H s i strict (X i')) (hp:p.Nodup) (u:J→Axis→marks Μ)(t:List (Trans i))(k:Trans i) : Tendsto (fun s'=> Average.center (fun i' : J → Filming.Cell (timeMesh Λ) s'=> (K' i W).ranking p (Repertoire.swipe J u k.val (fun i=> Filming.pebbles (timeMesh Λ) s' (i' i))) t)) Filming.horizon (𝓝 ((K' i W).ranking p u (k::t)))
  continues_from (j: Axis)(W : ∀ i,Veranda Y H s j strict (X i))(p':List J)(u:J→Axis→marks Μ) :
    (K' j W).reading p' (clearAbove u)= (K' j W).ranking p' u (look j)
  exact_at (j: Axis)(r: Request Y H s Q strict X p j) (u:J→Axis→marks (timeMesh Λ)) (p':(ι u)∈(T₀ r j).planeOK r.year) (w:(ι u)∈ P₀): Ξ₀ (ι u)= (T₀ r j).ranking r.year u []
variable (hn:p.Nodup)
include hi hn
lemma implanted : RankService Y H V s Q Qt strict X C' c p:=by
 refine ⟨⟨globe_open ..,pavilion_open ..⟩,?_,fun j r u v=> unified Y H V s Q Qt j strict X C' c hi p r hn u v,fun q b w u p' r u' z=>played Y H V s Q Qt b strict (C' b) (c b) X w z q p' r u',fun p v W h x t u=> Repertoire.screening (K' v W) x p h t u,fun j w l u=> reading_exact ..,?_⟩ -- syntax sections using · not lambda when too many
 · intro u t p'; obtain ⟨v,h⟩:= globe_shift Y H V s Q Qt strict X C' c hi p hn u t p'; exact ⟨v,h,living_globe Y H V s Q Qt strict X C' c hi p hn u p'⟩
 intro i W u p' h; exact pays_at Y H V s Q Qt i strict X C' c hi p W hn u h p'

omit hi hn
-- detect mix & pedestal
variable (Vc : ∀ j, Arena Y H Q.circuit j 0 false)(m:∀ j,(displayAlgebra Y H V Q Qt j false (Vc j)) →⋆ₐ[ℂ]ℂ)(hw:∀ j k s x,response Y H V s Q Qt j false (Vc j) (m j) x=response Y H V s Q Qt k false (Vc k) (m k) x)
local notation "L₀" v:max=> fort Y H V Q Qt v false (Vc v) (m v)
local notation "S₁" j:max=> peninsula Y H V Q Qt j false (Vc j) (m j)
local notation "Ω₁" j:max=> vocation Y H V Q Qt j false (Vc j) (m j)
local notation "K₀"=> (show List Bool from [false,true])
structure GlobeShape (j: Axis) (δ₀:ℝ)(F:Marks (tent Y H) true) (z:SU.Slot)(S':Finset Cover)(o:Cover)(u d:ℕ)(a b:Cover):Prop where
  seen : Exceeds Y H V s Q Qt j (Vc j) (m j) δ₀ F z S' o u d a b
  cluster (x y: L₀ j)(l:ℝ)(h:0<l) : ∃ t:ℝ,0≤t ∧∀ s:Axis→ℝ,t<s j →(∀k:Trans j,t < |s k.val|)→
    ‖inner ℂ x ((S₁ j).E (s j).toNNReal ((S₁ j).U (diameter s) y))- inner ℂ x (Ω₁ j)* inner ℂ (Ω₁ j) y‖≤ l
  window : let R':= linkedPair Y H j F a b; let A':= unify Y H V s Q Qt false R' Vc m K₀; let S0:=pavilion Y H V s Q Qt false R' Vc m K₀
           A' 0= response Y H V s Q Qt j false (Vc j) (m j) (show Marks K false from bosonLabel K ((mirrorInMarks Y H j true (relocateWorld Y H true a F))*(relocateWorld Y H true b F))) ∧
             ∀ᶠ p in 𝓝 (0:Bool→ Axis→ℝ),p∈ S0 ∧ 1/33 ≤ ‖A' p‖ -- parentheses for notation A'
  dyad_service : RankService Y H V s Q Qt false (linkedPair Y H j F a b) Vc m K₀
include hw
lemma shape_here (s':ℝ)(F:Marks (tent Y H) true)(z:SU.Slot)(G':Finset Cover)(o:Cover)(u d:ℕ)(a b:Cover)(h:Exceeds Y H V s Q Qt j (Vc j) (m j) s' F z G' o u d a b): GlobeShape Y H V s Q Qt Vc m j s' F z G' o u d a b:=by
 exact ⟨h, model_mixes Y H V Q Qt j false (Vc j) (m j) h.live.true_vac,(foyer_price Y H V s Q Qt j Vc m hw s' F z G' o a b u d h).2,implanted Y H V s Q Qt false _ Vc m hw _ (show List.Nodup _ from (by change List.Nodup [false,true]; decide))⟩

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.RankService
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.implanted
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.shape_here
