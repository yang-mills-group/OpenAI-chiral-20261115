import YM.SU5.Reconstruction.PilotLight.Steady
import YM.SU5.Reconstruction.PilotLight.Reel
import YM.SU5.Reconstruction.PilotLight.Landsdale
/-! The Actual Bill: by aperture, Story. No Spectrum price required! -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5700
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted
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
local notation "J₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "T₀"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Lp'"=> Follows Y H V G j (c j) χ
variable {A B : (indoor Y H V G.history G.clipped j false (c j) χ).Op}
variable (s w:ℕ)
variable {x y:Dome (tent Y H)}
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
local notation "bP" n:max=> bAll Λ s w n
local notation "K₁"=> ticket Y H G s
variable (z z': SU.Slot) {v:placement Λ} (n m:ℕ)(p:0<n)(q:0 < m)(e:0<w)
variable {S:Finset Cover}{d:ℕ}{a:Fin d→ Cover}
local notation "Φ" t:max=> valuePort Y H V G j c χ s w n e p t
local notation "Ψ" t:max=> valuePort Y H V G j c χ s w m e q t
open BridgeClub
local notation "W"=> pilotBeam Y H V G j (c j) χ
structure SparkCost (S:Finset Cover) {d:ℕ}(a:Fin d → Cover) (x y:Dome (tent Y H)) (v:placement Λ) (p:0<n)(q:0 < m)(e:0<w): Prop where
  left : Mantle Y H V G j c χ s (w:=w) z (S:=S) a n e p x
  right : Mantle Y H V G j c χ s (w:=w) z' (S:=S) a m e q y
  wick (t:ℂ) : ‖pilotBeam Y H V G j (c j) χ v (valuePort Y H V G j c χ s w n e p x) (valuePort Y H V G j c χ s w m e q y) t - 1‖ ≤ amber m+amber n+amber n*amber m
  alive (t:ℂ) : 1-1/16 ≤ ‖pilotBeam Y H V G j (c j) χ v (valuePort Y H V G j c χ s w n e p x) (valuePort Y H V G j c χ s w m e q y) t‖
  apart (t:ℂ): ¬ CoolFactor Y H V G j c χ s w S z a m n v t z' e p q
  -- auxiliary assertions: actual comparison class queries not extrapolated off linear extension!
  salary : ∀ (g m₀ g' t:Dome (tent Y H)), Clause (tent Y H) z S a w n true g m₀ → Clause (tent Y H) z' S a w m true g' t →
       (∀ x∈({g,m₀,g*m₀}:Set _),x∈insideAt Λ l K false (alcove (hAll Λ s w n)) s) ∧
       (∀ x∈({g',t,g'*t}:Set _),x∈insideAt Λ l K false (alcove (hAll Λ s w m)) s)
-- Interpretation for ANY of those permitted probes at these positions, including x,y gauge-invariant. Values at WHOLE χ.
include V in
lemma inquiry_keeps {δ R:ℝ} {p:placement Λ} (ht:StandingFree j δ R p)(h: (hAll Λ s w n:ℝ)≤ R)(f:(hAll Λ s w m:ℝ)≤R){d:Bool}(r:x∈insideAt Λ l K d (alcove (hAll Λ s w n)) s)(v:y∈insideAt Λ l K d (alcove (hAll Λ s w m)) s): ticket Y H G s x*move K p (ticket Y H G s y)∈ Domain Y H G d (alcove R ∪ slides (coordinates Λ p) (alcove R)):=
 domain_mult Y H G (domain_mono Y H G (alcove_mono h) (ticket_mem Y H G r)) (moving Y H V G p (K₁ y) (domain_mono Y H G (alcove_mono f) (ticket_mem Y H G v))) ht.separation

lemma inquiry_reads (g:g₂ n < (Real.toNNReal (coordinates Λ v j))) -- actually h strict casts want simpler
    (r:x∈insideAt Λ l K false (alcove (g₂ n)) s)(t:y∈insideAt Λ l K false (alcove (g₂ m)) s) : ∃ h: K₁ x * move K v (K₁ y)∈D false Set.univ,
    osValue Y H V G j (c j) χ ⟨ticket Y H G s x * move K v (ticket Y H G s y),h⟩= W v (Φ x) (Ψ y) (((coordinates Λ v j - (g₂ n:ℝ)):ℝ):ℂ) := by
 rw [← aTime (Λ:=Λ)];
 refine euPrice Y H V G j (c j) χ v ?_ ?_ ?_ (portent Y H V G j c χ s w n e p r) (portent Y H V G j c χ s w m e q t)
 · rw [aTime]; exact (Real.lt_toNNReal_iff_coe_lt).1 g -- tune
 · rw [aTime]; positivity
 rw [aTime]; positivity
-- convenience use with Frame
lemma standing (v:placement Λ)(δ R:ℝ)(k:0<δ) (t:StandingFree j δ R v)(h: (hAll Λ s w n:ℝ) ≤ R): (g₂ n) < Real.toNNReal (coordinates Λ v j):= Real.lt_toNNReal_iff_coe_lt.mpr (h.trans_lt ((lt_add_of_pos_right _ k).trans_le (t.gap j)))
include p q in
lemma money (T:ℂ) (x:‖T-1‖≤amber m+amber n+amber n*amber m) : 1-1/16 ≤ ‖T‖:=by
 have hp:= norm_le_norm_sub_add (1:ℂ) T; rw [norm_one,norm_sub_rev] at hp
 nlinarith [amber_nonneg m,amber_nonneg n,amber_control m q,amber_control n p]

lemma sails_solid (X: Traveler Y H V G c s w z S a x) (Y': Traveler Y H V G c s w z' S a y) : SparkCost Y H V G j c χ s w z z' n m S a (lantern (tent Y H) x w n) (lantern (tent Y H) y w m) v p q e := by
 let T:=lantern (tent Y H) x w n; let K' :=lantern (tent Y H) y w m
 have hx:=collects Y H V G j c χ s z X n p e; have hy:= collects Y H V G j c χ s z' Y' m q e
 let h(t:ℂ):‖W v (Φ T) (Ψ K') t-1‖≤ amber m+amber n+amber n*amber m:=distance_pay Y H V G j (c j) χ v t hx.detail hy.detail
 let k(t:ℂ):1-1/16 ≤ ‖W v (Φ T) (Ψ K') t‖:=money n m p q _ (h t)
 refine ⟨hx,hy,h,k,fun t v'=> ?_,fun a b q l h k=>?_⟩
 · have he:=k t; unfold T K' at he; rw [noSplit_credit Y H V G j c χ s w S z a m n e p q z' v t X.carnet X.real_ hx.flow hy.flow v'] at he; norm_num at he
 obtain ⟨u₀,v'⟩:= clause_permitted Y H s w e X.carnet h; obtain ⟨w',v''⟩:= clause_permitted Y H s w e X.carnet k;
 refine ⟨?_,?_⟩ <;> (intro i h'; rcases Set.mem_insert_iff.mp h' with he|he <;> first| (subst i; assumption)| (rcases Set.mem_insert_iff.mp he with he|he; (subst i; assumption); replace he:= Set.mem_singleton_iff.mp he; subst i; first |exact (insideAt ..).mul_mem u₀ v'|exact (insideAt ..).mul_mem w' v''))

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.sails_solid
