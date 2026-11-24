import GaugeFieldConstruction.Pinions
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Ingredients
/-!
# Directional hull to marker charges.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25000
set_option linter.unusedVariables false
noncomputable section
namespace YM.FlightFlux
open Lattice Function Finset Wilson Filter RG Pressure Gauge Work.F03
open Push.Uniform AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n c: Side}{G: Gauge}{p:BudgetPoint}{c' a b v:ℝ}{X:Support n}{U:Config G n}{i x o:Site n}{m j:ℕ}
lemma linkage_v (G:Gauge)(k:ℕ): ∃ C:ℝ,0<C ∧∀ (n:Side)(i:Edge (Site n))(u:Config G n), Allows k (fun x:Directions G n=> G.mat (increment u x i)) 0 C:=by
 obtain ⟨C,c,f⟩:= exists_allows (f:=fun i:G.Color=> G.mat (G.lieExp i)) (s:={0}) (isCompact_singleton) (fun x h=> G.exp_jet.contDiffAt) k; let K:=1+2^k*composeCost k C 1 * ‖(1:G.Mat)‖; have hp:0 ≤ composeCost k C 1:=by unfold composeCost; positivity
 refine ⟨K,(by unfold K; positivity),fun n i u=>?_⟩
 let p:Directions G n→L[ℝ]G.Color:= ContinuousLinearMap.proj (R:=ℝ) i; have ht:= f _ (show p 0∈({0}:Set G.Color) by rw [map_zero]; rfl); apply Allows.mono ((ht.comp (allows_linear (show ‖p‖≤1 from ContinuousLinearMap.opNorm_le_bound p zero_le_one (fun x=>by simpa only [one_mul] using (show ‖p x‖≤ ‖x‖ from norm_le_pi_norm x i))) (show ‖p 0‖≤1 by simp))).times (f:=fun x:Directions G n=>G.lieExp (p x)) (g:=fun _=>(u i)) (allows_const _ (show ‖G.mat (u i)‖≤ ‖(1:G.Mat)‖ from ?_))) (le_add_of_nonneg_left zero_le_one); -- tune Mat.norm
 rw [mat_paid (u i), ← mat_paid (G:=G) 1]; simp
lemma slotChart (G:Gauge)(N k:ℕ): ∃ C:ℝ,1≤C∧∀ n:Side,∀ (U:Config G n) (v:Site n) (i:RG.Slot), i.length ≤ N → Allows k (fun x:Directions G n=> i.atSite (increment U x) v) 0 C:=by
 obtain ⟨C,h,p⟩:= linkage_v G k; let Q:= curvatureCost G * travelCost G k (2*N) C; refine ⟨max 1 Q,le_max_left ..,fun n U v i u=>?_⟩
 simp_rw [Work.F02.atSite_curvature]; have hz:(Work.F02.slotWalk i).length≤ 2*N:=by unfold Work.F02.slotWalk Slot.length Lattice.reverse at *; simp only [List.length_append,List.length_map,List.length_reverse,show (square i.plaq.val.1 i.plaq.val.2).length=4 from rfl]; omega
 exact Allows.mono (curvature_price (U:=fun z=> travel (increment U z) v (Work.F02.slotWalk i)) (travel_jets (fun j=>p n j U) v hz)) (le_max_right ..)
-- Restrict to house asks. Need for both Mark costs & X3 Stoke. Estimate also variant unscaled small.
section
variable {E: Type*} [NormedAddCommGroup E][NormedSpace ℝ E]{F:Config G n→ E}
abbrev fitsSpan (S:Support n)(e:Edge (Site n)) := e.1∈ S∧ e.1+step e.2∈ S
def Keeper (G:Gauge)(S: Support n): Directions G n→L[ℝ] Directions G n:= ContinuousLinearMap.pi (fun i=> if fitsSpan S i then ContinuousLinearMap.proj (R:=ℝ) i else 0)
lemma stays (p:LocalOn X F) (u:Directions G n):F (increment U (Keeper G X u))=F (increment U u):=by
 apply p; intro i h g; apply congrArg (fun x:G.Color=> G.lieExp x*U i); unfold Keeper; simp only [ContinuousLinearMap.pi_apply]; rw [if_pos (show fitsSpan X i from ⟨h,g⟩)]; rfl
lemma keeper_buy(w:0≤ v)(T:Directions G n)(p:∀ i:Edge (Site n),fitsSpan X i→ ‖T i‖≤ v): ‖Keeper G X T‖≤v:=by
 apply (pi_norm_le_iff_of_nonneg w).2; intro i; unfold Keeper; by_cases h: fitsSpan X i
 · simp only [ContinuousLinearMap.pi_apply]; rw [if_pos h]; exact p i h
 simp only [ContinuousLinearMap.pi_apply]; rw [if_neg h]; exact (show ‖(0:G.Color)‖≤ v from (norm_zero|>.le.trans w))
structure KernelA (u:BudgetPoint)(F:Config G n→ E)(X: Support n) (a v:ℝ)(G₀: Set (Config G n)):Prop where
 fit : LocalOn X F
 bound(x:Config G n): x∈ G₀ → ‖F x‖≤ v
 proof(x:Config G n) : x∈ G₀ → Allows u.order (fun z:Directions G n=> F (increment x z)) 0 a
lemma hatchC(L:Allows m (fun z:Directions G n=> F (increment U z)) 0 a) (p:LocalOn X F)(k:j ≤ m)(V: Fin j → Directions G n) (v:Fin j→ℝ)(h:∀ i,0≤ v i)(f:∀ i e,fitsSpan X e→ ‖V i e‖≤v i): ‖iteratedFDeriv ℝ j (F ∘ increment U) 0 V‖ ≤ a*∏ i,v i:=by
 let X':=Keeper G X; let G':=F ∘ increment U; have he: iteratedFDeriv ℝ j G' 0 V= iteratedFDeriv ℝ j G' 0 (fun i=> X' (V i)):=by
    have h:iteratedFDeriv ℝ j (G'∘X') 0=ContinuousMultilinearMap.compContinuousLinearMap (iteratedFDeriv ℝ j G' 0) (fun _=> X'):=Next.Foundations.jets_linear X' (L.analytic.of_le le_top)
    rw [show G'∘X'=G' from funext (fun x=> stays p x)] at h; exact congrArg (fun F=> (F: ContinuousMultilinearMap ℝ (fun _:Fin j=>Directions G n) E) V) h -- tune
 rw [he]; exact ((iteratedFDeriv ℝ _ G' 0).le_opNorm _).trans (mul_le_mul (L.norm_le _ k) (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>keeper_buy (h i) (V i) (f i))) (Finset.prod_nonneg fun i _=>norm_nonneg _) L.nonneg)
end
end YM.FlightFlux
end
