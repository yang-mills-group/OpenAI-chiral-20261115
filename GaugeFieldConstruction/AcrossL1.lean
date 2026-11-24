import YM.CF.Buffered.Transfer

/- L1 stability estimates on actual marked ratios -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
lemma apply_stable {m B:Side}{j:ℕ}{L:Side}{ho:Odd L.val} {p:Pricing j L ho (Thread j)}{δ:ℝ}
   (U: Grasp p B δ) (R: Loom (CSide m B))(u: Measurable R)
   (X Y: GramM (CSide m B))(pX:Integrable (denZ X U R) (city (CSide m B))) (pY:Integrable (denZ Y U R) (city (CSide m B)))
   (F: Mark (CSide m B))(h:Envelope F) (c:ℝ) (v:∀ x:Fields (CSide m B), ‖F x‖≤ c) (d:ℝ)
   (hd:(∫ x, ‖(partitionZ X U R)⁻¹ • denZ X U R x-(partitionZ Y U R)⁻¹ • denZ Y U R x‖ ∂city (CSide m B)) ≤ d) :
   ‖markedRead F R (denZ X U R) / partitionZ X U R - markedRead F R (denZ Y U R) / partitionZ Y U R‖ ≤ c*d:=by
 let A(X: GramM (CSide m B)):=(partitionZ X U R)⁻¹ • denZ X U R; have hz(X):markedRead F R (denZ X U R)/partitionZ X U R=markedRead F R (A X):=by unfold A markedRead; simp only [Pi.smul_apply,map_smul]; rw [integral_smul,div_eq_mul_inv]; ring
 let P':=A X; let B':=A Y; have hp: Integrable P' (city _):= pX.smul _; have hb: Integrable B' (city _):= pY.smul _
 rw [hz,hz]; change ‖(∫ i, letterRead (F (drawn R i)) (P' i)∂city _) -(∫ i,letterRead (F (drawn R i)) (B' i) ∂city _)‖≤ _; rw [←integral_sub (mark_integrable u h hp) (mark_integrable u h hb)]; simp_rw [←map_sub]; refine (norm_integral_le_integral_norm _).trans ?_
 have ht:= integral_mono_of_nonneg (Filter.Eventually.of_forall fun _=>norm_nonneg _) (((hp.sub hb).norm).const_mul c) (Filter.Eventually.of_forall fun x=> (mark_bound (F (drawn R x)) (P' x-B' x)).trans (mul_le_mul_of_nonneg_right (v _) (norm_nonneg _))) ; refine ht.trans ((integral_const_mul _ _).trans_le ?_); exact mul_le_mul_of_nonneg_left hd ((norm_nonneg (F (1,1))).trans (v _))

#print axioms apply_stable
end YM.CF.Buffered
end
