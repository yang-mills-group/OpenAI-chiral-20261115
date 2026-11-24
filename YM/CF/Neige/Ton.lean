import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Gains
import YM.CF.Neige.Hike
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open FreeResolvent TestD AnalyticBridge.RelativeLogdet
section
variable {b:Mark α E}{ξ ι ρ:Type}[Fintype ι][DecidableEq ι] {W:Mark ρ ξ}{D':Cost ξ}{v':ρ→E}{P:ι→ξ}{x:E}{σ q V' r₀ u Q N η:ℝ} {I:ι→Set ι}{A:E→ Shelf ι}
def stepM(U:ι→Set ι)(A:Shelf ι)(x:ℝ):= pie U (edgeM A x) 0
lemma edge_gapM (h:FreeResolvent.Gap (A x) r₀)(hp:0<r₀){w:ℝ}(ht:w∈Isle):FreeResolvent.Gap (edgeM (A x-1) w) (min r₀ 1):=by
 let t:=min r₀ 1
 constructor; intro v; unfold edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph
 rw [Matrix.add_mulVec, one_mulVec, smul_mulVec, Matrix.sub_mulVec, one_mulVec, dotProduct_add,dotProduct_smul,dotProduct_sub,smul_eq_mul]
 have he := (h.mono (show t ≤ r₀ from min_le_left ..)).lower v
 have hl : t*(v ⬝ᵥ v)  ≤  v ⬝ᵥ v:=mul_le_of_le_one_left (normSum_nn v) (min_le_right ..)
 calc
    _ = (1-w)*(t*(v ⬝ᵥ v))+w*(t*(v ⬝ᵥ v)):=by dsimp only [t]; ring
    _  ≤  _:= (add_le_add (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left he ht.1)).trans_eq (by ring)
lemma tag_h (h:∀ i,i∈I i)(he:Bundle v' W D' P P A x n σ C)(hG:FreeResolvent.Gap (A x) η)(hp:0<η): Ink.Arc (fun z:E ×ℝ =>stepM I (A z.1-1) z.2) n x:=by
 apply pie_s _ _ h (fun t ht=>edge_gapM hG hp ht) (lt_min hp zero_lt_one); intro i hi; unfold edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph
 exact contDiffAt_const.add (contDiffAt_snd.smul ((he.smooth.comp _ contDiffAt_fst).sub contDiffAt_const))
lemma hector (he:Bundle v' W D' P P A x n σ C)(hG:FreeResolvent.Gap (A x) η)(hp:0<η)(hc:0 ≤ C)(p': W.Move D' d u)(hD:D'.Volume P d V') (hk: Price σ (C+1) (min η 1) d u V' 1 n)(hI:∀ i,i∈I i)(hx:(study I hI).Near D' P N)(t:ℝ)(ht:t∈Isle):
 let R:=meter n n (C+1) u (rise V' (min η 1))
 let S(y:E):=A y-1
 Bundle v' W D' P P (fun y=>stepM I (S y) t) x n d (V'*R) ∧ Bundle v' W D' P P (fun y=>tea_r (S y) (stepM I (S y)) t) x n d (Real.exp (-(n+1:ℕ)*d*N)*tagPrice u n (C+1) (V'*R)):=by
 intro R S; let B(y):=edgeM (S y) t; have hp' : Bundle v' W D' P P B x n σ (C+1):=by
    have ha:=sub_nonneg.mpr ht.2; apply ((((he.scale t).one_add ((one_r (x:=x) (p:=P) (v:=v')).scale (1-t)))).mono le_rfl ?_).glue (Eventually.of_forall fun y=>?_)
    · rw [abs_of_nonneg ht.1,abs_of_nonneg ha,mul_one]; exact add_le_add (mul_le_of_le_one_left hc ht.2) (sub_le_self _ ht.1)
    · unfold B edgeM S; simp only [AnalyticNext.ConnectedActivity.ResolventVolume.graph,smul_sub,sub_smul,one_smul]; abel -- tune order
 have h:Knew W D' P v' x n σ (C+1) (min η 1) 1 B:=⟨hp'.smooth,edge_gapM hG hp ht,Differential.recovered hp',by rw [mul_one]; exact fun l _ hl=>hp'.bound l hl⟩
 have hB: Bundle v' W D' P P (glimpse (study I hI) B 0) x n (3*(n+1:ℕ)*d) (V'*(R*drain 0)):=
    ⟨glimpse_smooth h _ le_rfl hk.r0,fun l hl=> (glimpse_rates h hk _ (u:=0) le_rfl p' hD l hl).mono le_rfl (mul_le_mul_of_nonneg_left (charges_lax _ hk.high (drain_pos le_rfl).le (drain_le le_rfl) hk.meter_abs) hk.vol)⟩ -- syntax
 have hd:= hk.pos
 have hU := h.miss hk (u:=0) le_rfl p' hD hx; dsimp only at hU
 rw [show drain 0=1 by simp [drain],mul_one] at hU hB
 have ht:d ≤ ↑(n+1:ℕ)*d:= le_mul_of_one_le_left hd.le (by push_cast; simp)
 refine ⟨(hB.mono (show d  ≤  _ by push_cast at *; nlinarith) le_rfl).glue (Eventually.of_forall fun y=>(pie_inspects _ _ _ hI).symm),?_⟩
 let X:=study I hI
 apply (Differential.bundle_neg (hU.mono ht le_rfl)).glue; filter_upwards with y
 unfold tea_r; change -(study I hI).error (B y) 0= _; rw [show _= -(defect I (B y) 0) from congr_arg Neg.neg (defect_survey _ _ _ hI).symm,AnalyticBridge.RelativeLogdet.defect]; rw [neg_sub]; simp only [zero_smul, add_zero]; rfl
end
end YM.CF.Neige
