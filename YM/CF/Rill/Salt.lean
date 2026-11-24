import YM.CF.Rill.Pott
import YM.CF.Levier.Wake
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes
attribute [local instance] opCStarAlgebra
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{x:E}
lemma Shake.various{ι:Type}[Fintype ι](P:E→ι→F)(g:0≤K)(h:∀ i,Shake (fun x=>P x i) x K l): Shake P x K l:=by
 have hp:ContDiffAt ℝ (↑l) P x:=contDiffAt_pi.mpr fun i=>(h i).smooth; refine ⟨g,hp,fun i u v=>ContinuousMultilinearMap.opNorm_le_bound g fun j=>?_⟩; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a=> ?_
 let L: (ι→F)→L[ℝ] F:=ContinuousLinearMap.proj a; change ‖L _‖≤ _; rw [show L _ = iteratedFDeriv ℝ i (fun v=>P v a) x j from ?_]; swap; · change L _=iteratedFDeriv ℝ i (L ∘ P) _ _; rw [L.iteratedFDeriv_comp_left hp (Nat.cast_le.mpr v)]; rfl
 exact ((iteratedFDeriv ℝ i (fun v=>P v a) x).le_opNorm j).trans (mul_le_mul_of_nonneg_right ((h a).bill i u v) (by positivity))
lemma brand_ask (k:ℕ):∃ a C:ℝ,0 < a ∧ 1 ≤ C∧ ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x:E){b:ℝ}(p:b≤a)(U:E→ SU.group.El)(t:Tender U x b k)(i:Bool), Shake (fun y=>if i then brand (U y) else star (brand (U y))) x (C*b) k:=by
 -- from dusk.Private expose.S
 obtain ⟨D,hD,P⟩:= slope k -- tune
 obtain ⟨K,hK,J⟩:= Jet.payment_for k (isCompact_univ.image SU.fund_cont) SU.triple (fun _ _=> trie.contDiffAt) -- tune
 let X:= (max 1 (Shake.quota k*K))*D; let V:=(starL' ℝ (A:=Tulip.Twig)).toContinuousLinearMap; let C:= max 1 ‖V‖ * X; have hx:D≤X:=le_mul_of_one_le_left (zero_le_one.trans hD) (le_max_left ..); have hu:X ≤ C:=le_mul_of_one_le_left (by positivity : 0 ≤ X) (le_max_left ..)
 refine ⟨1/D,C,div_pos one_pos (zero_lt_one.trans_le hD),hD.trans (hx.trans hu),@fun E _ _ y b p U t i=>?_⟩
 let L(y:E):=brand (U y); have hh :Shake L y (X*b) k:=by
    have hb:D*b ≤ 1:=(mul_comm ..).le.trans ((le_div_iff₀ (zero_lt_one.trans_le hD)).mp p); have ht:=P U y b t -- tune
    let F(y:E):=SU.fund (U y)
    have hf: Shake F y (D*b) k:=ht
    exact ((hf.thorn (Shake.pick (J _ (Set.mem_image_of_mem _ (Set.mem_univ (U y))))) hb).bag (by rw [←mul_assoc,←mul_assoc]; unfold X; gcongr <;>first| exact le_max_right ..|exact Tender.price_p U t|positivity)).team (hf.bag (mul_le_mul_of_nonneg_right hx (Tender.price_p U t))) -- check order ih
 cases i; exact (shakeL L _ hh V).bag (by rw [←mul_assoc]; unfold C; gcongr <;>first|exact le_max_right ..|exact Tender.price_p U t|positivity); exact hh.bag (mul_le_mul_of_nonneg_right hu (Tender.price_p U t))
end YM.CF.Rill
