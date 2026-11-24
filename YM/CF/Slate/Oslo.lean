import YM.CF.Slate.Spool
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
open Work.E03 Souk
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open Push
local notation "G"=> SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
-- unscaled has protected; transfer to σ with polynomial lamp mask. λ can be comparable with lamp not from ψ.
local notation "G₀"=>SU.group
variable {s:ℝ}{V:Config G c}{Y: Stores S} -- G notation
abbrev satU (g:Gauge)(s:ℝ)(v:Mast g c):Config g c:=facadeX g (s•v)
abbrev Chief(T:Tube G S)(x:ℝ)(F: Forest S.ratio)(k:S.Choices)(s:ℝ)(v:Mast G c):= bedX T x (bareStores S) F k (satU G s v)
lemma potP (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n:ℕ):∃ C e:ℝ,0<C∧0<e ∧∀ᶠ x in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → ∀ (k:S.Choices)(s:ℝ), s ∈ Set.Icc 0 e→ ∀ v:Mast G c, ‖v‖ ≤ 1 → Protected n (Chief T x F k s) v C ∧ Protected n (fun x'=> (Chief T x F k s x').transpose) v C:=by
 obtain ⟨a,d,y,C,m,ha,hd,hv,hC,hm,H⟩:=stampX n G K P p; let R:=Uniform.shade SU.group; refine ⟨composeCost n (activation G n 0 d*C) R,min a 1,(by unfold R Jet.composeCost; have hz:=activation_one G n 0 hd; have ht:=Uniform.shade_pos G; positivity),lt_min ha zero_lt_one,?_⟩
 filter_upwards [H,eventually_gt_atTop (0:ℝ)] with x H ht c f S T F Q k s hl v hV
 have hs:s≤1:=hl.2.trans (min_le_right ..); have hp : (bareStores S).flags=RG.flags (temp x) (1:Config G c):=(PhysicalNext.JointLoad.Heir.noFlags ..).symm
 let f:= hull G c; let L:=s • f
 have he :‖s • v‖≤ s:=by rw [norm_smul_of_nonneg hl.1]; exact mul_le_of_le_one_right hl.1 hV
 have hy: L v= hull G c (s • v):=(map_smul f s v).symm
 have hh:‖reader G c (L v)‖≤a:= hy.symm ▸ ((hull_h (s • v)).trans (he.trans (hl.2.trans (min_le_left ..))))
 have hx:= H S T Q.got Q.size Q.funds.1 (bareStores S) F k 1 hp (reader G c (L v)) hh
 have hf: ‖L‖ ≤ R:=by unfold L; erw [norm_smul,Real.norm_of_nonneg hl.1]; exact (mul_le_mul_of_nonneg_left (show ‖f‖ ≤ R from hull_n) hl.1).trans (mul_le_of_le_one_left (Uniform.shade_pos G).le hs)
 have hg:Allows n L v R:=Jet.allows_linear hf ((L.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hV).trans hf)); let B(z:PriceCoords G c):= AnalyticBridge.SectorAffine.field (1:Config G c) z
 have hc(y'): B (reader G c (L y'))=satU G s y':=by unfold satU facadeX B; rw [reader_field,map_smul]; rfl -- tune
 let X(z:Config G c):= bedX T x (bareStores S) F k z; have h := hx.2.2.1
 exact ⟨((polar_cash (A:=X ∘ B) _ h hC.le hd).comp hg).germ (Eventually.of_forall fun i=>by simp only [Function.comp_apply,hc]; rfl),((polar_cash (A:=fun x=> (X (B x)).transpose) _ h.transpose hC.le hd).comp hg).germ (Eventually.of_forall fun i=>by simp only [Function.comp_apply,hc]; rfl)⟩ -- application explicit A? tune
open FreeResolvent (Cost Bundle)
lemma transfer{a:ℝ}{k:S.Choices}{A:E→ Config G c}{u:E}(p:Protected n (fun y=> (majorX T x (bareStores S) F k q d 1 l (A y)).submatrix (pageX F x) (pageX F x)) u a):Protected n (majorX T x (bareStores S) F k q d 1 l ∘ A) u a:=by
 apply (jump_up (visitX F x) (leaveX F x) (leave_n ..) (visit_n ..) p).germ; filter_upwards with i; let M:= majorX T x (bareStores S) F k q d 1 l (A i); rw [tableVisit]; ext1 z
 change leaveX F x (visitX F x (paintO M (leaveX F x (visitX F x z))))= _; rw [visit_right,visit_right]; rfl
end YM.CF.Slate
