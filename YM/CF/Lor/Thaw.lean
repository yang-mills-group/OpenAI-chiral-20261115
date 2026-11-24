import YM.CF.Lor.Cell
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable (q:Chi)(K:ℝ)(n l:ℕ)
lemma tamper(P:Patch)(K K':ℝ)(h:0<K)(p:0<K') :∀ᶠ x in atTop,∀ β∈ Set.Icc (y G₅ P.L x/2) (2*y G₅ P.L x), let Y:= K'* Scales.p G₅ P.L x;∀ {c f:Side}(S:StepData c f)(T:Tube SU.group S)(M: Monk SU.group S),S.patch=P →‖M.z‖ ≤ Y → ∀ q:Chi,∀ d:ℝ,MossX n l x M.key M.park T M.V M.k K d (fiery G₅ x P.L) q→∀ i: M.zoo x, Allows n (fun y:Directions G₅ c=> tape ((M.atop y x).fuel x T q d l β) i) 0 1:=by
 let v:=Push.Uniform.shade G₅; have hv:0<v:=Push.Uniform.shade_pos _; let C:= v*(K+2*(2^n*K*K')); have hc:0<C:=by unfold C; positivity
 filter_upwards [(sizeK.scale (sizeK.fierce P.L) C).spine.eventually (ge_mem_nhds zero_lt_one), (year G₅ P.L).eventually_gt_atTop 0] with x u vz β b Y c f S T M hk hg q d H i
 have hz:0<Y:=mul_pos p (Scales.pos ..); have ht:=(ready_heat (β:=β) (M.bush x) (M.bell x) _ H Y ((pi_norm_le_iff_of_nonneg hz.le).mpr fun i=> (norm_le_pi_norm M.z i.val.val).trans hg) h.le); have hh := (shelJ ht.2 i); have hp:0<β:= (half_pos vz).trans_le b.1
 refine hh.mono (le_trans ?_ u); rw [abs_of_pos (coupling_pos hp)]
 apply (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_right (compare_v G₅ P.L x b vz).1 (by positivity : 0≤2^n*K*Y)) _) hv.le).trans (le_of_eq ?_); change v*(K*fiery G₅ x P.L+2*Scales.g G₅ P.L x*_)= _; unfold Y C; rw [Scales.fi]; ring
lemma rub(R: ChartRatio G₅)(v:ℝ)(h:LocalRatio R)(hp:0<v)(ht:4*v<R.radius):∃ C:ℝ,0<C∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ SU.group.Color)(x:E),Allows n U x 1→Allows n (logGuard q R v ∘ U) x C :=by
 obtain ⟨C,hc,H⟩:= Jet.compact_allow n zero_le_one _ ((logGuard_smooth q h hp ht).of_le (by exact_mod_cast le_top)) -- proof goal
 let K:=Jet.composeCost n C 1
 refine ⟨K+1,by unfold K Jet.composeCost; positivity,fun U x p=> ((H (U x) p.value).comp p).mono (le_add_of_nonneg_right zero_le_one)⟩ -- tune binder
-- cocoon Pell
lemma inc (p:Clip)(a σ:ℝ)(h:0<σ):∃ C:ℝ,0≤C ∧∀ᶠ x:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(T: Tube SU.group S)(M: Monk SU.group S),∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](i:E→L[ℝ] Directions G₅ c),(∀ y,axl M.key.flags (temp x•i y)=temp x• i y) → ‖i‖ ≤1→∀ L:ℝ,T.down.Bounds p σ a L →∀ (s:Signed)(w:Cell c),Allows n (fun y:E=>Esti.king (traceZ (turnStore s M.key).flags) T.down p (Stores.till x) S.patch.L.val (temp x) (pull s 0 ((Vmove x M.V ∘ i) y)) w) 0 C:=by
 obtain ⟨D,v,hD,hv,H⟩:= moveC n; obtain ⟨C,t,hC,hs,ht,hP⟩:= pong n D hD; obtain ⟨u,h,hU⟩:= shake_p n p a σ C hC hs h; refine ⟨u,h,?_⟩
 filter_upwards [Work.E05.ultimately_cool (min v (min t 1)) (lt_min hv (lt_min ht zero_lt_one)),eventually_gt_atTop (0:ℝ)] with x hx hy c f S T M E _ _ i h hp L g s w; let V:=Vmove x M.V∘ i; have ht:=hx.2.trans (min_le_right ..); have hv':= Work.E09.temp_pos hy; have hK(j:Bond c): Tender (fun y=> (Vmove x M.V ∘ i) y j) (0:E) (D*temp x) n:= (Shake.dil i _ (H _ _ hv' (hx.2.trans (min_le_left ..)) _) hp le_rfl).bag (by rw [one_pow,mul_one]); exact hU (pull s 0 ∘ V) 0 (temp x) _ _ (Stores.till x) S.patch.L.val hv' (ht.trans (min_le_right ..)) (hP V 0 _ hv'.le (ht.trans (min_le_left ..)) hK s).1 g (face_h (curtainP (x':=(0:E)) h) s) S.patch.L.property _
end YM.CF.Lor
