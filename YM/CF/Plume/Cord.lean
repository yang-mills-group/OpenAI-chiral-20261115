import YM.CF.Plume.Roll
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open scoped Classical ENNReal NNReal
open Girt
section sw
variable {E F:Type*}[MeasurableSpace E][Fintype E][MeasurableSingletonClass E][Nonempty E]
lemma paper (i:E): paperMeas E {i}= (Fintype.card E: ℝ≥0∞)⁻¹:=by
 simp [paperMeas, Measure.finset_sum_apply] -- tune
lemma bore(f:E→ E→E)(h:treatQ f): let μ:= paperMeas E; MeasurePreserving (rollQ f) (μ.prod μ) (μ.prod μ):=by
 intro μ; let L:= μ.prod μ; have hp(U:E×E): L {U}= (Fintype.card E:ℝ≥0∞)⁻¹ * (Fintype.card E:ℝ≥0∞)⁻¹:=by cases U with| mk x y=> dsimp only [L,μ]; rw [← Set.singleton_prod_singleton,Measure.prod_prod,show _=_ from paper x,show _=_ from paper y] -- tune
 have ht:Measurable (rollQ f):=measurable_of_countable _; refine ⟨ht, Measure.ext_of_singleton fun i=>?_⟩; change L.map _ _= L _; rw [Measure.map_apply ht (measurableSet_singleton _),show (rollQ f) ⁻¹' {i}={rollQ f i} from ?_,hp,hp]; ext x; simp only [Set.mem_preimage,Set.mem_singleton_iff]; exact ⟨fun h'=>(roll_in f h x).symm.trans (congrArg _ h'),fun g=>g ▸ roll_in f h i⟩
end sw
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
abbrev Cord := Arena.Tab S× TeamY (mid P B)
instance msT : MeasurableSpace (Arena.Tab S):= ⊤
instance : MeasurableSingletonClass (Arena.Tab S):=⟨fun _=> trivial⟩
instance ncS : Nonempty (Arena.Tab S):=by haveI:Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side; unfold Arena.Tab; infer_instance
variable{S}
def mixT (X:Support n₀)(y z:Cord S):Cord S:= bothQ (Arena.unite S X) (bothQ (bothQ (prQ fun i:Bond m₀=> S.ratio.parent i.1∈X) (prQ fun i:Bond m₀=> S.ratio.parent i.1∈X)) (prQ fun i:Site m₀=> S.ratio.parent i∈X)) y z
lemma mix_t(X:Support n₀): treatQ (mixT (S:=S) X):=by
 apply treat_m (f:=Arena.unite S X) (g:=_) _ (treat_m _ _ (treat_m _ _ (pr_t _) (pr_t _)) (pr_t _)); intro y z; apply Arena.eq_t
 · funext i; by_cases h:S.ratio.parent i∈X<;> simp [Arena.unite,Arena.token,h] -- error when !in: second z first? nested E f(exchange uses Y second case, inner2=zY picks y if not). ok
 · funext i; by_cases h:S.ratio.parent i∈X<;> simp [Arena.unite,Arena.token,h]
 refine Prod.ext (funext fun i=>?_) (funext fun i=>?_); by_cases h:i∈X <;> simp [Arena.unite,h]; by_cases h:i.1∈X <;> simp [Arena.unite,h] -- semicolon
variable(S)
def plummy(s:ℝ):Measure (Cord S):= (paperMeas (Arena.Tab S)).prod (springT S s)
lemma lum_p {s:ℝ}(p:0<s): IsProbabilityMeasure (springT S s):=by unfold springT suit; haveI:=Appel.how (α:=Bond m₀) G₀ p; infer_instance
lemma plum_p {s:ℝ}(p:0<s): IsProbabilityMeasure (plummy S s):=by unfold plummy; haveI:=lum_p S p; infer_instance
variable{S}
lemma plum_m{X:Support n₀}{s:ℝ}(p:0<s): let μ:= plummy S s; MeasurePreserving (rollQ (mixT X)) (μ.prod μ) (μ.prod μ):=by
 intro μ; haveI:= lum_p S p; have hp:treatQ (Arena.unite S X):=by
    intro u v; let Z: TeamY (mid P B):= ((1,0), Classical.arbitrary _); exact congrArg Prod.fst (mix_t X ((u,Z):Cord S) (v,Z)) -- tune
 haveI:= Appel.feast_nn G₀ p; apply roll_m (f:=Arena.unite S X) (g:=_) _ _ (bore _ hp)
 let κ:= prior G₀ m₀; haveI:=Appel.how (α:=Bond m₀) G₀ p
 exact roll_m (κ.prod (tableG G₀ (Bond m₀) s)) (depot _) _ _ (roll_m κ _ _ _ (pr_m ..) (pr_m ..)) (pr_m ..) -- pr_m inferred?
variable {s:ℝ}
def Fairy (S:StepData (Domain N B) (Domain P B))(s:ℝ)(x: Cord S):Prop:= ‖x.2.1.2‖ ≤ s
lemma tone_v (p:0<s):∀ᵐ x: TeamY (mid P B) ∂springT S s,‖x.1.2‖ ≤ s:=by
 let μ:= tableG G₀ (Bond m₀) s
 haveI:IsProbabilityMeasure (suit S):=by unfold suit; infer_instance
 haveI:IsProbabilityMeasure μ:= Appel.how G₀ p; haveI:=feast_nn G₀ p; have hp(x:Bond m₀):∀ᵐ (t:SU.group.Color) ∂feast G₀ s,t∈closedBall 0 s:=by unfold feast; apply Measure.ae_smul_measure; exact ae_restrict_mem isClosed_closedBall.measurableSet -- tune
 have hv:∀ᵐ t∂μ,‖t‖ ≤ s:= (ae_all_iff.mpr fun i:Bond m₀=>(measurePreserving_eval (fun _:Bond m₀=>feast G₀ s) i).quasiMeasurePreserving.ae (hp i)).mono fun x t=> (pi_norm_le_iff_of_nonneg p.le).mpr fun i=> mem_closedBall_zero_iff.mp (t i)
 let φ:=suit S; have hk:MeasurePreserving (fun x:TeamY (mid P B)=> x.1.2) (springT S s) μ:=measurePreserving_snd.comp (measurePreserving_fst (μ:= φ.prod μ)); exact hk.quasiMeasurePreserving.ae hv
lemma tone_p(p:0<s): ∀ᵐ x ∂plummy S s,Fairy S s x:=by haveI:=lum_p S p; exact (measurePreserving_snd (μ:=paperMeas (Arena.Tab S)) (ν:=springT S s)).quasiMeasurePreserving.ae (tone_v p)
end YM.CF.Plume
