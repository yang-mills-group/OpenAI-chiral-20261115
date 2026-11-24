import YM.CF.Jade.Sill
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable {r:ℕ}{Lκ d_:ℝ}{E:Type}{J:Type}[MeasurableSpace E][NormedAddCommGroup J]
open Girt Plume
lemma loral {u:ℝ}(h:0<u): MeasurePreserving (fun x:Cord S=> (x.2.1.2, x.2.2)) (plummy S u) ((tableG G5 (Bond (Domain P B)) u).prod (depot _)):=by
 let t:=tableG G5 (Bond (Domain P B)) u; let μ:=springT S u
 haveI:= Plume.lum_p S h; haveI: IsProbabilityMeasure (suit S):=by unfold suit; infer_instance
 haveI:IsProbabilityMeasure t:=Appel.how _ h
 exact (MeasurePreserving.prod (measurePreserving_snd (μ:=suit S) (ν:=t)) (MeasurePreserving.id _)).comp (measurePreserving_snd (μ:=paperMeas (Tab S)) (ν:=μ))
-- generic Simple finite measures
lemma fin_r (F:E→J)(hp:(Set.range F).Finite): ∃ Z:ℝ, 0 ≤ Z∧ ∀ i,‖F i‖≤ Z:=by
 let Z:=∑ i∈hp.toFinset,‖i‖; refine ⟨Z,sum_nonneg (fun _ _=> norm_nonneg _),fun i=>?_⟩; exact single_le_sum (fun x _=>norm_nonneg x) (hp.mem_toFinset.mpr ⟨_,rfl⟩) -- tune
variable{X':Type}[MeasurableSpace X'][Finite X'][MeasurableSingletonClass X']
lemma frill [SecondCountableTopology J](f:E→X')(p:Measurable f)(g:X'→J)(μ:Measure E)[IsFiniteMeasure μ]: Integrable (g ∘ f) μ:=by
 obtain ⟨z,h,Z⟩:= fin_r g (Set.finite_range _) -- Measurable to strongly may lacksSecond.Space; use countable Strong
 refine Integrable.of_bound ?_ z (Eventually.of_forall fun i=> Z (f i)); letI:= borel J; letI:BorelSpace J:=⟨rfl⟩; exact (((measurable_of_countable g).stronglyMeasurable).comp_measurable p).aestronglyMeasurable -- tune
local instance :MeasurableSpace (Finset (Sat S)):= ⊤
local instance :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local notation "dN"=> Directions SU.group (Domain P B)
local notation "Dz"=> tableG G5 (Bond (Domain P B))
local notation "μx"=> (depot (mid P B))
abbrev tale (S:StepData (Domain N B) (Domain P B))(k:ℕ)(u:ℝ):= Set.range (fun v:Directions SU.group (Domain P B)=> news (S:=S) v k u)
noncomputable def velt (z:dN)(b:ℕ)(c:ℝ): ↥(tale S b c):=⟨news (S:=S) z b c,⟨z,rfl⟩⟩
lemma velt_m:Measurable (fun z:dN=>velt (S:=S) z k d_):=Measurable.subtype_mk (talks_m _ _)
local instance :MeasurableSpace (List (Hos S r)):= ⊤
local instance :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
variable(C: Sil S r→tale S k d_→ℝ)
lemma ort(h:0<t)(i:Sil S r): Integrable (fun z:dN=> C i (velt (S:=S) z k d_)) (Dz t):=by
 haveI:= how G5 (α:=Bond (Domain P B)) h; exact frill _ (velt_m (k:=k)) (C i) _ -- tune
local notation "Φ"=> (fun i:Cord S=> C (era i.2.2) (velt (S:=S) i.2.1.2 k d_))
lemma eyes(h:0<t): Integrable Φ (plummy S t)∧(∫ i,Φ i ∂plummy S t)= ∫ i, (∫ z:dN,C (era i) (velt (S:=S) z k d_)∂Dz t)∂μx:=by
 let U(x: dN × Ids (mid P B)):= C (era x.2) (velt x.1 k d_); let Pμ :Measure (dN):= Dz t; haveI:IsProbabilityMeasure Pμ:=Appel.how _ h; have hp: Integrable U (Measure.prod Pμ μx):=frill _ (Measurable.prodMk (sill_m.comp measurable_snd) (velt_m.comp measurable_fst)) (fun x: ↥(Sil S r)× ↥(tale S k d_)=>C x.1 x.2) _
 let H:=loral (S:=S) h; exact ⟨H.integrable_comp_of_integrable hp,(Girt.hinge _ _ H hp).symm.trans (integral_prod_symm U hp) ⟩
end YM.CF.Jade
