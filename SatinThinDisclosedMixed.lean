import SatinFixedContrastNovember4
import SatinThinDisclosedPlan

/-!
# Really mixed (not in either pure raw plane)

`Spine.sensing` as given wouldn't assert this by itself (it's a submodule).
Check at the price on the actual prepared smears. Elementary but useful check
of nonvacuity even for each single, in this model with many terms and two kinds
of normalization on the fields. No claim about which plane any continuum
object should be interpreted in.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)
local notation "σ[" t "]"=> P.thinSplit x t
local notation "T"=> P.Test
local notation "X" => T →ₗ[ℂ]ℂ
local notation "p[" t "]"=> P.singleState 3 t x
local notation "K"=> P.calibration
local notation "ℒ"=> Lead.Clan
abbrev reallyMixed (P:Spine)(F:P.Test) := ¬ (PureGauge P.calibration F ∨ PureMatter P.calibration F)

private lemma directed_pure_test (s:ℕ)(F:T)(B:X)(q:p[s] F=0)(t:B F≠0)(v:B 1=0)
    (h:∀ M:X, Factors K M→ MatterWard K M∨GaugeWard K M→ M F=0) : reallyMixed P F:=by
 let G:=gaugePlane K; let L:=matterPlane K
 let W:=G.subtype; let V:= L.subtype; let C:X:=p[s]; let D:X:=p[s] + B
 have hc:C 1=1:= by change p[s] 1=1; rw [P.single_state,P.reading_unit,map_one]
 have hd:D 1=1:=by change C 1+B 1=_; rw [v,add_zero,hc]
 have hx:D F≠0:=by change p[s] F+B F≠0; rw [q,zero_add]; exact t
 rintro (r|r)
 · obtain ⟨M,_,g,k,l⟩:=any_marginal_pair K (D.comp W) (C.comp V) hd hc
   have hp:MatterWard K M:=(marginal_matter _ _ k).mpr ((marginal_matter K (C.comp V) rfl).mp (P.singles_pure_ward s x).2)
   exact hx ((LinearMap.congr_fun g (⟨F,r⟩:G)).symm.trans (h M l (Or.inl hp)))
 obtain ⟨M,_,g,k,l⟩:= any_marginal_pair K (C.comp W) (D.comp V) hc hd
 have hp:GaugeWard K M:=(marginal_gauge _ _ g).mpr ((marginal_gauge K (C.comp W) rfl).mp (P.singles_pure_ward s x).1)
 exact hx ((LinearMap.congr_fun k (⟨F,r⟩:L)).symm.trans (h M l (Or.inr hp)))

variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "W"=> P.soldTrumpet A c r n w
variable (T':P.HandleWith x c r A n) (F U: SampleDose)
local notation "s!" i:max=> c (n i)
local notation "I₁" a:max i:max => ((W a i).kiss P 3)
local notation "Φ" a:max t:max i:max=> P.prepared t (I₁ a i) F
local notation "Ψ" b:max t:max i:max=> P.prepared t (W b i) U
local notation "U₁" a:max i:max=>P.spacePrice (I₁ a i) F
local notation "U₂" b:max i:max=>P.spacePrice (W b i) U
local notation "χ'"=> P.reportPrism A c r n w F U
variable {C L: Doorway}{s k:ℕ}{K':P.Register}{μ:ℝ}
lemma verified_mixtures (D:P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∀ᶠ i in atTop, ∀ t:ℕ,s! i≤ t →
      (∀ a:ℒ,P.reallyMixed (Φ a t i) ∧ P.reallyMixed (Ψ a t i)):=by
 obtain ⟨d,u,_,_,e⟩:=D.margin; let E:= D.then_read
 filter_upwards [E.comparison,E.ward,e] with i y v q t b a
 have hm:= loud_fullrank _ d (q t b) u; rw [(y t b).2,sub_zero] at hm
 let F':= Φ a t i; let G':= Ψ a t i; let X':X:=p[t].comp ((LinearMap.mul ℂ T).flip G'); let Y:X:=p[t].comp (LinearMap.mul ℂ T F')
 have hr:p[t] (F' * G')≠0:= hm.2 a; have hv : p[t] F'=0∧ p[t] G'=0:= E.bothZero a i t b
 refine ⟨P.directed_pure_test x t F' X' hv.1 hr ?_ (fun x g h=> ((v t b x g h).1 a).1), P.directed_pure_test x t G' Y hv.2 hr ?_ (fun x g h=> ((v t b x g h).1 a).2)⟩
 · change p[t] (1 * G')=0; rw [one_mul,hv.2]
 change p[t] (F'*1)=0; rw [mul_one,hv.1]

section
variable (F' U':SampleDose)
-- include concrete plans, both marginal factors individually, under-box availability in FullPrismLab. Combined convergence as in AuthorizedPair. Price χ' on the comparator exactly both ways at that t.
structure SimultaneousDisclosure (i t:ℕ) : Prop where
 nonpure (a:ℒ) : P.reallyMixed (Φ a t i) ∧ P.reallyMixed (Ψ a t i)
 first_plan (a:ℒ) : ∃ L,P.stitchPlan t (U₁ a i) L (Φ a t i)
 second_plan (a:ℒ) : ∃ M,P.stitchPlan t (U₂ a i) M (Ψ a t i)
 marginal_cross (a b:ℒ) (f:P.PulseComponent t (U₁ a i))(g:P.PulseComponent t (U₂ b i)) : P.linkMarginal t _ x f=0 ∧ P.matterMarginal t _ x f=0 ∧ P.linkMarginal t _ x g=0 ∧ P.matterMarginal t _ x g=0 ∧ P.linkLink t _ _ x f g=0 ∧ P.matterMatter t _ _ x f g=0 -- individual prices in actual state's pure marginals
 split_costs (a b:ℒ)
    (L:P.PulseComponent t (U₁ a i)→₀ℂ)(M:P.PulseComponent t (U₂ b i)→₀ℂ)(h:P.stitchPlan t (U₁ a i) L (Φ a t i))(p:P.stitchPlan t (U₂ b i) M (Ψ b t i)) :
    χ' i t σ[t] a b=
      ∑ k∈L.support, ∑ j∈ M.support,L k * (M j * (P.linkLink t _ _ x k j * P.matterMatter t _ _ x k j))

lemma plan_issued (D:P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∀ᶠ i in atTop,∀ t:ℕ,s! i ≤ t → P.SimultaneousDisclosure x A c r n w F U i t:=by
 let R:= D.armada; let E:= D.then_read
 filter_upwards [E.epoch,P.verified_mixtures x A c r n w V g h T' F U D] with i h t s f
 exact {
  nonpure:= t s f
  first_plan:= fun a=> P.stitchPlan_budget s (I₁ a i) _ (P.sensor_mirror a.2 3 _ (R.sensor a i)) f
  second_plan:=fun a=> P.stitchPlan_budget s (W a i) _ (R.sensor a i) f
  marginal_cross:=fun a b u v=> ⟨(P.queries_marginal s _ x u).1,(P.queries_marginal s _ x u).2,(P.queries_marginal s _ x v).1,(P.queries_marginal s _ x v).2,P.earns_marginal s _ _ x u v (h a b).ordered⟩
  split_costs:=fun _ _ L M h v=> stitchPlan.product_reports x _ _ L M h v }
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.verified_mixtures
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.plan_issued
