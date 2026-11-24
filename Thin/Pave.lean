import YM.CF.Pso.Mite
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Plume Nor
/-!
# LookZ at arbitrary finite-volume domination constant

Contrary to having to pass changes through the analytic lemmas if using the
coarser LookZ receipts of `Provisions`, we can meet the actual LookZ API by
changing a parameter in it not used by any OTHER fee in the
NoSlip consumption. This is only a mathematical device for supplying an
ae-dominating constant at each given charge, not a useful estimate of c for
another purpose. Fixed sizes, no size issue at all for this constant.
-/


open scoped ENNReal BigOperators
private lemma positive_fiber {E I:Type*} [MeasurableSpace E][Fintype I](ρ:Measure E)
    [IsProbabilityMeasure ρ](f:E→I):∃ i: I, 0<ρ.real (f ⁻¹' {i}) := by
  by_contra! p
  have he : (⋃ i:I,f ⁻¹' {i}) = Set.univ :=Set.eq_univ_iff_forall.mpr fun y=> Set.mem_iUnion.mpr ⟨f y,rfl⟩
  have h(i:I) : ρ (f ⁻¹' {i}) = 0 := by
    refine (measureReal_eq_zero_iff ?_).mp (le_antisymm (p i) measureReal_nonneg)
    exact measure_ne_top _ _
  have hv := measure_iUnion_null h
  rw [he,measure_univ] at hv
  exact one_ne_zero hv

-- Exact target magnitude for the stamp denominator at arbitrary (common) fee j.
private lemma poll (K:ℕ) : ∃ L:ℝ,0<L ∧∀ y:ℝ, degreePrice K y 1=L*y:= by
  have h:= Animals.neighbors_ge K
  refine ⟨4*↑(Animals.ballCost K),by positivity,?_⟩
  intro y
  simp only [degreePrice,Trees.stretch,div_one,mul_assoc]

private lemma solve (K:ℕ)(v:ℝ)(p:0<v): ∃ c:ℝ,
    c*degreePrice K c 1 ^0*(1-degreePrice K c 1)⁻¹ = v := by
  obtain ⟨L,he,t⟩:= poll K
  have ht:1+v*L≠0:=(by positivity)
  let c:=v/(1+v*L)
  refine ⟨c,?_⟩
  simp only [pow_zero,mul_one,t]
  have h0:1-L*c ≠0:= by unfold c; field_simp; ring_nf; rw [mul_comm]; exact inv_ne_zero ht
  unfold c at *; field_simp; ring

private lemma towards {E I:Type*} [MeasurableSpace E][Fintype I](ρ:Measure E)
    [IsProbabilityMeasure ρ](f:E→I)(b C c:ℝ)(K:ℕ)(v:c*degreePrice K c 1 ^0*(1-degreePrice K c 1)⁻¹=b)
    (hp:0 < b)(hk:0<C): b/C ≤ tollW' ρ f c C K:=by
  obtain ⟨i,h⟩:= positive_fiber ρ f
  have he:ρ.real (f ⁻¹' {i}) ≤ 1:=by
    apply (measureReal_mono (Set.subset_univ _)).trans
    rw [Measure.real,measure_univ,ENNReal.toReal_one]
  have hz:ρ.real (f ⁻¹' {i}) ≠0:=ne_of_gt h
  unfold tollW'; rw [v]
  simp only [abs_of_nonneg (div_nonneg hp.le hk.le)]
  refine le_trans ?_ (single_le_sum (s:=Finset.univ) (a:=i) (fun j _=>div_nonneg (div_nonneg hp.le hk.le) measureReal_nonneg) (mem_univ i))
  exact (le_div_iff₀ h).mpr (mul_le_of_le_one_right (div_nonneg hp.le hk.le) he)


/-- Magnify to meet a full LookZ bill with one parameter `c`, on this finite pair
(no estimate at all for c as sizes grow). All numerators of the fee chosen
independently of C. -/
theorem paveThin (S:StepData (Domain N B) (Domain P B))(p:BudgetPoint)(σ:ℝ)(v:0<σ)(Z1 Z2:ℕ)(ℓ c X:ℝ) (K:ℕ) :
    ∃ z:ℝ,∀ C:Palot.leaf (Site (Domain N B)),X ≤ pave_ Z1 Z2 σ z c ℓ S p C K :=by
  let A:=Palot.leaf (Site (Domain N B))
  let markU(i:A):=surgeL p i.val K * liftR p i.val K 1
  have h(i:A):0< markU i:=by unfold markU surgeL liftR Jet.composeCost surgeL; positivity
  let y(i:A):= Trees.currency K c i.val
  have Y(i:A):0<y i:=Real.exp_pos _
  let U(i:A):= ((|X|+1)/markU i*y i)
  let d:ℝ:=1+∑ i:A,U i
  have k(i:A):0<U i:=mul_pos (div_pos (by positivity) (h i)) (Y i)
  have e:0<d:=by unfold d; exact add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun i _=> (k i).le)
  obtain ⟨b,t⟩:= solve K d e
  refine ⟨b,?_⟩
  intro i
  have z: U i ≤ d:= (single_le_sum (fun i _=> (k i).le) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  let R:= plummy S σ
  letI : IsProbabilityMeasure R:= plum_p S v
  letI : Finite ↥(Sil S Z2):= Set.Finite.to_subtype sill_p
  letI : Fintype ↥(Sil S Z2):= Fintype.ofFinite _
  let Q:= fun r:Cord S=> stamp r Z1 ℓ Z2
  have u : X ≤ markU i * |tollW' (plummy S σ) Q b (y i) K|:= by
    refine (le_abs_self _).trans ?_
    have hh : (|X|+1)/markU i ≤|tollW' (plummy S σ) Q b (y i) K| :=
      ((le_div_iff₀ (Y i)).mpr z).trans ((towards R Q d _ b K t e (Y i)).trans (le_abs_self _))
    nlinarith only [div_mul_cancel₀ (|X|+1) (ne_of_gt (h i)), h i,h i |>.le,
     mul_le_mul_of_nonneg_right hh (h i).le]
  unfold pave_ mow_z
  -- Fintype proof irrelevance? Fintype subsingleton not defeq. use cases
  convert! u using 1
  rw [abs_of_pos (h i)]

end YM.CF.Jade
