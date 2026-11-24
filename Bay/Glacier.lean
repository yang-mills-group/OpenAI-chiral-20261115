import Bay.FlowBank
import YM.SU5.Exchange.Seed.Station
import YM.SU5.Interaction.Draught.Taper
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf
open Mew PowerSeries
open scoped YM.CF.Mew
variable {n:Side} {P:BudgetPoint}
open Roots Vow Vow.TreasuryFog Push.AbsoluteSums Trees


/- Generous numbers at large height. U full incidence tariff, H birth, F
   existing Force, α spacing in Support currency, γ steady barrier for Lens. -/
abbrev facetG (P:BudgetPoint)(α:ℝ):ℝ:=P.supportExponent+5*α
abbrev lipG (P:BudgetPoint)(α:ℝ):ℝ:=P.supportExponent+7*α
abbrev giantG (B:ℕ)(α U:ℝ):ℝ:=spanV B * α⁻¹ * U
abbrev θG (B:ℕ)(α γ:ℝ):ℝ:= γ*(1-degreePrice B γ α)⁻¹

structure Glacier (B:ℕ)(α F U H γ:ℝ):Prop where
    pos:0<α
    tiny:5*α ≤ 1
    pay: 0 < γ
    full: 0 ≤ U
    life: F < γ
    fog: γ * spanV B ≤ α
    debt: spanV B*U ≤ α
    share: H + giantG B α U*γ - (α-spanV B*U)*γ<0
    degree : degreePrice B (100*γ) α ≤ 1/2
    base : degreePrice B γ α < 1
    still : θG B α γ ≤ 1
    enough : γ+Real.exp 1*θG B α γ ≤ 100*γ

namespace Glacier
variable {U H α γ f h:ℝ}(g:Glacier P.B α f U H γ)
def oc (P:BudgetPoint){α f U H γ:ℝ}(g:Glacier P.B α f U H γ) : Occlus P where
 κ:=1
 η:=α
 uΓ:=facetG P α
 w:=α

 γ:=γ
 c:=U
 d:=giantG P.B α U
 e:=H
 hη:=g.pos
 hγ:=g.pay
 hw:=by unfold facetG;linarith
 degree:=g.degree
 degree0:=g.base
 still:=g.still
 covers:=g.enough

-- incidence full, birth before gear. use width to bound extra card factor.
include g
lemma frost (C:Aura n→ℝ)(p:0 ≤C)(u:∀ x,tallB C P.B (lipG P α) x≤U)
 (x:Seat n):
 let L:=facetG P α; let W:=Cadre.fog (loom_v L α (widthK n P.B) 0) C γ
 Cadre.nook W x ≤ U ∧ shelfR W x ≤ giantG P.B α U:=by
 intro L W
 have hz:0≤ spanV P.B * α⁻¹ :=mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr g.pos.le)
 have hh(Y:Aura n): W Y ≤ C Y * tact (L+α) P.B Y:=by
    have hu:= (vigor n P.B).rate Y
    unfold W Cadre.fog waveL loom_v Sour.tact
    rw [mul_assoc,← Real.exp_add] -- tune
    apply mul_le_mul_of_nonneg_left _ (p _)
    apply Real.exp_le_exp.mpr
    let B:= widthK n P.B Y
    have h0:0≤ B:=Nat.cast_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left hu g.pay.le,
      mul_le_mul_of_nonneg_right g.fog h0]
 constructor
 · refine le_trans ?_ (u x)
   apply sum_le_sum; intro Y v
   exact (hh Y).trans (mul_le_mul_of_nonneg_left (tact_para (show L+α≤lipG P α by unfold lipG L facetG;linarith [g.pos]) _) (p _))

 apply le_trans _ (mul_le_mul_of_nonneg_left (u x) hz)
 unfold tallB shelfR
 rw [mul_sum]
 apply sum_le_sum
 intro Y _
 apply (mul_le_mul_of_nonneg_right (hh Y) (Nat.cast_nonneg Y.val.card)).trans
 have k:= mul_le_mul_of_nonneg_left (shelf_pay (s:=L+α) (k:=P.B) g.pos Y) (p Y)
 rw [show L+α+α=lipG P α from by unfold L facetG lipG;ring] at k
 change _ ≤ _ * (C Y * tact (lipG P α) P.B Y)
 nlinarith only [k]

-- pig obtained once from Flame
variable {q:ℕ}{K:ForceBudget n}{J:Cusp n}{r:blazeK n}
variable (y:Flame K P h (cipherK q) 1 f J r)
omit g
include y
lemma pig (X:Aura n)(D:Support (More n))(d:D⊆ X.val):
 Fray P h (cipherK q) X D (settleK K X D) (r X D):=by
 by_cases u:D.Nonempty
 · rw [y.card,eachFace _ J X u d] -- tune
   exact y.fray _ _ d
 have t:= y.fray X D d
 rw [not_nonempty_iff_eq_empty.mp u,(y.dead X).1] at t
 rw [not_nonempty_iff_eq_empty.mp u,settle0]
 exact t
/-
-/


include g
lemma warms (w:0≤h)(Z R:Aura n→ℝ)(C:0≤ Z)(D:0≤ R)
 (u:∀ x,tallB Z P.B (lipG P α) x≤U)
 (v:∀ x,tallB R P.B (lipG P α) x≤H):
 Timer (uChip Z R r) Z 1 (facetG P α) α (widthK n P.B) (spanV P.B)
 γ U (giantG P.B α U) H 1 R:=by
 have e:= frost g Z C u
 have hk:0 ≤ facetG P α - α*1:=by unfold facetG; linarith [g.pos,P.exponent_pos]
 have H₀(X:Aura n)(D:Support (More n))(k:D⊆X.val):0≤r X D:=(y.fray X D k).merit.wage w
 refine uGears _ _ _ C D H₀ _ _ _ _ _ _ _ _ _ (vigor ..)
    (fun i=> (e i).1) (fun i=>(e i).2) ?_ le_rfl (Nat.cast_nonneg _) g.pos.le
    g.pay.le g.debt g.full hk g.share ?_
 · intro i
   rw [←parse] -- parse namespace Sour
   exact (Larch.tall_m _ D (show facetG P α - α*0 ≤ lipG P α by unfold facetG lipG;linarith [g.pos]) i).trans (v i)
 intro i
 rw [←parse,age_t,show urnL r=0 from funext fun j=>(y.dead j).2,
     show ∀ a:ℝ,tallB (0:Aura n→ℝ) P.B a i=0 from fun a=>by simp [tallB],
     zero_add,one_mul]

 exact lt_of_le_of_lt ((Larch.tall_m _ (show 0≤ Vow.hymn r from fun _=>sum_nonneg (fun i k=> H₀ _ _ (mem_filter.mp k).2.2))
   (show facetG P α-α*0 ≤ P.supportExponent+1 by unfold facetG; linarith only [g.tiny]) i).trans (y.tall i)) g.life

-- rack proof. economical constants from earned full and birth incidence, pig from force.
variable {I:Type}[LinearOrder I][Fintype I]
lemma dressed (w:0≤h)(W:3 ≤ P.B)(σ:I→Seat n)(M:I→ Sour.Bag n)
 (c d:I→Aura n→ℝ)
 (m:∀ i,Orchard P q h (M i) (c i) (d i))
 (u:Tether σ M)
 (t:∀ i,tallB (riseF c) P.B (lipG P α) i ≤ U)
 (b:∀ i,tallB (riseF d) P.B (lipG P α) i ≤H):
 OrbitRack (oc P g) σ q K h (flare m) (riseF c) (riseF d) r (flareM M):=by
 refine ⟨pig y,fun z a=>(flarePrice m w W z a).1, fun z a=>(flarePrice m w W z a).2,
    flareGamble m,fun l X D _=>flareTurn m (settleK K) σ u l X D,
    flareField m _ (fun X=> by rw [settle0];exact fun _ _=>rfl),
    flareEmpty m _,?_⟩
 exact warms g y w _ _ (fun i=> sum_nonneg fun j _=> (m j i).tube.price)
   (fun i=>sum_nonneg fun j _=> (m j i).forms.choose_spec.1.price) t b
end Glacier
end YM.CF.Bay
#print axioms YM.CF.Bay.Glacier.dressed
