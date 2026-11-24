import Anomaly.Apert.Lift
import Anomaly.Apert.Price
import YM.CF.Salt.Rider
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax Rill Ione Clock Salt Mew PowerSeries Sour Turning
attribute [local instance] opCStarAlgebra
open scoped Mew
variable {n N B:Side}
local notation "Ω"=> mid N B
variable {p:BudgetPoint}{q l m:ℕ}{h w μ c d:ℝ} {F: ForceBudget (mid N B)}
variable (s:Sweep (mid N B))
local notation "Vn"=> Aura (mid N B)
open QuadClock Neon Bake Larch

variable {I J:Type}[LinearOrder I][LinearOrder J][Fintype I][Fintype J]
variable {c₀ c₁:Occlus p}{o: I→Site (mid N B)} {u: J→Site (mid N B)}
variable {K: I→ Bag (mid N B)}{G: J→ Bag (mid N B)}
variable {k k' : I→ Aura (mid N B)→ℝ} {v v':J→ Aura (mid N B)→ℝ}
variable (Q:∀ (i:I)(X:Aura (mid N B)),YM.CF.Sour.Flight p q X h (K i X) (k i X) (k' i X)) (T:∀ (j:J)(X:Aura (mid N B)),YM.CF.Sour.Flight p q X h (G j X) (v j X) (v' j X))
local notation "L"=> zealPitch G v v' T
variable {z y :Aura (mid N B)→ℝ}{r: Cadre.Tape (A:=Seat (mid N B))}
    {M: Key I→ Orbit (mid N B)→ Aura (mid N B)→ FC (Dwell (mid N B))}{e f :Aura (mid N B)→ℝ}{t:Cadre.Tape (A:=Seat (mid N B))}
    {Z:Key J→ Orbit (mid N B)→ Aura (mid N B)→ FC (Dwell (mid N B))}
variable (Y:OrbitRack c₀ (Cube.node∘o) q F h (zealPitch K k k' Q) z y r M) (X:OrbitRack c₁ (Cube.node∘u) q F h (zealPitch G v v' T) e f t Z)
local notation "A"=> zealPitch K k k' Q
variable (τ:Ids (mid N B))(i:I)(j:J) (hF:passingF (mid N B) s F F)
    (hE:∀ V:Orbit (mid N B), Injective (priorP V.2)→∀ X:Aura (mid N B),G j (moldA s X) (yellA s V)=sauce s.charge (detX s.s) (γS s) (K i X V))
local notation "ΨE"=> singleReceipt K k k' Q τ i (Cube.node (o i))
local notation "Ψt" => singleReceipt G v v' T τ j (Cube.node (u j))
include hE Q T
lemma marksTurn (e:mPath s (u j)=o i) :∀ V:Orbit Ω,marksCopy p Ψt (yellA s V)=suit_Y s (marksCopy p ΨE V):=by
  have he:(boxA s).symm (node (o i))=node (u j):=by rw [←e,nodeA,Equiv.symm_apply_apply]
  have hp:passingR Ω s ΨE Ψt:= he ▸ peers s Q T τ i j hE
  have ht:dashF s ΨE=Ψt:=by
    funext i v; obtain ⟨i,rfl⟩:= (scope_q s).surjective i; obtain ⟨v,rfl⟩:= (show Surjective (flashA s) from fun v=>⟨flashA s⁻¹ v,by rw [lights,inv_mul_cancel,rev1]⟩) v -- tune
    exact (dash_eq s _ i v).trans (hp i v).symm
  rw [←ht]; exact fun V=>dash_Ek s V _

variable (sW:s∈ Whirl (mid N B))(dv:0≤μ)(dK:0≤w)(h₀: HavenL (mid N B) p l)(w₀: duty_Q p.order p.power≤μ)(w₁:strive_E p.order ≤ μ)(hp:1≤h)
    {Uc:RegBudget (mid N B)}{Pv:ArcΦ}{V: Cusp (mid N B)}{Tv:ℂ}
include sW dv dK h₀ w₀ w₁ hp
lemma moves_C (e:mPath s (u j)=o i)(r:Ice l (o i) p h w c d (marksCopy p ΨE) Uc V Tv Pv): Ice l (u j) p h (μ*w) (μ*c) d (marksCopy p Ψt) (dashF s Uc) (dashK s V) (Spire.payZ s Tv) (arc_s s.s (Levier.spinU false s.s) Pv):= iceBoat s _ _ _ Uc V Pv Tv w c d μ (zero_le_one.trans hp) dK (show Ice l (mPath s (u j)) _ _ _ _ _ (marksCopy p ΨE) _ _ _ _ from (by rw [e]; exact r)) h₀.rooms h₀.period sW w₀ w₁ (Levier.spinU false s.s) (Levier.spinZ ..) (marksTurn s Q T τ i j hE e)
omit sW dv dK h₀ w₀ w₁ hp Q T hE
-- supplement Bond normalization to budgetDisplace. rust genesis and hom.S.
include Q Y hp
lemma birthUnrav (m:ℕ)(i':Key I)(p':i'∈hill I): Unravel p (Jade.nixV (lensCells F A m i')) h:= by
  have he:=layerSuit c₀ F A (Cube.node∘o) q M Y m hp i' p'; have hs:=c₀.hη
  exact ⟨Y.plain i' _, _,_,_,_,_, _,by linarith [p.exponent_pos], (rackMoney c₀ F A (Cube.node∘o) q M Y m hp).1,he.1⟩
include T X hF
open Levier
lemma feudForce (U:I→ Cusp (mid N B))(V:J→Cusp (mid N B))(c:ℝ)(d:∀ V:Orbit Ω,Injective (priorP V.2)→∀ X:Aura Ω,(c:ℂ) • G j (moldA s X) (yellA s V) =sauce s.charge (detX s.s) (γS s) (K i X V)) (u':∀ i,∀ x:Aura (mid N B), node (o i)∉x.val → U i x=0) (v':∀ i,∀ x:Aura (mid N B), node (u i)∉x.val → V i x=0) (a:|c|≤1) (hv:passingU_n Ω s (U i) (c • V j)) : passingF Ω s (emberTip (mkCup p F A m U) i) (c • emberTip (mkCup p F L m V) j):=by
  let W:=mkCup p F A m U
  let Y':= mkCup p F L m V
  have ht (x: ℝ)(w:|x| ≤1) : passingF Ω s (W (realKey i x)) (Y' (realKey j (x*c))):=by
    let v:=realKey i x; let v₂:=realKey j (x*c)
    have he:x*c∈ Set.Icc (-1:ℝ) 1:=abs_le.mp (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) a |>.trans w)
    let pc(i':Key I):=lensCells F A m i'; let pt(i':Key J):=lensCells F L m i'
    have pT:passingU Ω s (pc v) (pt v₂):=by
      apply habit_P s Q T hF v v₂ m
      intro i' h X
      unfold v v₂ realKey; rw [inkRelease,inkRelease]; simp only [Pi.smul_apply]
      rw [Complex.ofReal_mul, mul_smul,d i' h X]; simp only [Complex.coe_smul,sauce, singT,win_r,map_smul]
    have hz: MirrorBill Ω p s (pc v) (pt v₂):= MirrorBill.vest _ _ _ pT (birthUnrav Q Y hp _ _ (realKey_mem _ x w)) (birthUnrav T X hp _ _ (realKey_mem _ (x*c) (abs_le.mpr he))) hp
    apply hz.lamp (Φstack U v) (Φstack V v₂); -- defeq
    intro X u h D hx v'
    have H{R:Type}[Fintype R][LinearOrder R](U:R→ Cusp Ω)(j:R)(x:ℝ): Φstack U (realKey j x)=x • U j:=by unfold Φstack; rw [Finset.sum_eq_single j,realKey, update_self]; rfl; intro k _ v; unfold realKey; rw [update_of_ne v]; exact zero_smul ..; simp
    change Φstack _ v₂ _ _ _=suit_Y s (Φstack _ v _ _ _); rw [H,H,mul_smul]; exact (congrArg (x • ·) (hv X u h D hx v')).trans (map_smul (suit_Y s) x _).symm -- whitespace `_`
  intro Xx x k; exact turnAxis s i j _ _ ((flows_cup A c₀ o Y m U hp u' Xx).2 x) ((flows_cup L c₁ u X m V hp v' _).2 _) c fun y v=>ht y v Xx x k
end YM.CF.Vow.TreasuryFog
