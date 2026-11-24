import YM.SU5.Exchange.Pilot.Marquet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
-- Head of regulator as mask tile. Copies beyond positive degree 2 included!
variable {h a c:ℝ} {F : InkD n} {i:Scree.Hub n}
lemma Ark.piece {ι:Type*}[LinearOrder ι][Fintype ι](S:Finset ι)(p:1 ≤ h): Ark (poke S) h (h^S.card):=by
 induction S using Finset.induction_on_min with
 |empty=> rw [card_empty,pow_zero,show poke ∅=(1:FC ι) from (Poly.tag_void ..)]; exact Ark.one h
 |insert i S g ih=>
    unfold poke; rw [Poly.tag_min _ _ _ g,card_insert_of_notMem, pow_succ']; exact Ark.opus h p (Ark.blond h p _) ih
    intro v; exact lt_irrefl i (g i v)
abbrev wetPC(P:BudgetPoint)(i:Scree.Hub n)(F:InkD n)(x:Orbit n):FC (Dwell n):=(numbE P.threshold i.val.2 F x.1).val
lemma wetR (p:PressB P i F h a)(u:1≤ h)(g:i.val.2 ⊆ Y.val)(x:Y.val ⊆ X.val): Marque P X Y D (wetPC P i F) h (chi_f P.order*a):=by
 let I:=i.val.2
 let A:=rimR p (zero_le_one.trans u)
 let W(x:Orbit n):=(oV F x).val
 have hw:wetPC P i F=capR P I W:=by
    funext V; unfold wetPC capR numbE; by_cases hp:V∈ pingMask P I; · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show V.1∈{U|pingS P.threshold i.val.2 U} from hp)]
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show V.1∉{U|pingS P.threshold i.val.2 U} from hp)]; rfl -- indentation
 rw [hw]; have hW: Measurable W:=continuous_subtype_val.measurable.comp A.keeps
 have he(X:Orbit n):Sector (camp Y.val) false (W X):=lift_v (life (p.fitted X.1)) fun _ t=> mem_filter.mpr ⟨mem_univ _, g (mem_filter.mp t).2⟩
 by_cases hp: Disjoint I D
 · apply Marque.capMask _ I (g.trans x); refine ⟨⟨hW,he,fun j k _ _ p' _=>?_ ,fun j k _=>?_⟩,?_⟩
   · exact congrArg Subtype.val (p.term j.1 k.1 (agrees_mono p' (Finset.coe_subset.mpr (g.trans x))))
   · exact congrArg Subtype.val (p.gaugeV ..)
   obtain ⟨M,hM,H,h₁⟩:= A.pays; let J(z: Finset (Dwell n))(v:Orbit n):= Pastry.crumb (W v) z • poke z
   let m'(z:Finset (Dwell n)):=M z*h^z.card
   have ha: W=∑ k:Finset _,J k:=by funext i; rw [Finset.sum_apply]; exact (fineShape ((oV F) i)).allP
   have hc(i': Finset (Dwell n)): AuraOp P X D (J i') h (m' i') :=by
      apply AuraOp.sat h (P:=P) (fun i=> Pastry.crumb (W i) i') (poke i') (Ark.piece _ u) (hM i')
      intro V pV S _
      have hS: pingS P.threshold i.val.2 V.1:= (pingFix (g.trans x) pV).mpr hp
      exact (H V (by rw [sdiff_empty]; exact hS) (empty_subset S)).haveP i'
   have hz:(∑ k:Finset _,m' k)= joinV (fun i:Finset (Dwell n)=>h^i.card) M:=sum_congr rfl (fun _ _=>mul_comm ..)
   rw [ha]; exact ((AuraOp.sumR h _ _ _ (fun i _=> hc i)).bigger (zero_le_one.trans u) (hz.trans_le h₁)).pay
 refine ⟨⟨hW.indicator (measurable_fst ping_o.measurableSet),fun i=>?_ ,fun i j p q u v=>?_ ,fun i t p=>?_⟩,?_⟩
 · by_cases p:i∈ pingMask P I; · rw [capR,Set.indicator_of_mem p]; exact he i
   rw [capR,Set.indicator_of_notMem p]; exact Sector.zero _
 · rw [capR,Set.indicator_of_notMem (show i∉ _ from mt (pingFix (g.trans x) p).mp hp),Set.indicator_of_notMem (show j∉_ from mt (pingFix (g.trans x) q).mp hp)]
 · let V:Orbit n:=(Lattice.gauge t i.1, threadG t i.2); have ht:i∉ pingMask P I:=mt (pingFix (g.trans x) p).mp hp; rw [capR,Set.indicator_of_notMem (show V∉_ from mt (pingB i.1 t).mp ht),Set.indicator_of_notMem ht,sauce,singT,win_z,map_zero]
 refine ⟨fun _ _=> 0,fun i j=> le_rfl,fun j=>?_,fun v k Z t i j=>?_⟩
 · simp only [mul_zero,sum_const_zero]; exact mul_nonneg (A.wage (zero_le_one.trans u)) (pow_nonneg (zero_le_one.trans u) _)
 refine Pence.germ (show Pence P.order (fun _:tangD n=> (0:ℂ)) 0 0 from (norm_zero (E:=ℂ)) ▸ Pence.const 0 (0:ℂ)) ?_; filter_upwards [whileLit (Z:=Z) k] with e q; let w:Orbit n:=(pressQ P Z v.1 e,v.2); rw [capR,Set.indicator_of_notMem (show w∉_ from mt (pingFix (i:=w) (g.trans x) q).mp hp)]; rfl
end YM.CF.Sour
