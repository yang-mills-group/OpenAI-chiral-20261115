import YM.SU5.WakeFields.StrokePort
import YM.SU5.WakeFields.PolarLight
import YM.SU5.Exchange.Seed.Pip
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Rue
namespace TreasuryFog

open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open scoped YM.CF.Mew
open Jet Yaw Nor Prism Font Wray Roots Oise Dial
namespace Furrow
variable {I : Type} [Fintype I] [LinearOrder I]
variable {n : Side} {P : BudgetPoint}
    {F F' : Mew.Key I→ ForceBudget n}
    {K : Key I→ Rinse (Seat n) (Copy n)}
    {Y W : Key I → Aura n→ ℝ}{J : Key I → Aura n→ Support (More n)→ℝ} {M : Key I→ Bag n}
    {C:Occlus P} {q : ℕ} {h : ℝ} {σ : I→Seat n}
variable (L : Furrow σ C q F h K Y W J M) (c : ℕ)(p : 1 ≤ h)
open Bake
include L p
-- read ∂E_Z before wake projection at V. allow *mask scope only* on ζ.
open PowerSeries
private lemma primeLayer (X:Aura n)(k:Key I)(l:k∈hill I) : coeff 1 (Cadre.chip (K k) (settleK (F k)) X ∅)= K k X ∅ X 1:=by
 nth_rw 1 [Cadre.peel]
 rw [sprig, Cadre.pingT _ _ _ _ (L.price k l).start]; simp only [Nat.cast_zero,zero_add,inv_one,one_smul,map_add, if_neg Finset.not_nonempty_empty,coeff_zero_C]
 suffices h:coeff 0 (∑ Y:Aura n, _)=(0:Copy n) from by rw [h,add_zero]
 rw [map_sum]; apply sum_eq_zero; intro Y v; rw [Cadre.rils]; refine sum_eq_zero (fun S w=>?_)
 have hG: coeff 0 (∏ j∈S, Cadre.chip (K k) (settleK (F k)) j (∅∩j.val))=0:=by
    rw [PowerSeries.coeff_zero_eq_constantCoeff,map_prod]; obtain ⟨a,q⟩:=(mem_filter.mp (mem_inter.mp w).2).2; apply prod_eq_zero q; rw [←PowerSeries.coeff_zero_eq_constantCoeff,Cadre.peg,empty_inter]; exact settle0 (F k) a
 rw [hG,(L.price k l).start]
variable (i:I)
-- call shape with the literal b(X) including real tag qualification. buy matching exponent.
variable (uBe:c≥1)
include uBe
open Py
-- Derives from Seed/Pip but at all depths even with incoming rack
lemma readPrime (X:Aura n)(V:Orbit n) : tipI (fun z=> spaceSimple F K c z X V) [i]= tipI (fun z=> K z X ∅ X 1 V) [i]:=by
 let I' := range (c+1); let D(j:ℕ)(z:Key I):= (coeff j (Cadre.chip (K z) (settleK (F z)) X ∅)) V
 have e(i):= L.floods i X ∅ (empty_subset _) V; have he(z:Mew.Key I):spaceSimple F K c z X V=∑ j∈I', D j z:= Finset.sum_apply ..
 rw [funext he,(tip_bank I' D (fun j _=>(e j).riv)).2,sum_eq_single_of_mem 1 (mem_range.mpr (Nat.lt_succ_of_le uBe))]
 · exact lace_C _ (fun z w=> congrFun (primeLayer L p X z w) V) roots
 intro b v t; by_cases w:b=0
 · subst b; unfold D; simp_rw [Cadre.peg,settle0]; exact tip_0 _
 exact (e b).ebb [i] (show 1<b from by omega)
lemma primePort (X:Aura n)(V:Orbit n)(g:visible P X.val ∅ V.1) :
 tipI (fun z=> spaceG P F K c z X V) [i] = tipI (fun z=>K z X ∅ X 1 V) [i]:=by
 let θ:=P.supportExponent+C.η+C.η+C.η; have ht:0≤ θ:=by unfold θ; linarith only [P.exponent_pos,C.hη]
 let Z(x)(v:x∈hill I):=(L.rackMoney c p x v).1
 exact (strokes (spaceSimple F K c) P p (fun x y=> L.layerFlow c x _ (empty_subset _) y) (fun z=> urnL (paidLayers (J z) (Y z) (W z) c)) ht Z (fun z w=> (L.layerSuit c p z w).1) (ready_pos Palot.stern P.B (Z _ roots)).le C.degree0 (L.plainOrigin c) X V g i).trans (L.readPrime c p i uBe X V)

variable (τ:Ids n) (E:I → RegBudget n)
open Sault
local notation "YΩ"=>Scree.Hub n
local notation "DK"=>spaceD P F K c τ
local notation "Ψg"=>spaceG P F K c
lemma conducts (v:SpanTip P (E i) (σ i) K τ i)(W:Pane n) : exponentL P (E i) W=exponentL P (νΦX (spaceD P F K c τ) {i}) W:=by
 let V:Orbit n:=(W,τ); let A:= E i; let G:= νΦX DK {i}; let Fv(j:Aura n):= tipI (fun z=>K z j ∅ j 1 V) [i]; let T':=Fv
 have hp(X:Scree.Hub n)(v:pingS P.threshold X.val.2 W):G X W=bassH (lagE X) • (Fv (lagE X)):=by
    let q':= lagE X
    have ht:visible P q'.val ∅ V.1:= hates ((by rw [sdiff_empty]; exact v))
    unfold G Fv; rw [νΦX]; simp_rw [gemI, Mew.Cue, Finset.sort_singleton]; change tipI (fun z=> bassH q' • Ψg z q' V) [i]=_
    simp_rw [←Complex.coe_smul]; rw [tip_C (L.simpleFlow c p (lagE X) V), L.primePort c p i uBe q' V ht]
 unfold exponentL
 let L(r:YΩ):= numbE (P.threshold) r.val.2 (A r) W; let J(r:YΩ):= numbE (P.threshold) r.val.2 (G r) W
 have he(t:YΩ): t∈ web0 (lagE t):= mem_filter.mpr ⟨mem_univ _,rfl⟩
 have hw (Y':YΩ→Cipher n):(∑ i: YΩ,Y' i)=(∑ X' : Aura n,∑ j∈web0 X',Y' j):=by
    rw [← Finset.sum_fiberwise_of_maps_to (s:=univ) (t:=univ) (g:=lagE) (fun i _=>mem_univ _)] -- this is reversed rew on lhs?
 change ∑ i: YΩ,L i=∑ i:YΩ,J i; rw [hw L,hw J]; apply sum_congr rfl; intro j w
 let H:=web0 j; have hb (i:YΩ)(z:i∈H):lagE i=j:=(mem_filter.mp z).2
 by_cases g:pingS P.threshold j.val W; swap
 · rw [sum_eq_zero (s:=H) (f:=L), sum_eq_zero (s:=H) (f:=J)]<;> (intro i v; exact Set.indicator_of_notMem (show W ∉ _ from (show ¬pingS P.threshold (lagE i).val W from by rw [hb i v]; exact g)) _)
 have hx(i':YΩ)(z:i'∈H):J i'=bassH j • T' j ∧ L i'=(if i'.val.1=σ i then T' j else 0):=by
    have h:pingS P.threshold (lagE i').val W:= (hb i' z).symm ▸ g; show J _= _∧ _=_
    unfold J L numbE; rw [Set.indicator_of_mem (show W∈{U|pingS P.threshold i'.val.2 U} from h), Set.indicator_of_mem (show W∈ {U| pingS P.threshold i'.val.2 U} from h),hp i' h]; rw [hb i' z]; refine ⟨rfl,?_⟩
    exact (v.entry i' W h).trans (by rw [hb i' z])
 rw [sum_congr rfl (fun i p=>(hx i p).1),sum_const,ore_D]; rw [← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀] -- maybe fold bassH
 · by_cases g':σ i∈ j.val; swap; · have h:T' j=0:=v.silent j W g g'; rw [h]; refine Finset.sum_eq_zero (fun i p=>?_); rw [(hx i p).2,h]; split <;> rfl
   let a:YΩ:=⟨(σ i,j.val),g'⟩; have ht : a∈ H := mem_filter.mpr ⟨mem_univ _,Subtype.ext rfl⟩; rw [sum_eq_single_of_mem a ht,(hx a ht).2,if_pos]; exact rfl
   intro i' v l; rw [(hx i' v).2]; exact if_neg (fun g=> l (Subtype.ext (Prod.ext g (congrArg Subtype.val (hb i' v)))))
 exact_mod_cast (Finset.card_pos.mpr j.property).ne'
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.conducts
