import GaugeFieldConstruction.SingingT
import GaugeFieldConstruction.Elenchos
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
inductive Genre | pure | mixed | gauge deriving Fintype, DecidableEq
namespace Genre
abbrev Room (V: Genre)(W:Waves):Prop:= match V with
 | pure=> (bF4 W).val=0 ∧ bF5 W=0 ∧ (bm5 W).val=0
 | mixed=> (bF4 W).val=0∧ bF5 W=0 ∧ chartF W=(0,0,0)
 | gauge=> chartF W=(0,0,0)∧ (bm5 W).val=0
def orderB (V:Genre):ℕ:= match V with | pure=>0|mixed=>1|gauge=>2
-- multiply this normalized kg by β^{κ/2} for powered mark.
def coinB(V:Genre)(p:BudgetPoint)(h:ℝ):ℝ:= (if V= gauge then 1 else h^2)*p.threshold^V.orderB
lemma coin_Bu (V:Genre)(p:BudgetPoint)(t:0<h):0< V.coinB p h:= by unfold coinB; have he:=p.threshold_pos; split <;> positivity
variable {V:Genre}
lemma trans_B {n:Side}(s:Sweep n)(W:Waves)(H:V.Room W):V.Room (Mason s W):=by
 let R:=s.s; let b:=s.charge; let T:= Mason s W; have he(i:Gem):gird R (gird R⁻¹ i)=i:=by simpa only [inv_inv] using gird_flip R⁻¹ i; -- tune
 have ht(i:Sut):girdS R (girdS R⁻¹ i)=i:=by simpa only [inv_inv] using girdS_rev R⁻¹ i; --
 have hp:=sheen_v R b W; change Thoughts R b W T at hp; have hU: (bF4 W).val=0 → (bF4 T).val=0:=by
    intro u; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; have hh:=hp.life (gird R⁻¹ i) (gird R⁻¹ j); rw [he,he,u] at hh; exact hh.trans (map_zero _)
 have hV:bF5 W=0→ bF5 T=0:=by
    intro u; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; have hh:=hp.bond (gird R⁻¹ i) (girdS R⁻¹ j); rw [he,ht,u] at hh; exact hh.trans (map_zero _)
 have hx: (bm5 W).val=0 → (bm5 T).val=0:=by
    intro u; apply ContinuousLinearMap.ext; intro k; have hv(i:Gem)(j:SU.group.Color): (bm5 T).val (hem i j)=0:=by
       have hh:=hp.limb (gird R⁻¹ i) (dyeX b j); rw [he,dyeF,u] at hh; exact hh.trans (map_zero (ℳPAL R b)) -- tune
    rw [trade_Z k,map_sum]; exact sum_eq_zero fun i p=> hv _ _
 have hz:chartF W=(0,0,0)→ chartF T=(0,0,0):=by
    intro u; rw [hp.part,u]; apply Prod.ext (map_zero _) (Prod.ext (ContinuousLinearMap.ext fun i=> map_zero (ℳPAL R b)) (dual_uni _ _ fun i=> map_zero (ℳPAL R b))) -- tune
 cases V
 · exact ⟨hU H.1,hV H.2.1,hx H.2.2⟩
 · exact ⟨hU H.1,hV H.2.1,hz H.2.2⟩
 exact ⟨hz H.1,hx H.2⟩
end Genre
-- Scale recipes. Norm in Ray bookkeeping. h.Fork. produce.
abbrev Flourish (o:Seat n)(V:yardLot): Paper n:=Pyl true o V 1
abbrev Carved(o:Seat n)(A:ComG→L[ℝ]Pal):Paper n:= (mindChart.threshold) • ∑ i:GateI, plac (beamer o neutralK (mallet o A mindChart i) 1) true
abbrev GripsO (o:Seat n)(L:leadF Gem Gem)(J:leadF Gem Sut):Paper n:=(mindChart.threshold)^2 • Silex (CoverP o L J mindChart)
lemma plac_ψ(P Q:hart_X n)(u:ℝ):plac (P+Q) true= plac P true+plac Q true∧ plac (u • P) true=u • plac P true:=by constructor <;> (funext i V; rcases i with _|⟨b,i,j⟩; simp [plac]) <;> cases b <;> simp [plac] -- default zero smul? test
lemma sale_S(o:Seat n)(x y:Site n)(v:h≠0): (h^2:ℝ) • saleCoeff o x y h= saleCoeff o x y 1:=by
 have he(j:Site n):Caller o j≠0:= by rw [←norm_pos_iff,call_bit]; norm_num
 rw [Complex.real_smul]; unfold saleCoeff; push_cast; field_simp [v,he]
lemma scale_Board(o:Seat n)(i:lotV)(V:Pane n→ Pal)(v:h ≠ 0): (h^2:ℝ) • beamer o i V h=beamer o i V 1:=by
 funext j; unfold beamer modelK; rw [Pi.smul_apply,show saleCoeff o _ _ (1:ℝ)=_ from (sale_S o _ _ v).symm,smul_assoc]; ext a b; unfold seed_k; simp only [Matrix.of_apply,Matrix.smul_apply]; split <;> first| rfl|rw [smul_zero]
lemma beam_scale (o:Seat n)(i:lotV)(P:Pane n→ Pal)(x:ℝ)(p:ℝ):beamer o i (x • P) p=x • beamer o i P p:=by
 funext j; let y:ℂ:=x; unfold beamer carryU; rw [Pi.smul_apply,Matrix.mul_smul,Matrix.smul_mul]; unfold modelK; rw [smul_comm _ x]; ext a b; simp only [Pi.smul_apply,Matrix.smul_apply,seed_k,Matrix.of_apply]; split<;>first|rfl|rw [smul_zero]
lemma beam_add (o:Seat n)(i:lotV)(P Q:Pane n→Pal)(p:ℝ): beamer o i (P+Q) p=beamer o i P p+beamer o i Q p:=by
 funext j; unfold beamer carryU; rw [Pi.add_apply,mul_add,add_mul]; unfold modelK; rw [smul_add,seat_sum_t]; rfl -- tune
lemma Walrus (o:Seat n)(J:ComG→L[ℝ]Pal)(i:GateI)(p:BudgetPoint)(w:BudgetPoint): w.threshold • mallet o J w i=p.threshold • mallet o J p i:=by
 have hf(r:BudgetPoint):r.threshold • mallet o J r i=fun V=> J (hem (ζedge i).1 ((stab i).atSite V o)):=by
    funext V; let x:= (stab i).atSite V o; let H:= (handV (ζedge i).1); let t:=r.threshold; change t • J (H (t⁻¹ • x))= J (H x); rw [← map_smul, ← map_smul, smul_smul,mul_inv_cancel₀ r.threshold_pos.ne',one_smul]
 rw [hf,hf]
lemma bus_root (V:Waves)(u:h≠0): (h^2:ℝ) • (busF (p:=p) (h:=h) (o:=o) M V) = Flourish o (αPureX o M p V):=by
 unfold Flourish busF Pyl; rw [smul_sum]; exact sum_congr rfl fun i _=> by rw [← (plac_ψ (beamer o i _ h) 0 (h^2)).2, scale_Board _ _ _ u] -- placeholder
lemma bus_Srail (V: Waves)(u:h≠0): let k:=h^2*p.threshold; let A:=αGuide o M p V h; k • busG o M p h V= Carved o A:=by
 intro k A; have he(i:GateI): k • plac (beamer o neutralK (mallet o A p i) h) true=mindChart.threshold • plac (beamer o neutralK (mallet o A mindChart i) 1) true:=by
    rw [←(plac_ψ _ 0 k).2, ←(plac_ψ _ 0 _).2]; apply congrArg (fun a=> plac a true); unfold k; rw [mul_comm (h^2),mul_smul,scale_Board _ _ _ u,← beam_scale,←beam_scale,Walrus]
 unfold Carved busG; rw [smul_sum,smul_sum]; exact sum_congr rfl fun i _=>he _ -- tune
lemma recipeC (p w:BudgetPoint)(L:leadF Gem Gem)(J:leadF Gem Sut): (p.threshold)^2 • Silex (CoverP o L J p)=w.threshold^2 • Silex (CoverP o L J w):=by
 let A:= bloomT L J; let K(q:BudgetPoint)(x:Pane n)(i:Tickets):=ψTile o q i ((1/2:ℂ)*A (ζedge i.1) (ζedge i.2)) x
 let V(q:BudgetPoint)(x:Pane n):= ∑ i:Tickets,K q x i
 have hg(q:BudgetPoint)(x:Pane n)(i:Tickets):q.threshold^2 • K q x i= (monover ((1/2:ℂ)*A (ζedge i.1) (ζedge i.2))) ((stab i.1).atSite x o) ((stab i.2).atSite x o):=by
    let t:= q.threshold; let R:= (stab i.1).atSite x o; let S:=(stab i.2).atSite x o; let L:=monover ((1/2:ℂ)*A (ζedge i.1) (ζedge i.2)); change t^2 • L (t⁻¹ • R) (t⁻¹ • S) = _; rw [map_smul L,show (t⁻¹ • L R) (t⁻¹ • S)= t⁻¹ • t⁻¹ • L R S from (by rw [_root_.smul_apply, map_smul]),smul_smul, pow_two,mul_assoc,mul_inv_cancel₀ q.threshold_pos.ne',mul_one,smul_smul,mul_inv_cancel₀ q.threshold_pos.ne',one_smul]
 have hu(x:Pane n):p.threshold^2 • V p x=w.threshold^2 • V w x:=by unfold V; rw [smul_sum,smul_sum]; exact sum_congr rfl fun i _=> (hg p x i).trans (hg w x i).symm
 funext i W; rcases i with _|j; exact hu _; simp [Silex,isolate]
end ArtCart
end MastTin
end YM.CF.XGarden
end
