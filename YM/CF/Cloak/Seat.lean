import YM.CF.Tarn.Loops
import YM.CF.Cloak.Mint
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Vol Pressure.Tube
section orient
variable (T:Tube G S)(U:Config G f)(V:Config G c)(s:Signed)(A:Stores S)(q:Chi)(F W:BudgetPoint)(x α β:ℝ)
open Vol
local notation "u₀"=> pull s 0 U
local notation "V'"=> pull s 0 V
local notation "a₀"=> (turnStore s A).costs
local notation "t₀"=> F.threshold
local notation "r₀"=> Stores.till x
local notation "u"=>S.patch.L.val
local notation "H₀"=>r₀/u
local notation "s₀"=>W.threshold
local notation "Q₀"=>traceZ (turnStore s A).flags
def park(P:ℕ→RG.Atom G r)(j:Site f):=∑' i,lush_k q (P i) a₀ t₀ j u₀
def visit(P:ℕ→RG.Atom G r)(j: Site c):=∑' i,peer_k (P i) Q₀ s₀ j V'
local notation "gY"=>fun {r:ℕ} (P:ℕ→ RG.Atom G r)=>park U s A q F P
local notation "VY"=>fun {r:ℕ} (P:ℕ→ RG.Atom G r)=>visit V s A W P
def leftV(i: Site f):= β*((∑' j,sleeve (rod T.up r₀ j) a₀ T.high i t₀ u₀)+ ((park U s A q F (haste r₀ T.up.cubic) i)+(park U s A q F (haste r₀ T.up.quartic) i)))+ park U s A q F (haste r₀ T.up.loop) i
def rightV(i: Site c):= (β+α)*((∑' j,sleeve (rod T.down H₀ j) Q₀ T.low i s₀ V')+ (visit V s A W (haste H₀ T.down.cubic) i+visit V s A W (haste H₀ T.down.quartic) i))+visit V s A W (haste H₀ T.down.loop) i+α*(visit V s A W (batch T.down.cubic H₀) i+visit V s A W (batch T.down.quartic H₀) i)
def heatR(i:Cay.Along S):ℝ:=match i with
 | .inl (.inr (.inr (.inl i)))=> -α * king Q₀ T.down T.low r₀ u s₀ V' i
 | .inl _ =>0
 | .inr (.inl i)=> park U s A q F (batch T.up.loop r₀) i
 | .inr (.inr i)=> - visit V s A W (batch T.down.loop H₀) i
variable {U V F W A x}{K:Teller G} (p:Mowed S A x U V)(hp:K.Funds S T)(hf: F.threshold=fiery G x S.patch.L)(h:W.threshold=temp x)(hu:0< F.threshold)
include p hf hu
lemma spice (P:ℕ→RG.Atom G r)(j:Site f): park U s A q F P j=PathData.atomSeries P F u₀ j:=by
 apply tsum_congr; intro i; exact sonK (P i) u₀ _ q _ _ j rfl hu fun w g=> (mowed_f s p _ (mem_sdiff.mp g).2).trans (by rw [hf])
omit hf hu
include h
lemma spliceV(P:ℕ→RG.Atom G r)(j:Site c): visit V s A W P j=PathData.atomSeries P W V' j:=by
 apply tsum_congr; intro i; exact sunK (P i) _ _ _ _ fun w g=> (mowed_c _ p _ (mem_sdiff.mp g).2).trans_eq h.symm -- tune implicit s
lemma stilt(j:Cell c): king Q₀ T.down T.low r₀ u s₀ V' j=crown T.down T.low r₀ u s₀ V' j:=by
 rw [h]; have hp:0 ≤ temp x:= temp_nonneg _; exact crownK _ _ _ _ _ _ _ _ hp (shipP _ _ _ _ _ hp (mowed_c s p)).symm (or_iff_not_imp_left.mpr fun g=> mowed_c s p j g)
include hp hu hf
lemma pool : lowP T.up T.high F 1 r₀ r₀ β u₀-lowP T.down T.low W u r₀ H₀ (β+α) V'-α * peakP T.down T.low W u r₀ H₀ V'=(∑ i,leftV T U s A q F x β i)-(∑ i,rightV T V s A W x α β i)+∑ i:Cay.Along S, heatR T U V s A q F W x α i:=by
 obtain ⟨κ,v,P,Y⟩:=hp.feeds; rw [←hp.high] at P; rw [←hp.low] at Y
 have he(i:Site f):(∑' j,sleeve (rod T.up r₀ j) a₀ T.high i t₀ u₀)= ∑ z,cuff T.up T.high F 1 r₀ u₀ (i,z):=by have hp(x):=mowed_f s p x; have hx:=sleeve_p (B:=F) i P 1 r₀ (Nat.zero_lt_one) u₀ t₀ rfl a₀ ((shipP t₀ u₀ a₀ _ i hu.le (fun i H=> (hp _ H).trans (by rw [←hf]; exact half_le_self hu.le))).symm); simpa only [Nat.div_one] using hx
 have hw(i:Site c):= sleeve_p (B:=W) i Y u r₀ S.patch.L.property V' s₀ rfl Q₀ ((shipP s₀ V' Q₀ _ i (by rw [h]; exact temp_nonneg _) (fun i t=> h.symm ▸ mowed_c s p i t)).symm)
 have hx: (∑ i:Cay.Along S,heatR T U V s A q F W x α i)= (∑ i:Cell c, -α* crown T.down T.low r₀ u s₀ V' i)+((∑ i:Site f,park U s A q F (batch T.up.loop r₀) i)-(∑ i:Site c,visit V s A W (batch T.down.loop H₀) i)):=by
    unfold Cay.Along Slate.Dill; simp_rw [Fintype.sum_sum_type]; unfold heatR
    simp only [sum_const_zero,zero_add,add_zero]; simp_rw [stilt T s p h]; simp only [sum_neg_distrib]; abel
 rw [hx]; unfold Reine.lowP peakP leftV rightV clippedP dashK; change _= _
 simp_rw [he,hw, spice s q p hf hu,spliceV s p h]; have h2:=fun i=> exteriorL r₀ _ u₀ F P.width P.two i -- tune lambda binder implicit P
 have h3:=fun i=> exteriorL r₀ _ u₀ F P.width P.three i; have h4:=fun i=> exteriorL r₀ _ u₀ F P.width P.four i
 have hq:=fun i=> exteriorL H₀ _ V' W Y.width Y.two i; have hz:=fun i=> exteriorL H₀ _ V' W Y.width Y.three i; have hK:=fun i=> exteriorL H₀ _ V' W Y.width Y.four i
 unfold Reine.clippedP; simp_rw [h2,h3,h4,hq,hz,hK]; simp only [Pressure.Cell, Lattice.Face,Fintype.sum_prod_type,sum_sub_distrib,sum_add_distrib,← mul_sum]; ring -- tune
end orient
end YM.CF.Cloak
