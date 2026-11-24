import GaugeFieldConstruction.ObBank3
import GaugeFieldConstruction.Lunch3
import GaugeFieldConstruction.WoolSock3
import GaugeFieldConstruction.FateH3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Iona Isle Rio Py Nor Py.Riant
variable (P:BudgetPoint)(σ:I→ Seat n)
-- budget template.Q poses all.
section
variable (F: KK I (Copy n) n) (W0: Finset I→Vow.Pax n)(Q0: Finset I→ Vow.Cusp n)(U0:RegBudget n)(A:XE I (InkD n) n)(X0:Rio I n)
variable (Q:LeaseQ γ n)(L K:ℕ){J:Type}[Fintype J](C:I→J→Factor3 n)(r h a ℓ E Ω η δ u:ℝ)(k:ℕ)
variable (S:Ids n)
section
variable (T : KI I n→ℝ)(V Y:WA3 I n→ℝ) (fV:BillF P σ h r K T F)(p: Plen_E P σ W0 Q0 h r V Y)(uV:0≤ V)(uY:0≤Y)(hr:0<r)(h₀:1≤h)
local notation "B"=> P.B
local notation "βF"=> Outbank P.B a η V Y T
-- timeline.W seats all proofs.Gear.Primary Orientation.Coating.B permissions epoch readiness _
structure Momentum3 (U:γ→ℝ)(A:I→J→ℝ)(s:Finset I):Prop where
    act(i:I)(u':i∈s)(j:J):Act3 (C i j) P K h (A i j)
    leased : Leased Q P K h U
    costs(i)(u:i∈s): let V:=Platform Q (C i) P L; (∑ j:Actors Q (C i), Win3 Q (C i) r U (A i) j*Summit P.B a (spark3 Q (C i) P L j).val.2) ≤ ℓ
    pos(i)(u:i∈s)(j):0 ≤ A i j
    ge:0 ≤ U
    aligns(i)(u':i∈s)(j):(C i j).H.val.1=σ i
variable (U:γ→ℝ)(V0:I→J→ℝ)(s:Finset I)(P0:Momentum3 P σ Q L K C r h a ℓ U V0 s)
def penStep (X:Rio I n)(i:I):= purchase3 (Frame3 σ W0 Q0 X) Q i (FortX3 F X) (C i) (Platform Q (C i) P L) S σ
def Book3 (l:List I):Rio I n:= List.foldl (fun x i=> x+penStep P σ F W0 Q0 Q L C S x i) 0 l
local notation "Hm"=>penStep P σ F W0 Q0 Q L C S
local notation "ΞΩ"=>Book3 P σ F W0 Q0 Q L C S
lemma Book3_cons (l:List I)(i:I) : ΞΩ (l++[i])=ΞΩ l+Hm (ΞΩ l) i:=by unfold Book3; rw[List.foldl_append]; rfl
include fV p uV uY hr h₀ P0
lemma Build_law (v:0<η)(b:0≤Ω)(t:Cube_M P.B*Ω≤1)(l:List I)(pL: l.toFinset⊆s): WarpL P σ r h K P.B a η ℓ Ω (Outbank P.B a η V Y T) (l.map σ) (Book3 P σ F W0 Q0 Q L C S l):=by
 induction l using List.reverseRecOn with
 | nil=> exact WarpL.empty
 | append_singleton l i ih=>
    let X:= ΞΩ l; have hv:i∈s:=pL (by simp); rw [List.map_append,Book3_cons]; refine WarpL.step (ih (fun x t=>pL (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp t))))) ?_
    let WQ:= Frame3 σ W0 Q0 X; let W':= FortX3 F X; let A:= Craft3 WQ Q i W' (C i) (Platform Q (C i) P L) S
    have hc(z:Actors Q (C i)): (A z).anchor.val.1=σ i:=(congrArg (fun x:Hub n=>x.val.1) (placeH WQ Q i W' (C i) P L S z)).trans (P0.aligns i hv z.1)
    refine vintage σ A P h r K (σ i) hc X (Outbank P.B a η V Y T) a η ℓ Ω P.B b t hr v ?_
    intro X' H'; obtain ⟨rπ,Zt⟩:= Libero P σ F W0 Q0 X h r hr V Y K T fV X' H' p uV uY -- shadow r!
    obtain ⟨B₀,M₀⟩:= Maxim3 P σ F W0 Q0 X h _ hr V Y K T fV X' H' p uV uY; refine ⟨Win3 Q (C i) r U (V0 i),_,_,B₀,M₀,?_,?_,?_⟩
    · exact fun j=> (yH WQ Q i W' (C i) (Platform Q (C i) P L) S σ P rπ (P0.act i hv) P0.leased (fun j=>padd_on Q _ P L) Zt (P0.aligns i hv) h₀ hr M₀ B₀ P0.ge (P0.pos i hv) j).1 -- tune
    · have h:=P0.costs i hv; change _ ≤ ℓ; refine (le_of_eq ?_).trans h; apply sum_congr rfl; intro j _; unfold A; rw [placeH]
    exact seasonalT P σ F W0 Q0 X V Y T X' a η
-- boot weights and peel.F.Calendar sliced.
local notation "mΦ"=> Flow4 k P.B
variable (z0:ℝ)(mZ:η=Eta4 k P.B)
variable (q:0 ≤ Ω)(hq:Boot4 P.B Ω η ℓ z0 (Flow4 k P.B)) (D pX:List I)(v:D.toFinset ⊆ s)(sU:supplyL k σ (D++pX))(z₁:0 ≤ a)(ht:∀ i:Seat n, postG pastMask (V+Y) (March P.B (a+7*ζd)) i + pointX cloudK T (March P.B (a+7*ζd)) i ≤ z0)
local notation "YΞ"=> ΞΩ D
include z₁ mZ q hq v sU ht
lemma ReceiptT : ∃ Z:CashI I n, Weighted P σ r h K (Book3 P σ F W0 Q0 Q L C S D) Z∧∀ i:Seat n, Paw P.B a η Z (pX.map σ) i ≤ ℓ*Flow4 k P.B ∧ Rio.Band P.B a η Z (pX.map σ) i ≤ advanceC ℓ η*z0+stolon P.B Ω η ℓ*Flow4 k P.B :=by
 let Γ:=βF; have hn:0≤Γ:= fun i y=>add_nonneg (sum_nonneg fun j _=>mul_nonneg (add_nonneg (uV _) (uY _)) (Temp_p ..|>.le)) (pointX_gene _ _ fV.gist _ (fun _=>Temp_p ..|>.le) y)
 have he:0<η:= mZ.symm ▸ (etaP4 ..)
 have tv(F L:List I)(a: supplyL k σ (F++L)): supplyL k σ F:=by
    refine ⟨List.Nodup.of_append_left a.1,fun i=>?_⟩; apply le_trans _ (a.2 i); apply Finset.card_le_card; intro j z; obtain ⟨u,h⟩:=mem_filter.mp z; exact mem_filter.mpr ⟨by simp only [List.toFinset_append]; exact mem_union_left _ u,h⟩
 obtain ⟨K',hd⟩:=Frank σ a k P.B _ sU z₁
 let F':=pX.map σ; let D':=D.map σ
 have hz:Lattice.Corona.Hive.Scales P.B a η (D'++F'):=by unfold F' D'; rw [←List.map_append,mZ]; exact hd
 have hD:= (Frank σ a k P.B _ (tv D pX sU) z₁).1
 have hw: WarpL P σ r h K P.B a η ℓ Ω Γ D' YΞ:= Build_law P σ F W0 Q0 Q L K C r h a ℓ Ω η S T V Y fV p uV uY hr h₀ U V0 s P0 he q hq.2.1 D v -- tune
 have QΛ :∀ i, Γ (D'++F') i ≤ z0:=by
    intro i; apply le_trans _ (ht i); unfold Γ Outbank
    have e(x:Support (More n))(m:ℝ)(u:m ≤6):tempI P.B (a+m*ζd) η (D'++F') x ≤ March P.B (a+7*ζd) x:=by
       unfold tempI March; rw[←Real.exp_add]; apply Real.exp_monotone; have he:= hz.toll x; let b:=heft P.B x; have hb:0≤b:= Nat.cast_nonneg _; nlinarith only [he,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right u ζdp.le) hb]
    refine add_le_add (sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (e _ _ (show (6:ℝ)≤6 from le_rfl)) (add_nonneg (uV _) (uY _)))) (pointX_up cloudK T fV.gist _ _ (fun i=>e i _ (by norm_num: (2:ℝ)≤6)) _)
 have hs(i:List (Seat n))(y o:Seat n):Γ i y≤ Γ (o::i) y:=by
    unfold Γ Outbank; refine add_le_add (sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (Temp_mono _ _ _ _ _ he.le _) (add_nonneg (uV _) (uY _)))) (pointX_up cloudK T fV.gist _ _ (fun k=>Temp_mono _ _ _ _ _ he.le _) _)
 obtain ⟨Z,H,Q⟩:= Rio.pressure P σ r h K P.B a η ℓ Ω Γ F' D' YΞ mΦ z0 hq.2.2.2.2 hq.1 he hq.2.2.2.1 q hn hs hw QΛ hz hD
 have h0:0≤advanceC ℓ η:= by have h:=hq.1; unfold Rio.advanceC; positivity
 refine ⟨Z,H,fun i=>⟨(Q i).1.trans (mul_le_mul_of_nonneg_left (hD i) hq.1),?_⟩⟩
 exact (le_add_of_nonneg_right (mul_nonneg h0 (add_nonneg (show 0≤Γ _ _ from hn _ _) (H.estate (d:=P.B) (a:=a) he.le _ i|>.1)))).trans ((Q i).2.trans (add_le_add (mul_le_mul_of_nonneg_left (QΛ i) h0) (mul_le_mul_of_nonneg_left (hD i) (Sl_Pos _ _ _ _ hq.1 he q))))
#print axioms Build_law
end
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
