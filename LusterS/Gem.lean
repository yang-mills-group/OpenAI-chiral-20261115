import LusterS.Ruin
import Refrain.Shrift
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)

variable {χ fuel:ℝ}
variable (hD:LocalRatio J)
variable (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ)(g0:2*(r.count.val+1)<n.val)(d:0≤t)(g:0<β)(l:0≤C)
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i,(Precision.K (H.metric.acts n)) i i ≤ t)(he:0<δ)
abbrev LogWing (N:Side)(R:Rules G)(J:ChartRatio G)(q:Clip)(p:BudgetPoint)(β v η C S ξ χ ν Λ:ℝ)(m l d:ℕ)(F:Finset T.Free)(H:Bed):=kiosk N R J q p β v η C S ξ χ ν Λ m l d F.card*chartCost (prism T F H G)⁻¹ (coupling β)
private lemma wing_purchase (h:(cellM T F H).PosDef)(g:0<β)(hD:LocalRatio J) : let M:= LogWing n R J q p β v η C S ξ χ ν Λ m A.card D.card F H; 0<M ∧ Real.log M=(F.card:ℝ) * (Real.log (spare J β)+Λ) - (Fintype.card G.ColorIndex:ℝ)/2*Real.log (cellM T F H).det + taxΔ R q n p β v η C S m - ξ*A.card - (χ+ν)*D.card :=by
 intro M; let F':= J.scale ^ F.card * chartCost (prism T F H G)⁻¹ (coupling β)
 let V:= R.C; let E:= taxΔ R q n p β v η C S m - ξ*A.card - (χ+ν)*D.card; let T:= Real.exp (E+Λ*F.card); have hz: 0<F':= mul_pos (pow_pos hD.scale _) (chartCost_pos _ (PosDef.kronecker h PosDef.one).inv (coupling_pos g))
 have hT: M=F'*T:=by unfold F' M LogWing kiosk T; rw [mul_pow,Real.exp_add, mul_comm Λ _,Real.exp_nat_mul]; unfold E; ring
 rw [hT]; refine ⟨mul_pos hz (Real.exp_pos _),?_⟩; rw [Real.log_mul hz.ne' (Real.exp_pos _).ne',show Real.log T= _ from Real.log_exp _, (show Real.log F'= _ from prism_spec J hD g h)]; unfold E; ring
include B P L hD I g0 d g l j wH uH he
omit B P g0 l he in
lemma splitBill {u:(H.metric.acts n).PosDef} (A:Support c)(D:Finset (Cell n))(H':Buttress T F)(pH:4*margin J β t*(r.count.val:ℝ)^4 ≤ ξ)(hd:4*margin J β t*(lusterBill (hallBill m):ℝ) ≤ χ): let W:= bloom T F A D m; let M:=LogWing n R J q p β v η C S ξ χ ν Λ m A.card D.card W H; (cellM T W H).PosDef ∧ M ≤ Real.exp (Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t)-ν*D.card):=by -- u implicit causing omit param L; make explicit implicit synthesizable?
 intro W M
 let d':= margin J β t; let K:=leasePart (H.metric.acts n); let X:= Real.log (spare J β); let Y:ℝ:=(Fintype.card G.ColorIndex:ℝ)/2
 let i:= Real.log K; let Hf:=cellM T W H; have hh:W⊆ F:= fun i h=>inner_part (bloom_sub h); let Hc:= rentRoom r R q m p β v η C S Λ d'; let D':ℕ:=F.card-W.card; let f:ℝ:=F.card; let c':ℝ:=W.card; let a:ℝ:=Fintype.card (Site c); let B:ℝ:=Fintype.card (Site n)
 have hm : 1 ≤ Fintype.card (Site n):=Fintype.card_pos; have ht :f=3*(B-1):=by unfold f; rw [H'.count,Nat.cast_mul,Nat.cast_sub hm]; push_cast; rfl
 obtain ⟨gH,hZ⟩:= looks H u uH H' hh; refine ⟨gH,?_⟩; obtain ⟨h1,h2⟩:=wing_purchase (A:=A) (R:=R) (H:=H) (p:=p) (v:=v) (η:=η) (C:=C) (S:=S) (ξ:=ξ) (Λ:=Λ) (χ:=χ) (ν:=ν) (D:=D) (m:=m) gH g hD; rw [← Real.log_le_log_iff h1 (Real.exp_pos _),Real.log_exp]; change Real.log M ≤ Roof J β n H + Hc-ν*D.card -- maybe parse
 let x:= largerBill r.count.val (hallBill m); let δ:ℝ:=D.card; let hdv:ℝ:=lusterBill (hallBill m); let y:ℝ:= (r.count.val:ℝ)^4
 have hp : (D':ℝ)=f-c':= Nat.cast_sub (card_le_card hh)
 have hx :(D':ℝ) ≤ 4*((a*x+A.card*y)+δ*hdv):= by
    exact (Nat.cast_le (α:=ℝ).mpr (bloom_charge (a:=F) (D:=D) (m:=m) (A:=A) j wH)).trans (le_of_eq (by unfold a x y δ hdv; push_cast; rfl))
 have hy:0 ≤ f-c':=hp ▸ Nat.cast_nonneg _
 have h':= mul_le_mul_of_nonneg_left hx (pays_hall (J:=J) (β:=β) d)
 -- split I green. t δ etc. absorb
 have hh':Λ*(B) ≥ 0:= mul_nonneg I.green (by unfold B; positivity)
 have hu:c'*Λ ≤ f*Λ:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) I.green
 have hq:= mul_le_mul_of_nonneg_left pH (Nat.cast_nonneg (α:=ℝ) A.card)
 have hX:= mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α:=ℝ) D.card)
 have hk:= mul_le_mul_of_nonneg_right (neg_le_abs X) hy
 change Real.log M=_ at h2; rw [h2]; unfold Hc Roof rentRoom
 change i ≤ Real.log (Hf.det) + t*D' at hZ; rw [hp] at h' hZ
 change c'*(X+Λ) - Y*_ + _ -_-(χ+ν)*D.card ≤ 3*(B-1)*X-Y*i +( _ + 4*Λ*B +4*d'*a*x)-ν*D.card
 have hz:0≤Y:=by unfold Y; positivity
 change d'*(f-c') ≤ d'*(4*((a*x+A.card*y)+δ*hdv)) at h'; change _ * (4*d'*y) ≤ _ at hq; change i≤ Real.log (cellM T W H).det+ _ at hZ; rw [←ht]; rw [show |X|=d'-Y*t by unfold d' Y margin X; ring] at hk
 change δ*(4*d'*hdv)≤δ*χ at hX
 unfold δ at h' hX; unfold hdv at *; linarith only [hk,h',ht,hu,I.green,mul_le_mul_of_nonneg_left ht.le I.green,hh',mul_le_mul_of_nonneg_left hZ hz,hq,hX]

end YM.Gleam.Luster
