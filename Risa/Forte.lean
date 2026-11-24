import LusterS.Rogue
import YM.SU5.Regis.Trophy
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
namespace Risa
open Regis ProbabilityTheory

open Module
variable {χ χ' fuel :ℝ}
variable (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ)(d:0 ≤ t)(g:0<β)
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i,(Precision.K (H.metric.acts n)) i i ≤ t)
def snags{c n:Side} (r:Ratio c n)(m:ℕ)(A:Support c)(D:Finset (Cell n)):ℝ:= 4*(((Fintype.card (Site c):ℝ)*largerBill r.count.val (hallBill m)+(A.card:ℝ)*(r.count.val:ℝ)^4)+(D.card:ℝ)*lusterBill (hallBill m))
lemma snag_price {a:Finset T.Free}(j:Odd r.count.val)(wH:hallBill m≤ r.count.val/2) : (a.card:ℝ)-( (bloom T a A D m).card:ℝ) ≤ snags r m A D:=by
 have ht:bloom T a A D m⊆ a:= fun i h=> inner_part (bloom_sub h)
 have h:=Nat.cast_le (α:=ℝ).mpr (bloom_charge (a:=a) (m:=m) (A:=A) (D:=D) j wH)
 rw [Nat.cast_sub (card_le_card ht)] at h; unfold snags lusterBill; push_cast; push_cast at h; exact h
include D' B L P j wH d g uH I
-- starlight buy. exp toll.rank_diff.Asset
lemma venal {u:(H.metric.acts n).PosDef}(y t' t₀ C₀:ℝ)(W:Altar G n→ℝ)(A:Support c)(D: Finset (Cell n)) {F:Finset T.Free}(z:Buttress T F)
 (a:4*descendCost J β t y*(r.count.val:ℝ)^4 ≤ ξ)(a':4*descendCost J β t y*(lusterBill (hallBill m):ℝ) ≤ χ)(p0:0 ≤ y): let W0:= bloom T F A D m; (cellM T W0 H).PosDef ∧ LogWing n R J q p β v η C S ξ χ ν Λ m A.card D.card W0 H * Real.exp (jewelFee B P W t' C₀ T W0 (t₀+y*snags r m A D)) ≤ Real.exp ((Roof J β n H+rentRoom r R q m p β v η C S Λ (descendCost J β t y)+t₀ + plumeCost B P W t' + trend*C₀^2*t'^2)-ν*D.card):=by
 intro W0; let k:=margin J β t; let d₀:= (Fintype.card G.ColorIndex:ℝ)/2
 let c':=d₀+y; let γ:=descendCost J β t y; let vX:ℝ:=r.count.val; let vS:ℝ:=lusterBill (hallBill m)
 let x0:=4*k*vX^4; let x1:=4*k*vS
 have hk:0≤ k:=pays_hall d; have hd:0 ≤ c':=add_nonneg (by unfold d₀; positivity) p0
 have hxy:x0+4*c'*vX^4 ≤ ξ:=by unfold x0 k c' d₀ vX; unfold descendCost at a; linarith only [a]
 -- fix tactic scope
 have hz:x1+4*c'*vS≤ χ:= by unfold x1 k c' d₀ vS; unfold descendCost at a'; linarith only [a']
 have h0:x0 ≤ ξ:= hxy.trans' (le_add_of_nonneg_right (by positivity))
 have h1:x1 ≤ χ:= hz.trans' (le_add_of_nonneg_right (by unfold vS; positivity))
 let I':Radiance J R q p r.count.val m β κ fuel v' x0 x1 ν v Λ:={I with prompt:=by linarith only [h1,I.prompt], brave:=by linarith only [h0,I.brave], zero_ξ:= by unfold x0; positivity}
 -- get split
 obtain ⟨ho,he⟩:= splitBill (u:=u) L D' I' d g j wH uH A D z (le_refl x0) (le_refl x1)
 have hF:=at_rank B P L (z.precision u).1; have hw:=at_rank B P L ho -- ho is on W0
 let s':= snags r m A D
 have hr: (finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T W0)):ℝ) ≤ s'*Fintype.card G.ColorIndex:=by
    rw [← garden_equiv B P L z,hF,hw]; push_cast; rw [←_root_.sub_mul]; exact mul_le_mul_of_nonneg_right (snag_price j wH) (by positivity)
 refine ⟨ho,?_⟩
 let M(ξ χ:ℝ):=LogWing n R J q p β v η C S ξ χ ν Λ m A.card D.card W0 H
 let R₁:=Roof J β n H
 let C1:=trend*C₀^2*t'^2
 let Q:=plumeCost B P W t'
 let e0:= jewelFee B P W t' C₀ T W0 (t₀+y*s')
 let c2:ℝ:=Fintype.card (Site c); let l:ℝ:=largerBill r.count.val (hallBill m)
 let d2:ℝ:=A.card; let d3:ℝ:=D.card
 let e1:=(x0-ξ)*d2+(x1-χ)*d3
 have hM:M ξ χ=M x0 x1 * Real.exp e1:=by
    unfold M LogWing kiosk; simp_rw [mul_right_comm (_ * _) (chartCost ..) (Real.exp _)] -- tune
    unfold e1 d2 d3; rw [show (_ * Real.exp (_:ℝ)) * Real.exp (_:ℝ) = _ from (mul_assoc ..)] -- inspect
    rw [←Real.exp_add]; congr 3; ring
 change M _ _ * Real.exp e0 ≤ Real.exp (R₁+rentRoom r R q m p β v η C S Λ γ+t₀+Q+C1-ν*D.card); rw [hM,mul_assoc, ← Real.exp_add]; refine le_trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le) ?_; rw [←Real.exp_add]; apply Real.exp_monotone
 -- e0 ≤ t0+ y*snags+Q+C1+d0*s'. bounds
 have hp: e0≤ (t₀+c'*s'+Q+C1):= by unfold e0 jewelFee c' d₀; change (t₀+y*s')+Q+C1 +_≤ _; linarith only [hr]
 have ht: s'=4*(c2*l+d2*vX^4+d3*vS):=rfl
 change R₁ + rentRoom r R q m p β v η C S Λ k - ν* D.card + (e1+e0)≤ _; unfold rentRoom
 unfold e1 at *; unfold γ descendCost; change R₁+(_+_+4*k*c2*l)-_+_ ≤ R₁+(_+_+4*((margin J β t)+(Fintype.card G.ColorIndex:ℝ)/2+y)*c2*l)+_+_+_-_
 let vm:Fintype (Site c):=inferInstance -- noop
 have hγ:(margin J β t+(Fintype.card G.ColorIndex:ℝ)/2+y)=k+c':=by unfold k c' d₀; ring
 rw [hγ]; rw [ht] at hp -- cycle ht at self?
 linarith only [hp,mul_le_mul_of_nonneg_right hxy (show 0≤ d2 from Nat.cast_nonneg _),mul_le_mul_of_nonneg_right hz (show 0≤ d3 from Nat.cast_nonneg _)]
#print axioms venal
end Risa
end YM.Gleam.Luster
