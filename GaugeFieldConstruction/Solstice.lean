import GaugeFieldConstruction.Splint

/-! # Pay gauge rent under localized aggregate mark perturbation. Adapt Inlets & Danube,
     determinant of unperturbed already licensed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)


variable {Wa Da:Flaws n}{κ' k f₁ f₂ q':ℝ}{W:Altar G n→ℝ}{τ b Q:ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) (I:TopPrice J R q p r.count.val m β κ k f₁ f₂ v Λ q')
variable (g:0<β)(d:0≤ κ')(l:0≤ C)(j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)

private lemma seal_K (h:(cellM T F H).PosDef)(g:0<β)(D:LocalRatio J) : let M:= daySeal n R J q p β v η C S Λ m Wa Da f₁ f₂ F.card * chartCost (prism T F H G)⁻¹ (coupling β); 0<M ∧ Real.log M=(F.card:ℝ) * (Real.log (spare J β)+Λ) - (Fintype.card G.ColorIndex:ℝ)/2*Real.log (cellM T F H).det + (billA R q n p β v η C S m Wa Da f₁ f₂) :=by
 intro M; let F':= J.scale ^ F.card * chartCost (prism T F H G)⁻¹ (coupling β)
 let V:= R.C; let E:= (billA R q n p β v η C S m Wa Da f₁ f₂); let T:= Real.exp (E+Λ*F.card); have hz: 0<F':= mul_pos (pow_pos D.scale _) (chartCost_pos _ (PosDef.kronecker h PosDef.one).inv (coupling_pos g))
 have hT: M=F'*T:=by unfold F' M daySeal T; rw [mul_pow,Real.exp_add, mul_comm Λ _,Real.exp_nat_mul]; unfold E; ring
 rw [hT]; refine ⟨mul_pos hz (Real.exp_pos _),?_⟩; rw [Real.log_mul hz.ne' (Real.exp_pos _).ne',show Real.log T= _ from Real.log_exp _, (show Real.log F'= _ from prism_spec J D g h)]; unfold E; ring

include B P D I L d g j wH uH
private lemma rayCapital {K':(H.metric.acts n).PosDef}(Wa Da:Flaws n)(H':Buttress T F) : let Wa0:= accRoom T F (grid_break r Da) Wa m;
               let M:=daySeal n R J q p β v η C S Λ m Wa Da f₁ f₂ Wa0.card * chartCost (prism T Wa0 H G)⁻¹ (coupling β); (cellM T Wa0 H).PosDef ∧ M*Real.exp (jewelFee B P W t b T Wa0 Q) ≤ Real.exp (Roof J β n H + 4*Λ*(Fintype.card (Site n):ℝ) + (descendCost J β κ' 0)*(4* (wallTax (grid_break r Da) Wa r (hallBill m) :ℝ)) + billA R q n p β v η C S m Wa Da f₁ f₂ + Q + plumeCost B P W t + trend*b^2*t^2):=by
 intro W0 M

 let d':= descendCost J β κ' 0; let K:=leasePart (H.metric.acts n); let X:= Real.log (spare J β); let Y:ℝ:=(Fintype.card G.ColorIndex:ℝ)/2
 let i:= Real.log K; let Hf:=cellM T W0 H; have hh:W0⊆ F:= filter_subset ..; let Hc:= rentRoom r R q m p β v η C S Λ d'; let D':ℕ:=F.card-W0.card; let f:ℝ:=F.card; let c':ℝ:=W0.card; let a:ℝ:=Fintype.card (Site c); let B₀:ℝ:=Fintype.card (Site n)
 have hm : 1 ≤ Fintype.card (Site n):=Fintype.card_pos; have ht :f=3*(B₀-1):=by unfold f; rw [H'.count,Nat.cast_mul,Nat.cast_sub hm]; push_cast; rfl
 obtain ⟨gH,hZ⟩:= looks H K' uH H' hh; refine ⟨gH,?_⟩; obtain ⟨h1,h2⟩:=seal_K (Wa:=Wa) (Da:=Da) (R:=R) (H:=H) (p:=p) (v:=v) (η:=η) (C:=C) (S:=S) (Λ:=Λ) (m:=m) gH g D; rw [← Real.log_le_log_iff (mul_pos h1 (Real.exp_pos _)) (Real.exp_pos _),Real.log_mul h1.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp];
 let x:= largerBill r.count.val (hallBill m); let y:ℝ:= (r.count.val:ℝ)^4
 have hp : (D':ℝ)=f-c':= Nat.cast_sub (card_le_card hh)

 let N:= wallTax (grid_break r Da) Wa r (hallBill m); let Z0:= d'*(4*(N:ℝ))
 have hxcard : f-c' ≤ 4*(N:ℝ):=by
    rw [← hp]; exact_mod_cast accRoom.tall (F:=F) (L:=Wa) (A:=grid_break r Da) j wH
 have h':d'*(f-c') ≤ Z0:=mul_le_mul_of_nonneg_left hxcard (show 0≤d' from by unfold d' descendCost; have t' := pays_hall (J:=J) (β:=β) d; positivity)
 have hy:0≤ f-c':=hp ▸ Nat.cast_nonneg _
 have hh':Λ*(B₀) ≥ 0:= mul_nonneg I.green (by unfold B₀; positivity)
 have hu:c'*Λ ≤ f*Λ:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) I.green
 have hk:= mul_le_mul_of_nonneg_right (neg_le_abs X) hy
 change Real.log M=_ at h2; rw [h2]; unfold Roof
 change i ≤ Real.log (Hf.det) + κ'*D' at hZ; rw [hp] at hZ
 change c'*(X+Λ) - Y*_ + _ + jewelFee B P W t b T W0 Q ≤ 3*(B₀-1)*X-Y*i + 4*Λ*B₀+ Z0+_ +_ +_ +_
 have hz:0≤Y:=by unfold Y; positivity
 change i≤ Real.log (cellM T W0 H).det+ _ at hZ; rw [←ht]; unfold jewelFee
 have uT: (cellM T F H).PosDef:= (H'.precision K').1
 have hF:=at_rank B P L uT; have hw:=at_rank B P L gH; rw [← garden_equiv B P L H',hF,hw]; push_cast only [Nat.cast_mul]
 have hx : |Real.log (spare J β)|=d'-Y*κ'-Y:=by unfold d' Y descendCost margin; ring
 let C' := Fintype.card G.ColorIndex; rw [show |X| = _ from hx] at hk
 change (_ :ℝ) + (Q +_ +_ + ((f*(C':ℝ)-c'*(C':ℝ))/2)) ≤ _
 have hw : (C':ℝ) = 2*Y:= by unfold Y C'; ring
 linarith only [hk,hh',ht,hu,mul_le_mul_of_nonneg_left hZ hz,h', I.green,mul_le_mul_of_nonneg_right ht.le I.green,mul_le_mul_of_nonneg_right hw.ge hy,mul_le_mul_of_nonneg_right hw.le hy]

omit L B P I D g j wH uH d
def sunkV (J:ChartRatio G)(q:Clip)(β κ':ℝ) := 4*(descendCost J β κ' 0) -- nonneg
-- volume debt not including any holes
abbrev cutRate (J:ChartRatio G)(R:Rules G)(q:Clip)(p:BudgetPoint)(r:Ratio c n)(m:ℕ)(κ' β v Λ η C S:ℝ) := taxΔ R q n p β v η C S m + 4*Λ*(Fintype.card (Site n):ℝ) + sunkV J q β κ'*rimTax (∅:Support c) r (hallBill m)
-- per hole in each currency
abbrev reachΔ (J:ChartRatio G)(R:Rules G)(q:Clip)(m:ℕ)(β κ':ℝ):= sunkV J q β κ' *((2*hallBill m+1)^4:ℕ)
abbrev castΔ (J:ChartRatio G)(R:Rules G)(q:Clip)(r:Ratio c n)(β κ':ℝ):= sunkV J q β κ' * (21^4*r.count.val^4:ℕ)
lemma no_trouble (h:0 ≤ κ'): 0 ≤ sunkV J q β κ':=by unfold sunkV descendCost; have he:=pays_hall (t:=κ') (J:=J) (β:=β) h; positivity
include B P D I L d g j wH uH u l he
variable (g0:2*(r.count.val+1)<n.val) {Wake Weight:ℝ} -- post-deduction head exponent Alpha/Beta
-- Phi may depend on the choices. use a single Φ here, masks built in ψ.
include g0
lemma one_house (Wa Da:Flaws n)(H':Buttress T F)(W:Altar G n→ℝ)(t b₁ b₂ Q:ℝ)(a:ContDiff ℝ 1 W)(h1: ∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
   (V: Clarity B P p T m Wa Da q' β v Q t φ W) : (∫ x,day_play Z q p Wa Da T β κ k q' φ x ∂T.order G) ≤ Real.exp (Roof J β n H + cutRate J R q p r m κ' β v Λ η C S + (reachΔ J R q m β κ' - f₁)*(Wa.card:ℝ) + (castΔ J R q r β κ'-f₂)*(Da.card:ℝ)+ Q + plumeCost B P W t + trend*b₂^2*t^2):=by
 let A:=grid_break r Da; let F':= accRoom T F A Wa m
 have hi:F'⊆accRoom T univ A Wa m:= filter_subset_filter _ (subset_univ _)
 have hh:=rayCapital (R:=R) (W:=W) (t:=t) (b:=b₂) (Q:=Q) (K':=qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩) B P L D I g d j wH uH Wa Da H' -- inspect order
 refine (dayBudget B P L D I g0 u a h1 h2 Wa Da hh.1 g l hi V).trans (hh.2.trans (Real.exp_monotone ?_))
 let D':= sunkV J q β κ'; let X:=(r.count.val:ℝ)
 have h:(A.card:ℝ) ≤ Da.card*(21:ℝ)^4:=by exact_mod_cast grid_pays r Da
 have ht:A.card*(X^4)*D' ≤ Da.card* ((21:ℝ)^4)*(X^4)*D':=by gcongr; · exact no_trouble d -- tune
 let f:= rimTax (∅:Support c) r (hallBill m)
 rw [show (wallTax (grid_break r Da) Wa r (hallBill m))=f + A.card*(r.count.val)^4 + Wa.card*(2* hallBill m+1)^4 from rfl]
 simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] -- keeps casts in reaches?
 unfold cutRate reachΔ castΔ billA; push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]; unfold D' sunkV X at *; unfold f at *; norm_num only [Nat.cast_ofNat,Nat.cast_one]; simp only [rimTax,Nat.cast_mul]; linarith only [ht]

end YM.Gleam
end
