import YM.SU5.Thin.Glacier.Layer
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)
variable {N:Finset (Cell n)} {τ κA ψ:ℝ}
variable (I:ArcChill J R q p r.count.val m β κ ξ v Λ τ κA ψ) (g0:2*(r.count.val+1)<n.val)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
variable (Q':0 ≤ z') -- z' reserve coefficient per unit universal wall
variable {κ' : ℝ}
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)

abbrev fritTrap (r:Ratio c n)(m:ℕ)(A:Support c)(N:Finset (Cell n)):ℝ:=4*((Fintype.card (Site c):ℝ)*largerBill r.count.val (hallBill m)+ A.card*(r.count.val:ℝ)^4 + N.card*(speckCount (hallBill m):ℝ))
private lemma core_purchase (h:(cellM T F H).PosDef)(g:0<β)(D:LocalRatio J) : let M:= iceWing R J q p β v η C S ξ Λ ψ m A.card F H N; 0<M ∧ Real.log M=(F.card:ℝ) * (Real.log (spare J β)+Λ) - (Fintype.card G.ColorIndex:ℝ)/2*Real.log (cellM T F H).det + taxΔ R q n p β v η C S m - ξ*A.card- ψ*N.card :=by
 intro M; let F':= J.scale ^ F.card * chartCost (prism T F H G)⁻¹ (coupling β)
 let V:= R.C; let E:= taxΔ R q n p β v η C S m - ξ*A.card- ψ*N.card; let T:= Real.exp (E+Λ*F.card); have hz: 0<F':= mul_pos (pow_pos D.scale _) (chartCost_pos _ (PosDef.kronecker h PosDef.one).inv (coupling_pos g))
 have hT: M=F'*T:=by unfold F' M iceWing iceFeet T; rw [mul_pow,Real.exp_add, mul_comm Λ _,Real.exp_nat_mul]; unfold E; ring
 rw [hT]; refine ⟨mul_pos hz (Real.exp_pos _),?_⟩; rw [Real.log_mul hz.ne' (Real.exp_pos _).ne',show Real.log T= _ from Real.log_exp _, (show Real.log F'= _ from prism_spec J D g h)]; unfold E; ring
variable (g:0<β)(d:0≤ κ')(l:0≤ C)
include B P L D I d g j wH uH Q'
lemma highCore {K':(H.metric.acts n).PosDef} (A:Support c)(H':Buttress T F){d₀:ℝ}(hS:4*descendCost J β κ' z'*speckCount (hallBill m)+d₀ ≤ ψ) (pH:4*descendCost J β κ' z'*(r.count.val:ℝ)^4 ≤ ξ): let W0:= hallFrozen T F A m N; let M:=iceWing R J q p β v η C S ξ Λ ψ m A.card W0 H N; (cellM T W0 H).PosDef ∧ M*Real.exp (jewelFee B P W t b₂ T W0 (Q+z'*fritTrap r m A N)) ≤ Real.exp (Roof J β n H+rentRoom r R q m p β v η C S Λ (descendCost J β κ' z') + Q + plumeCost B P W t + trend*b₂^2*t^2 - d₀*N.card):=by -- u implicit causing omit param L; make explicit implicit synthesizable?
 intro W0 M
 let d':= descendCost J β κ' z'; let K:=leasePart (H.metric.acts n); let X:= Real.log (spare J β); let Y:ℝ:=(Fintype.card G.ColorIndex:ℝ)/2
 let i:= Real.log K; let Hf:=cellM T W0 H; have hh:W0⊆ F:=(hall_icy ..).trans inner_part; let Hc:= rentRoom r R q m p β v η C S Λ d'; let D':ℕ:=F.card-W0.card; let f:ℝ:=F.card; let c':ℝ:=W0.card; let a:ℝ:=Fintype.card (Site c); let B₀:ℝ:=Fintype.card (Site n)
 have hm : 1 ≤ Fintype.card (Site n):=Fintype.card_pos; have ht :f=3*(B₀-1):=by unfold f; rw [H'.count,Nat.cast_mul,Nat.cast_sub hm]; push_cast; rfl
 obtain ⟨gH,hZ⟩:= looks H K' uH H' hh; refine ⟨gH,?_⟩; obtain ⟨h1,h2⟩:=core_purchase (ψ:=ψ) (N:=N) (A:=A) (R:=R) (H:=H) (p:=p) (v:=v) (η:=η) (C:=C) (S:=S) (ξ:=ξ) (Λ:=Λ) (m:=m) gH g D; rw [← Real.log_le_log_iff (mul_pos h1 (Real.exp_pos _)) (Real.exp_pos _),Real.log_mul h1.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp];
 let x:= largerBill r.count.val (hallBill m); let y:ℝ:= (r.count.val:ℝ)^4
 have hp : (D':ℝ)=f-c':= Nat.cast_sub (card_le_card hh)
 have hxcard :(D':ℝ) ≤ 4*(a*x+A.card*y+(N.card:ℝ)*speckCount (hallBill m)):= by
    apply le_trans (Nat.cast_le (α:=ℝ).mpr (hall_trim (F:=F) (m:=m) (A:=A) (W:=N) j wH)); unfold a x y surfaceBill; change (_:ℝ) ≤ _; push_cast; exact le_of_eq (by rfl)
 have hy:0 ≤ f-c':=hp ▸ Nat.cast_nonneg _
 have h':= mul_le_mul_of_nonneg_left hxcard (show 0≤d' from by unfold d' descendCost; have t' := pays_hall (J:=J) (β:=β) d; positivity)
 -- split I green. t δ etc. absorb
 have hh':Λ*(B₀) ≥ 0:= mul_nonneg I.green (by unfold B₀; positivity)
 have hu:c'*Λ ≤ f*Λ:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) I.green
 have hq:= mul_le_mul_of_nonneg_left pH (Nat.cast_nonneg (α:=ℝ) A.card)
 have hk:= mul_le_mul_of_nonneg_right (neg_le_abs X) hy
 change Real.log M=_ at h2; rw [h2]; unfold Roof rentRoom
 change i ≤ Real.log (Hf.det) + κ'*D' at hZ; rw [hp] at h' hZ
 change c'*(X+Λ) - Y*_ + _ -_ -_ + jewelFee B P W t b₂ T W0 (Q+z'*fritTrap r m A N) ≤ 3*(B₀-1)*X-Y*i +( _ + 4*Λ*B₀ +4*d'*a*x)+_+_+_ -_
 have hz:0≤Y:=by unfold Y; positivity
 change d'*(f-c') ≤ d'*(4*(a*x+A.card*y+(N.card:ℝ)*speckCount (hallBill m))) at h'; change _ * (4*d'*y) ≤ _ at hq; change i≤ Real.log (cellM T W0 H).det+ _ at hZ; rw [←ht]; unfold jewelFee; let Z0:= fritTrap r m A N
 have uT: (cellM T F H).PosDef:= (H'.precision K').1
 have hF:=at_rank B P L uT; have hw:=at_rank B P L gH; rw [← garden_equiv B P L H',hF,hw]; push_cast
 have hx : |Real.log (spare J β)|=d'-Y*κ'-Y-z':=by unfold d' Y descendCost margin; ring
 have hv : f-c' ≤ Z0:= by rwa [hp] at hxcard
 change d'*(f-c') ≤ d'*Z0 at h'
 change 0 ≤ z' at Q'
 let C' := Fintype.card G.ColorIndex
 rw [show |X| = _ from hx] at hk
 have hv': (d'-z')*(f-c') ≤ (d'-z')*Z0:=mul_le_mul_of_nonneg_left hv (by unfold d' descendCost; have hz:=pays_hall (J:=J) (β:=β) d; have he:0 ≤ (Fintype.card G.ColorIndex:ℝ):=Nat.cast_nonneg _; linarith only [hz,he])
 change (d'-z')*(f-c') ≤ (d'-z')*(4*(a*x + A.card*y + (N.card:ℝ)*speckCount (hallBill m))) at hv'
 change z' ≥ 0 at Q'; change (_ :ℝ) + (Q + z'*(4*(a*x + A.card*y + (N.card:ℝ)*speckCount (hallBill m)))+_ +_ + ((f*(C':ℝ)-c'*(C':ℝ))/2)) ≤ _  -- adjust assoc
 have hw : (C':ℝ) = 2*Y:= by unfold Y C'; ring
 have hS0: (N.card:ℝ)* (4*d'*speckCount (hallBill m)+d₀) ≤ _:= mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
 linarith only [hk,hh',ht,hu,hq,mul_le_mul_of_nonneg_left hZ hz,hv', I.green,mul_le_mul_of_nonneg_right ht.le I.green,mul_le_mul_of_nonneg_right hw.ge (show 0≤f-c' from hy),mul_le_mul_of_nonneg_right hw.le hy,hS0] -- fritTrap not unfolded so z'*fritTrap as atom

end YM.Gleam