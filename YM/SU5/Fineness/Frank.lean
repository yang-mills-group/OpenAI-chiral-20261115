import YM.SU5.Fineness.Storey
import YM.CF.Souk.Bit
import YM.CF.Newt.Stage
import YM.CF.Corne.Vest
/-!
# Sharp orientation cost under precision (uniform logarithmic). Lean
 prickly about AnalyticBridge norms! compare Newt.paintO norm in precisely its ℓ∞
 coordinates on both sides; eigenvalue/gap subproof done in genuine l2 (qpay).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Matrix Finset CF CF.Newt Pressure
open scoped Matrix Matrix.Norms.Frobenius BigOperators
variable {I:Type}[Fintype I][DecidableEq I]{a ρ u:ℝ}{A B T:Sheet I}
lemma frank_row (p:Bᵀ=B)(y:I→ℝ)(h:∀ i,∑ j, |B i j|≤a): qpay B y≤a* dotProduct y y:=by
 let f (i j:I):ℝ:= |B i j| *y i^2; have ht(i j:I): y i*(B i j*y j) ≤ (f i j+f j i)/2:=by
    have hp: B j i=B i j:=congr_fun (congr_fun p i) j
    unfold f; rw [hp]; by_cases h:0≤B i j
    · rw [abs_of_nonneg h]; nlinarith only [mul_nonneg h (sq_nonneg (y i-y j))]
    rw [abs_of_neg (lt_of_not_ge h)]; nlinarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (sq_nonneg (y i+y j))]
 have he: qpay B y ≤ ∑ i,∑ j,(f i j+f j i)/2:=by
    simp only [qpay,dotProduct, Matrix.mulVec, mul_sum]; exact sum_le_sum fun i _=>sum_le_sum fun j _=> ht i j
 have hp (i:I) : ∑ j,f i j≤a*(y i*y i):=by
    unfold f; rw [← Finset.sum_mul,sq]; exact mul_le_mul_of_nonneg_right (h i) (mul_self_nonneg _)
 simp_rw [←Finset.sum_div,Finset.sum_add_distrib] at he; nth_rw 2 [sum_comm] at he -- which?
 refine le_trans (show qpay B y≤ ∑ i,∑ j,f i j by linarith [show _ from he]) ?_; unfold dotProduct; rw [mul_sum]; exact sum_le_sum fun i _=> hp i
lemma spread_one (p:0<u)(q:FreeResolvent.Gap A u)(g:Aᵀ=A)(ht:B.PosDef)(l:‖paintO (B-A)‖≤ρ) : Real.log B.det-Real.log A.det ≤ Fintype.card I * (ρ/u):=by
 have ha:A.PosDef:= qpos p g q; let v:=ρ/u+1; have hL:= (norm_nonneg _).trans l; have hv:v>0 := add_pos_of_nonneg_of_pos (by positivity) zero_lt_one
 refine le_trans ?_ (show _ from mul_le_mul_of_nonneg_left (show Real.log v ≤ ρ/u by simpa only [v,add_sub_cancel_right] using Real.log_le_sub_one_of_pos hv ) (show 0 ≤ (Fintype.card I:ℝ) by positivity))
 have hg: B.det ≤ (v • A).det:=by
    refine (harvested ht (by rw [Matrix.transpose_smul,g]) fun x=>?_).2; rw [rates]; unfold v; rw [add_mul,one_mul]; let C:= B-A; have he:= frank_row (B:=C) (by unfold C; rw [Matrix.transpose_sub,((q_iff _).1 ht).1,g]) x (fun i=>(Souk.row_S C i).trans l)
    calc
      _ = qpay C x+qpay A x:= by rw [←priced_plus,sub_add_cancel]
      _ ≤ (ρ/u)*(u*dotProduct x x)+qpay A x :=add_le_add (he.trans_eq (by field_simp)) le_rfl
      _ ≤ _:= add_le_add (mul_le_mul_of_nonneg_left (q.lower _) (by positivity)) le_rfl
 have he:= Real.log_le_log ht.det_pos hg; rw [det_smul,Real.log_mul (by positivity) ha.det_pos.ne', Real.log_pow] at he; linarith only [he]
lemma priceSpread(p:0<u)(q:FreeResolvent.Gap A u)(q':FreeResolvent.Gap B u)(g:Aᵀ=A)(ht:Bᵀ=B)(l:‖paintO A-paintO B‖≤ρ) : |Real.log B.det-Real.log A.det| ≤ Fintype.card I * (ρ/u):=by
 rw [abs_le]; refine ⟨?_,spread_one p q g (qpos p ht q') (by rw [map_sub,norm_sub_rev]; exact l)⟩; have he:= spread_one (ρ:=ρ) p q' ht (qpos p g q) (by rw [map_sub]; exact l); linarith only [he]
open Filter Lattice RG Precision Tree Forge FreeResolvent PhysicalNext.JointLoad.Heir
open Next Next.Fluctuations Next.SectorChange
open AnalyticBridge.LocalGaussianLaws
open scoped Classical Topology Kronecker
local notation "G"=>SU.group
variable {K:Teller SU.group}{R:Patch}{m n:Side}(S:StepData m n)(M:Monk SU.group S){x η δ:ℝ}
local notation "g'"=> Affine.headGap G R K.bind K.top.clip
local notation "β'" => Fintype.card (Site n)
local notation "Zm"=> Fintype.card SU.group.ColorIndex
variable (ε:ℝ) (U: Tube SU.group S)(H:Bed)
local notation "H'"=> Neige.baseX U x (Corne.kist M).key (Corne.kist M).park (Corne.kist M).k 1
local notation "G₀"=> treeMatrix G S M.park H.metric
local notation "C0"=> K.top.paths
local notation "W0"=> K.top.width
lemma g_sym (h:(H.metric.acts n)ᵀ=H.metric.acts n): (treeMatrix SU.group S M.park H.metric)ᵀ = G₀:=by rw [tree_eq, ← kroneckerMap_transpose, transpose_one,board_symm S M.park _ h]
lemma g_prec {x:ℝ}(t:Newt.Cert R K S U x)(p:Floor H K.top.clip n η δ)(q:Attached H U.up)(e:Bid.Sworn H n G): FreeResolvent.Gap G₀ (Affine.headGap SU.group R K.bind K.top.clip):=by
 obtain ⟨a,b,h,u⟩:= t.funds.1.feeds
 have ht:= Affine.identifies S M.park M.k t.pace.1 h q p.roots e; rw [← ht,← t.got,←t.funds.1.knobs]; apply Affine.directGap; exact t.pace
lemma porch (p:Floor H K.top.clip n η δ)(q:Attached H U.up)(e:Bid.Sworn H n G)(t: Newt.Cert R K S U x) :
 |Corne.arcD U x M+(1/2:ℝ)*Real.log (treeMatrix G S M.park H.metric).det| ≤ β' * (2* Zm * (( Real.exp (-(W0/4)*Stores.till x)*ozPay R K.bind W0 C0 G)/ Affine.headGap G R K.bind K.top.clip)):=by
 let u: ( (Corne.kist M).key)=bareStores S:=rfl
 let ht:( (Corne.kist M).park)=M.park:=rfl
 obtain ⟨a,b,h,v⟩:= t.funds.1.feeds
 let M':=Corne.kist M
 let W:=H'; let w':Fineness.Sheet (FreeResolvent.Active G M.park):= W.submatrix (pageX M.park x) (pageX M.park x)
 let Gx:=G₀; let ρ := Real.exp (-(W0/4)*Stores.till x)*ozPay R K.bind W0 C0 G ; let f:=U.high
 let qK:= t.funds.1.high; have hB: (U.up).Bounds U.high W0 C0 a:=qK.symm ▸ h
 have hx:=g_prec S M U H t p q e; have gu : 0<g':= Affine.headGap_pos ..
 have he:= Affine.identifies S M.park M.k t.pace.1 hB q (qK.symm ▸ p.roots) e;
 obtain ⟨Y,W'⟩:= recount M.park x M.k hB t.pace t.funds; have hp:= octo M.park x M.k hB t.pace t.funds K.top.paths_pos.le
 rw [W',show FreeResolvent.Affine.all = (fun _=>true) from rfl,he,t.got,t.funds.1.knobs] at hp -- motive S kernel
 have hv:w'ᵀ=w':=by change (W.submatrix _ _)ᵀ=_; rw [transpose_submatrix,show Wᵀ=W from Char.gramS ..]
 have hC:Gap w' g':=by
    rw [show w' =_ from (show w'=Affine.primary S M.park M.k U.high U.up (Affine.shorter (Stores.till x)) 0 from Y), ← t.got, ← t.funds.1.knobs, ←t.funds.1.high]; exact Affine.directGap S M.park M.k _ _ _ t.pace
 have hh:= priceSpread (A:= G₀) (B:=w') gu hx hC (g_sym S M H p.symmetric.1) hv (show ‖paintO Gx - paintO w'‖ ≤ρ from hp)
 have hn: (Fintype.card M.park.Free:ℝ)≤4*β':= by
    have ht:Fintype.card M.park.Free ≤ 4* β':=by
       rw [show 4*β'= Fintype.card (Edge (Site n)) from (by rw [Fintype.card_prod]; rw [show Fintype.card Axis=4 by rfl]; ring)]
       exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    exact_mod_cast ht
 let k':= ρ/g'; have h0:0 ≤ρ:= le_trans (norm_nonneg (paintO Gx-paintO w')) hp
 have he k : 0 ≤ ((k:ℕ):ℝ):= Nat.cast_nonneg _
 have hz:0 ≤ (Zm:ℝ)*k':= mul_nonneg (by positivity) (div_nonneg h0 gu.le)
 change |-(1/2:ℝ)*Real.log W.det+1/2 * Real.log Gx.det| ≤ _
 change |Real.log w'.det- Real.log Gx.det|≤ (Fintype.card (M.park.Free×SU.group.ColorIndex):ℝ)*k' at hh
 rw [abs_le,Fintype.card_prod,Nat.cast_mul,show w'.det=W.det from Matrix.det_submatrix_equiv_self (pageX M.park x) W] at hh -- delta w'? rw won't
 rw [abs_le]; change _≤_ ∧ _ ≤ (β':ℝ)*(2* Zm * k'); -- tune
 change -((β':ℝ)*(2*Zm*k')) ≤ _∧ _
 constructor <;> nlinarith only [hh.1,hh.2, mul_le_mul_of_nonneg_right hn hz]
lemma porch_rate (K:Teller SU.group)(R:Patch)(p:0<ε) : ∀ᶠ x in atTop,∀ {m n:Side}(S:StepData m n)(M:Monk SU.group S)(U:Tube SU.group S)(H:Bed){η δ:ℝ},Floor H K.top.clip n η δ→Attached H U.up→ Bid.Sworn H n SU.group→ Newt.Cert R K S U x→ |Corne.arcD U x M+(1/2:ℝ)*Real.log (treeMatrix G S M.park H.metric).det| ≤ ε* Fintype.card (Site n):=by
 let v:= K.top.width/4; have hp:0<v:= by unfold v; have h:=K.top.width_pos; positivity
 let k:= Affine.headGap SU.group R K.bind K.top.clip; have he:0<k:= Affine.headGap_pos ..
 let c:ℝ:=2*(Fintype.card SU.group.ColorIndex:ℝ); have hc:0≤c:=by unfold c; positivity
 have hx:Tendsto temp atTop (𝓝 0):= by simpa using YM.Work.E09.radiusB_temp 0
 have hq:Tendsto (fun x => c*(temp x/k)) atTop (𝓝 0):= by simpa using (hx.div_const k).const_mul c
 filter_upwards [Newt.smallF (n:=1) hp (ozPay R K.bind K.top.width K.top.paths SU.group), hq.eventually (ge_mem_nhds p)] with x ht hp; intro m n S M U H η δ p q e t
 rw [pow_one] at ht; rw [mul_comm ε]; exact (porch S M U H p q e t).trans (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht he.le) hc).trans hp) (by positivity))
end YM.Fineness
#print axioms YM.Fineness.porch_rate
