import YM.SU5.Gleam.Inlets
/-! # Upper pressure competition for gauge share. -/
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
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)
variable (I:Archive J R q p r.count.val m β κ ξ v Λ) (g0:2*(r.count.val+1)<n.val) (d:0≤ t) (g:0<β) (l:0≤C)
def Roof (J:ChartRatio G) (β:ℝ)(n:Side)(H:Bed):= 3*((Fintype.card (Site n):ℝ)-1)*Real.log (spare J β) -(Fintype.card G.ColorIndex:ℝ)/2*Real.log (leasePart (H.metric.acts n))
def margin (J: ChartRatio G) (β t:ℝ):= |Real.log (spare J β)| + (Fintype.card G.ColorIndex:ℝ)/2*t
def hallBill (m:ℕ):ℕ:= Sequest m+ Sequest m
def rentRoom (r:Ratio c n)(R:Rules G)(q:Clip)(m:ℕ)(p:BudgetPoint)(β v η C S Λ d:ℝ):= taxΔ R q n p β v η C S m + 4*Λ*(Fintype.card (Site n):ℝ) +4*d*(Fintype.card (Site c):ℝ) * largerBill r.count.val (hallBill m)
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ t)(he:0 < δ)
lemma pays_hall (d:0 ≤ t):0 ≤ margin J β t:=by unfold margin; positivity
private lemma wing_purchase (h:(cellM T F H).PosDef)(g:0<β)(D:LocalRatio J) : let M:= wingFee n R J q p β v η C S ξ Λ m A.card F H; 0<M ∧ Real.log M=(F.card:ℝ) * (Real.log (spare J β)+Λ) - (Fintype.card G.ColorIndex:ℝ)/2*Real.log (cellM T F H).det + taxΔ R q n p β v η C S m - ξ*A.card :=by
 intro M; let F':= J.scale ^ F.card * chartCost (prism T F H G)⁻¹ (coupling β)
 let V:= R.C; let E:= taxΔ R q n p β v η C S m - ξ*A.card; let T:= Real.exp (E+Λ*F.card); have hz: 0<F':= mul_pos (pow_pos D.scale _) (chartCost_pos _ (PosDef.kronecker h PosDef.one).inv (coupling_pos g))
 have hT: M=F'*T:=by unfold F' M wingFee sealFeet T; rw [mul_pow,Real.exp_add, mul_comm Λ _,Real.exp_nat_mul]; unfold E; ring
 rw [hT]; refine ⟨mul_pos hz (Real.exp_pos _),?_⟩; rw [Real.log_mul hz.ne' (Real.exp_pos _).ne',show Real.log T= _ from Real.log_exp _, (show Real.log F'= _ from prism_spec J D g h)]; unfold E; ring
include B P L D I g0 d g l j wH uH he
omit B P g0 l he in
private lemma highBill {u:(H.metric.acts n).PosDef} (A:Support c)(H':Buttress T F)(pH:4*margin J β t*(r.count.val:ℝ)^4 ≤ ξ): let W:= room T F A m; let M:=wingFee n R J q p β v η C S ξ Λ m A.card W H; (cellM T W H).PosDef ∧ M ≤ Real.exp (Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t)):=by -- u implicit causing omit param L; make explicit implicit synthesizable?
 intro W M
 let d':= margin J β t; let K:=leasePart (H.metric.acts n); let X:= Real.log (spare J β); let Y:ℝ:=(Fintype.card G.ColorIndex:ℝ)/2
 let i:= Real.log K; let Hf:=cellM T W H; have hh:W⊆ F:=inner_part; let Hc:= rentRoom r R q m p β v η C S Λ d'; let D':ℕ:=F.card-W.card; let f:ℝ:=F.card; let c':ℝ:=W.card; let a:ℝ:=Fintype.card (Site c); let B:ℝ:=Fintype.card (Site n)
 have hm : 1 ≤ Fintype.card (Site n):=Fintype.card_pos; have ht :f=3*(B-1):=by unfold f; rw [H'.count,Nat.cast_mul,Nat.cast_sub hm]; push_cast; rfl
 obtain ⟨gH,hZ⟩:= looks H u uH H' hh; refine ⟨gH,?_⟩; obtain ⟨h1,h2⟩:=wing_purchase (A:=A) (R:=R) (H:=H) (p:=p) (v:=v) (η:=η) (C:=C) (S:=S) (ξ:=ξ) (Λ:=Λ) (m:=m) gH g D; rw [← Real.log_le_log_iff h1 (Real.exp_pos _),Real.log_exp]; change Real.log M ≤ Roof J β n H + Hc -- maybe parse
 let x:= largerBill r.count.val (hallBill m); let y:ℝ:= (r.count.val:ℝ)^4
 have hp : (D':ℝ)=f-c':= Nat.cast_sub (card_le_card hh)
 have hx :(D':ℝ) ≤ 4*(a*x+A.card*y):= by
    exact (Nat.cast_le (α:=ℝ).mpr (inner_charge (a:=F) (d:=hallBill m) (A:=A) j wH)).trans (le_of_eq (by unfold a x y; push_cast; rfl))
 have hy:0 ≤ f-c':=hp ▸ Nat.cast_nonneg _
 have h':= mul_le_mul_of_nonneg_left hx (pays_hall (J:=J) (β:=β) d)
 -- split I green. t δ etc. absorb
 have hh':Λ*(B) ≥ 0:= mul_nonneg I.green (by unfold B; positivity)
 have hu:c'*Λ ≤ f*Λ:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) I.green
 have hq:= mul_le_mul_of_nonneg_left pH (Nat.cast_nonneg (α:=ℝ) A.card)
 have hk:= mul_le_mul_of_nonneg_right (neg_le_abs X) hy
 change Real.log M=_ at h2; rw [h2]; unfold Hc Roof rentRoom
 change i ≤ Real.log (Hf.det) + t*D' at hZ; rw [hp] at h' hZ
 change c'*(X+Λ) - Y*_ + _ -_ ≤ 3*(B-1)*X-Y*i +( _ + 4*Λ*B +4*d'*a*x)
 have hz:0≤Y:=by unfold Y; positivity
 change d'*(f-c') ≤ d'*(4*(a*x+A.card*y)) at h'; change _ * (4*d'*y) ≤ _ at hq; change i≤ Real.log (cellM T W H).det+ _ at hZ; rw [←ht]; rw [show |X|=d'-Y*t by unfold d' Y margin X; ring] at hk
 linarith only [hk,h',ht,hu,I.green,mul_le_mul_of_nonneg_left ht.le I.green,hh',mul_le_mul_of_nonneg_left hZ hz,hq]
lemma harvest_dirt (pH: 4*margin J β t*(r.count.val:ℝ)^4 ≤ ξ) :
   (∫ U:Config G n,richG Z q p β κ U∂prior G n) ≤ Real.exp (Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t) + Real.log 2*(Fintype.card (Site c):ℝ)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T; have h':= richG_inv (β:=β) (κ:=κ) (p:=p) (n:=n) B; rw [T.pack _ ((income_g B).integrable _) (fun k _=> h' k)]; let Q:= Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t); let F'(A:Support c):= play Z q p A T β κ
 have hp(A:Support c) : (∫ x,F' A x ∂T.order G)≤ Real.exp Q := by
    let e:= room T F A m; obtain ⟨g,k⟩:= highBill (u:=qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩) L D I d g j wH uH A h pH; refine (insideBudget B P L D I g0 A g ‹0<β› l (filter_subset_filter _ (subset_univ F))).trans k
 rw [show (fun x:T.Slice G=> richG Z q p β κ (T.drape x))=(fun x=>∑ i: Support c,F' i x) from ?_] -- rw inside integral? binder
 swap; · funext x; simp [F', play]
 rw [integral_finsetSum]; swap; · exact fun i _=> (env_play B _).integrable _
 refine (sum_le_sum (fun i _=> hp i)).trans_eq (?_); change (∑ _: Support c, Real.exp Q)=Real.exp (Q+_)
 simp only [sum_const,card_univ,nsmul_eq_mul,Real.exp_add]; rw [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num)]; unfold Support; simp only [Fintype.card_finset]; push_cast; ring
abbrev angBill (Z:PathData G)(q:Clip)(p:BudgetPoint)(β κ:ℝ)(U:Config G n):ℝ:= Real.exp (-(Z.inChannels q p β U)+κ*(misdemean p.threshold U).card)
omit P L D I g0 d g l j wH uH he in
lemma env_ang : Envelope (angBill Z q p β κ (n:=n)):= ((PathData.channels_env B p β).neg.add (conduct ..)).exp
omit B P L D I g0 d g l j wH uH he in
private lemma on_wind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))
omit P L D I g0 d g l j wH uH he in
lemma allChannels : (∫ x:Config G n, angBill Z q p β κ x∂prior G n) ≤ ∫ x,richG Z q p β κ x∂prior G n := by
 let M:ℝ:=Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 let w:= M⁻¹; let S:=angBill Z q p β κ (n:=n); let F:=richG Z q p β κ (n:=n); let X:=prior G n; let Φ(s:Signed)(x:Config G n):=F (pull s 0 x)
 have hw:∑ _:Signed,w=1:= by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 let E:=income_g (n:=n) (p:=p) (β:=β) (κ:=κ) B; let G'(x: Config G n):= ∑ i: Signed,w*Φ i x
 have he(i:Signed): Integrable (fun x=>w*Φ i x) X:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable (E.integrable X)).const_mul w
 have hf:Integrable G' X:= integrable_finsetSum _ (fun i _=> he i)
 refine le_trans (integral_mono ((env_ang B).integrable X) hf ?_) (le_of_eq ?_)
 · intro x; let f(s:Signed):= Z.principal q p β (pull s 0 x); let g:= κ*(misdemean p.threshold x).card; let e(s:Signed):= -f s+g; have ht(i:Signed): Φ i x=Real.exp (e i):=by unfold Φ F richG e; rw [on_wind]
   unfold G'; simp_rw [ht]; let t:= (convexOn_exp.map_sum_le (w:=fun _ : Signed=>w) (fun i _=> inv_nonneg.mpr hM.le) hw (fun s _ => Set.mem_univ (e s)))
   change Real.exp _ ≤ ∑ i,w • _; apply t.trans'; refine Eq.le (congrArg Real.exp ?_); unfold e; simp only [smul_eq_mul,mul_add,sum_add_distrib, mul_neg,sum_neg_distrib, ← mul_sum, sum_const, card_univ,nsmul_eq_mul]; change -(w*∑ s,f s)+ g= -(w*∑ s,f s)+ w * (M*g); rw [inv_mul_cancel_left₀ hM.ne'] -- order
 unfold G'; rw [integral_finsetSum _ (fun i _=> he i)] -- signature lemma
 have h(i:Signed):(∫ x:Config G n, w*Φ i x∂X)=w*∫ x,F x∂X:=by rw [integral_const_mul]; refine congrArg (w * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂X from (by have ht:= integral_map (μ:=prior G n) (f:=F) t.measurable.aemeasurable (show AEStronglyMeasurable F _ from E.meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht)) -- replace
 simp_rw [h]; rw [← sum_mul,hw,one_mul]
lemma wide_ship (pH: 4*margin J β t*(r.count.val:ℝ)^4 ≤ ξ) :
   (∫ U:Config G n,angBill Z q p β κ U∂prior G n) ≤ Real.exp (Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t) + Real.log 2*(Fintype.card (Site c):ℝ)):= (allChannels B).trans (harvest_dirt B P L D I g0 d g l j wH uH he pH)
end YM.Gleam
#print axioms YM.Gleam.wide_ship
