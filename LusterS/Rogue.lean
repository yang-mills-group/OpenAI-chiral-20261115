import LusterS.Gem
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
variable (hD:LocalRatio J) (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ) (g0:2*(r.count.val+1)<n.val) (d:0≤t)(g:0<β)(l:0≤C)
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i,(Precision.K (H.metric.acts n)) i i≤t)(he:0<δ)

lemma power_layout {A:Type}[Fintype A](v:ℝ): (∑ i: Finset A, Real.exp (-v*(i.card:ℝ)))≤Real.exp (Real.exp (-v)*Fintype.card A):=by
 let x:= Real.exp (-v)
 have he:(∑ i:Finset A, Real.exp (-v*(i.card:ℝ)))=(x+1)^Fintype.card A:=by
    have h(i:Finset A):Real.exp (-v*(i.card:ℝ))=∏ _∈i,x:=by rw [mul_comm,Real.exp_nat_mul,prod_const]
    simp_rw [h]
    have ht:= (Fintype.prod_add (fun _:A=>x) (fun _=>1))
    simpa using ht.symm
 rw [he,mul_comm (Real.exp (-v)),Real.exp_nat_mul]; exact pow_le_pow_left₀ (by unfold x; positivity) (Real.add_one_le_exp _) _

include B P L hD I g0 d g l j wH uH he
lemma harvest_dual (pH: 4*margin J β t*(r.count.val:ℝ)^4 ≤ ξ) (hd:4*margin J β t*(lusterBill (hallBill m):ℝ) ≤ χ):
   (∫ U:Config G n,goods Z q p β κ fuel v' U ∂prior G n) ≤ Real.exp ((Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t) + Real.log 2*(Fintype.card (Site c):ℝ)) + Real.exp (-ν)*(Fintype.card (Cell n):ℝ)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T
 have h':=goods_invariant (n:=n) (p:=p) (β:=β) (κ:=κ) (fuel:=fuel) (v':=v') B
 rw [T.pack _ ((env_grow B).integrable _) (fun k _=> h' k)]
 let Q:= Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t); let F'(A:Support c)(D:Finset (Cell n)):= trip Z q p A D T β κ fuel v'
 have hp(A:Support c)(D:Finset (Cell n)) : (∫ x,F' A D x ∂T.order G)≤ Real.exp (Q-ν*D.card):= by
    let e:= bloom T F A D m; obtain ⟨g,k⟩:= splitBill (u:=qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩) L hD I d g j wH uH A D h pH hd; refine (sharp_insideBudget B P L hD I g0 A D g ‹0<β› l (bloom_mono (subset_univ F))).trans k
 rw [show (fun x:T.Slice G=> goods Z q p β κ fuel v' (T.drape x))=(fun x=>∑ i: Support c,∑ b:Finset (Cell n),F' i b x) from ?_]
 swap
 · funext x
   symm; rw [sum_eq_single (broken r v' (T.drape x))]; · simp only [F',trip,true_and]; simp
   · intro a _ h; refine sum_eq_zero fun b _=> ?_; unfold F' trip; rw [if_neg (fun p=> h p.1.symm)]
   simp
 rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ fun j _=>(through_t B _ _).integrable _
 let M:ℝ:=Fintype.card (Site c); let D:ℝ:=Fintype.card (Cell n)
 have hx (A:Support c): (∫ x:T.Slice G,(∑ b:Finset (Cell n),F' A b x) ∂T.order G) ≤ Real.exp Q * Real.exp (Real.exp (-ν)*D):=by
    rw [integral_finsetSum _ fun b _=> (through_t B _ _).integrable _]; refine (sum_le_sum (fun i _=>hp A i)).trans ?_; simp_rw [sub_eq_add_neg,Real.exp_add,←neg_mul]; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (power_layout _) (Real.exp_pos _).le
 refine (sum_le_sum (fun i _=> hx i)).trans_eq (?_); change (∑ _: Support c, Real.exp Q*_)=Real.exp ((Q+Real.log 2*M)+_)
 rw [sum_const,card_univ,nsmul_eq_mul,Real.exp_add ((Q+_:ℝ)) _,Real.exp_add Q (Real.log 2*M), mul_comm (Real.log 2)]; unfold Support D M; rw [Real.exp_nat_mul, Real.exp_log (by norm_num), Fintype.card_finset]; push_cast; ring
abbrev regenerate (Z:PathData G)(q:Clip)(p:BudgetPoint)(β κ fuel v':ℝ)(U:Config G n):= Real.exp (-(Z.inChannels q p β U)+(κ*(misdemean p.threshold U).card+fuel*(misdemean v' U).card))
omit P L hD I g0 d g l j wH uH he in
lemma env_reg : Envelope (regenerate Z q p β κ fuel v' (n:=n)):= ((PathData.channels_env B p β).neg.add ((conduct ..).add (conduct ..))).exp
omit B P L hD I g0 d g l j wH uH he in
private lemma on_wind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))
omit P L hD I g0 d g l j wH uH he in
lemma fullCheck : (∫ x:Config G n, regenerate Z q p β κ fuel v' x∂prior G n) ≤ ∫ x,goods Z q p β κ fuel v' x∂prior G n := by
 let M:ℝ:=Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 let w:= M⁻¹; let S:=regenerate Z q p β κ fuel v' (n:=n); let F:=goods Z q p β κ fuel v' (n:=n); let X:=prior G n; let Φ(s:Signed)(x:Config G n):=F (pull s 0 x)
 have hw:∑ _:Signed,w=1:= by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 let E:=env_grow (n:=n) (p:=p) (β:=β) (κ:=κ) (fuel:=fuel) (v':=v') B; let G'(x: Config G n):= ∑ i: Signed,w*Φ i x
 have he(i:Signed): Integrable (fun x=>w*Φ i x) X:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable (E.integrable X)).const_mul w
 have hf:Integrable G' X:= integrable_finsetSum _ (fun i _=> he i)
 refine le_trans (integral_mono ((env_reg B).integrable X) hf ?_) (le_of_eq ?_)
 · intro x; let f(s:Signed):= Z.principal q p β (pull s 0 x); let g:= κ*(misdemean p.threshold x).card+fuel*(misdemean v' x).card; let e(s:Signed):= -f s+g; have ht(i:Signed): Φ i x=Real.exp (e i):=by unfold Φ F goods e; rw [on_wind,on_wind]
   unfold G'; simp_rw [ht]; let t:= (convexOn_exp.map_sum_le (w:=fun _ : Signed=>w) (fun i _=> inv_nonneg.mpr hM.le) hw (fun s _ => Set.mem_univ (e s)))
   change Real.exp _ ≤ ∑ i,w • _; apply t.trans'; refine Eq.le (congrArg Real.exp ?_); unfold e; simp only [smul_eq_mul,mul_add,sum_add_distrib, mul_neg,sum_neg_distrib, ← mul_sum, sum_const, card_univ,nsmul_eq_mul]; change -(w*∑ s,f s)+ g= -(w*∑ s,f s)+ w * (M*g); rw [inv_mul_cancel_left₀ hM.ne'] -- order
 unfold G'; rw [integral_finsetSum _ (fun i _=> he i)] -- signature lemma
 have h(i:Signed):(∫ x:Config G n, w*Φ i x∂X)=w*∫ x,F x∂X:=by rw [integral_const_mul]; refine congrArg (w * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂X from (by have ht:= integral_map (μ:=prior G n) (f:=F) t.measurable.aemeasurable (show AEStronglyMeasurable F _ from E.meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht)) -- replace
 simp_rw [h]; rw [← sum_mul,hw,one_mul]

lemma rich_bill (pH: 4*margin J β t*(r.count.val:ℝ)^4 ≤ ξ)(hd:4*margin J β t*(lusterBill (hallBill m):ℝ) ≤ χ): (∫ U:Config G n, regenerate Z q p β κ fuel v' U ∂prior G n) ≤ Real.exp ((Roof J β n H+rentRoom r R q m p β v η C S Λ (margin J β t) + Real.log 2*(Fintype.card (Site c):ℝ)) + Real.exp (-ν)*(Fintype.card (Cell n):ℝ)):= (fullCheck B).trans (harvest_dual B P L hD I g0 d g l j wH uH he pH hd)
end YM.Gleam.Luster
