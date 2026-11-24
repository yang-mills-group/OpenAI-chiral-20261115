import Risa.Scarp
import Risa.Forte
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
variable {χ fuel b0 Q0 b₁ b₀ y plumeU:ℝ}{Φ:Config G n→ℝ}{Q:Support c→Finset (Cell n)→Altar G n→ℝ}(e:RG.Envelope Φ)(gΦ:GaugeInvariant Φ)
  (e1:∀A D,ContDiff ℝ 1 (Q A D))(h1:∀A D x,|Q A D x|≤ b₁)(h2:∀A D x,‖fderiv ℝ (Q A D) x‖≤ b₀)(W0:∀A D, GradeLease B P p r m β v (Q0+y*snags r m A D) v' A D Φ (Q A D))
  (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ)(eD:χ+ν ≤ β*(q.direct*p.threshold^2/2))(g0:2*(r.count.val+1)<n.val)(d:0≤t)(g:0<β)(l:0≤C)(j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i,(Precision.K (H.metric.acts n)) i i ≤ t)(he:0<δ)
include B D' P L I eD g0 d g l j wH uH he e gΦ e1 h1 h2 W0
lemma festival (pH:4*descendCost J β t y*(r.count.val:ℝ)^4 ≤ ξ)(hd:4*descendCost J β t y*(lusterBill (hallBill m):ℝ) ≤ χ)(y0:0 ≤ y)(hu:∀ A D, plumeCost B P (Q A D) 1≤plumeU):
 (∫ U:Config G n,goods Z q p β κ fuel v' U * Real.exp (Φ U) ∂prior G n) ≤ Real.exp ((Roof J β n H+rentRoom r R q m p β v η C S Λ (descendCost J β t y) + Q0 + trend*b₀^2*1^2 + plumeU + Real.log 2*(Fintype.card (Site c):ℝ)) + Real.exp (-ν)*(Fintype.card (Cell n):ℝ)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T
 have h':=goods_invariant (n:=n) (p:=p) (β:=β) (κ:=κ) (fuel:=fuel) (v':=v') B

 let S0(u:Config G n):=goods Z q p β κ fuel v' u * Real.exp (Φ u)
 change (∫ u,S0 u∂prior G n) ≤ _
 have HE:Envelope S0:=(env_grow B).mul e.exp
 rw [T.pack _ (HE.integrable _) (fun k _ U=> by unfold S0; rw [h' k U, gΦ k U])] -- gauge invariant rich k? h' k U V? signature? GaugeInvariant F expects g,U two args, ∀i? from code h' k. inspect
 let Q₁:= Roof J β n H+rentRoom r R q m p β v η C S Λ (descendCost J β t y) + Q0 + trend*b₀^2*1^2 + plumeU; let F'(A:Support c)(D:Finset (Cell n)):= source₂ Z q p A D T β κ fuel v' Φ
 have hhA(A:Support c)(D:Finset (Cell n)) : (∫ x,F' A D x ∂T.order G)≤ Real.exp (Q₁-ν*D.card):= by
    let E:= bloom T F A D m; let r0:=Q0+y*snags r m A D
    have h0w:= venal (u:=qpos he L.symmetric.1 ⟨fun a=> (L.uniform.1 a).1⟩) B P L D' I d g j wH uH y 1 Q0 b₀ (Q A D) A D h pH hd y0 -- order check
    let X:=source_inside B P L D' I eD g0 e e1 h1 h2 W0 A D h0w.1 g l (bloom_mono (subset_univ F))
    refine X.trans (h0w.2.trans (Real.exp_le_exp.mpr ?_))
    unfold Q₁; linarith only [hu A D]
 rw [show (fun x:T.Slice G=> S0 (T.drape x))=(fun x=>∑ i: Support c,∑ b:Finset (Cell n),F' i b x) from ?_]
 swap
 · funext x
   symm; rw [sum_eq_single (broken r v' (T.drape x))]; · simp only [F',source₂]; rw [←sum_mul]; simp [trip₂,S0]
   · intro a _ h; refine sum_eq_zero fun b _=> ?_; unfold F' source₂ trip₂; rw [if_neg (fun p=> h p.1.symm),zero_mul]
   simp
 rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ fun j _=>(through_source₂ B e _ _).integrable _
 let M:ℝ:=Fintype.card (Site c); let D:ℝ:=Fintype.card (Cell n)
 have hx (A:Support c): (∫ x:T.Slice G,(∑ b:Finset (Cell n),F' A b x) ∂T.order G) ≤ Real.exp Q₁ * Real.exp (Real.exp (-ν)*D):=by
    rw [integral_finsetSum _ fun b _=> (through_source₂ B e _ _).integrable _]; refine (sum_le_sum (fun i _=>hhA A i)).trans ?_; simp_rw [sub_eq_add_neg,Real.exp_add,←neg_mul]; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (power_layout _) (Real.exp_pos _).le
 refine (sum_le_sum (fun i _=> hx i)).trans_eq (?_); change (∑ _: Support c, Real.exp Q₁*_)=Real.exp ((Q₁+Real.log 2*M)+_)
 rw [sum_const,card_univ,nsmul_eq_mul,Real.exp_add ((Q₁+_:ℝ)) _,Real.exp_add Q₁ (Real.log 2*M), mul_comm (Real.log 2)]; unfold Support D M; rw [Real.exp_nat_mul, Real.exp_log (by norm_num), Fintype.card_finset]; push_cast; ring

omit B P L D' I eD g0 d g l j wH uH he e gΦ e1 h1 h2 W0
private lemma on_wind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))
variable {φ:Config G n→ℝ}(u: Envelope φ)
include B u in
lemma forWind {fuel v':ℝ} (ξ:ℝ)(t:ℝ)(hh:∀ d: Signed,(∫ x:Config G n, goods Z q p β κ fuel v' x *Real.exp (t*φ (pull d 0 x)) ∂prior G n) ≤ ξ) : (∫ x:Config G n, regenerate Z q p β κ fuel v' x * Real.exp (t*φ x) ∂prior G n) ≤ ξ := by
 let M:ℝ:=Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 let w:= M⁻¹; let S:=regenerate Z q p β κ fuel v' (n:=n); let F (s: Signed) (x:Config G n):= goods Z q p β κ fuel v' x * Real.exp (t*φ (pull s⁻¹ 0 x)); let X:=prior G n; let Φ(s:Signed)(x:Config G n ):=F s (pull s 0 x)
 have hw:∑ _:Signed,w=1:= by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 have E(i:Signed) : Envelope (F i):=(env_grow B).mul ((fun p:Envelope (fun x:Config G n=> φ (pull i⁻¹ 0 x) )=>expEnv p t) ⟨u.meas.comp (by apply (prior_pull _ _).measurable), u.cost.choose,fun _=> u.cost.choose_spec _⟩); let G'(x: Config G n):= ∑ i: Signed,w*Φ i x
 have he(i:Signed): Integrable (fun x=>w*Φ i x) X:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable ((E i).integrable X)).const_mul w
 have hf:Integrable G' X:= integrable_finsetSum _ (fun i _=> he i)
 refine le_trans (integral_mono (show Integrable _ _ from ((env_reg (n:=n) (p:=p) (κ:=κ) (β:=β) (fuel:=fuel) (v':=v') B).mul (expEnv u t)).integrable X) hf ?_) ?_
 · intro x; let f(s:Signed):= Z.principal q p β (pull s 0 x); let g:= κ*(misdemean p.threshold x).card+fuel*(misdemean v' x).card; let e(s:Signed):= -f s+g + t*φ x; have ht(i:Signed): Φ i x=Real.exp (e i ):=by unfold Φ F goods e; rw [on_wind,on_wind,pull_pull]; simp [affine,Real.exp_add]; unfold f g; rw [Real.exp_add]
   unfold G'; simp_rw [ht]; let tt:= (convexOn_exp.map_sum_le (w:=fun _ : Signed=>w) (fun i _=> inv_nonneg.mpr hM.le) hw (fun s _ => Set.mem_univ (e s)))
   rw [←Real.exp_add]
   change Real.exp _ ≤ ∑ i,w • _; apply tt.trans'; refine Eq.le (congrArg Real.exp ?_); unfold e; simp only [smul_eq_mul,mul_add,sum_add_distrib, mul_neg,sum_neg_distrib, ← mul_sum, sum_const, card_univ,nsmul_eq_mul]; change -(w*∑ s,f s)+ g + t*φ x= -(w*∑ s,f s)+ w * (M*g) + w * (t*(M*φ x)); rw [mul_left_comm t M, inv_mul_cancel_left₀ hM.ne', inv_mul_cancel_left₀ hM.ne'] -- order
 unfold G'; rw [integral_finsetSum _ (fun i _=> he i)] -- signature lemma
 have h(i:Signed):(∫ x:Config G n, w*Φ i x∂X)=w*∫ x,F i x∂X:=by rw [integral_const_mul]; refine congrArg (w * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂X from (by have ht:= integral_map (μ:=prior G n) (f:=F i) t.measurable.aemeasurable (show AEStronglyMeasurable (F i) _ from (E i).meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht))
 simp_rw [h]; refine (Finset.sum_le_sum (g:=fun _=> w*ξ) (fun i _=>?_)).trans_eq ?_; · exact mul_le_mul_of_nonneg_left (hh i⁻¹) (by unfold w; positivity)
 rw [← Finset.sum_mul,hw,one_mul]

#print axioms forWind
#print axioms festival
#check @festival
end Risa
end YM.Gleam.Luster
