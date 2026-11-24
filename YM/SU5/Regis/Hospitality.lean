import YM.SU5.Regis.Archive
import YM.SU5.Regis.Curators
/-! # Safe tile payment for inserted scale aperture, matching the gauge share. -/
set_option autoImplicit false
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule
open Gleam Matrix Next.SectorChange Next.SectorChange.Gaussian
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {n c:Side}{r: Ratio c n}{G:Gauge}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β ε : ℝ}{T:Support c}{D:ChartRatio G}{Z:PathData G}{I J:Type*}

lemma cool_home (t:Odd r.count.val)(u:m ≤ r.count.val/2) : (univ.filter (fun i=> ¬ Safe r T m i)).card ≤ Fintype.card (Site c)* largerBill r.count.val m + T.card * r.count.val^4:=by
 let H: Support n:= univ.filter (fun i=> ¬ Safe r T m i); let X:= r.count.val; let f:=X/2; let l:= f-m
 let C: Finset Cover:=Lattice.box f \ Lattice.box l; let P:=(univ:Support c) ×ˢ C; let Q:= T ×ˢ (univ:Support r.count)
 let y(i: Site c × Cover): Site n:= r.assemble (i.1,wrap r.count i.2)
 have hs:H ⊆ P.image y∪ Q.image r.assemble:=by
    intro x h; obtain ⟨⟨a,b⟩,rfl⟩:= r.assemble_bijective.2 x; let v:=Lattice.lift b; by_cases e:a ∈ T
    · exact mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨e, mem_univ b⟩))
    have h': v ∉ Lattice.box l:= by intro v'; apply (mem_filter.mp h).2; unfold Safe; simp only [Ratio.assemble_parent,not_false_eq_true,e,true_and]; exact sec_solutions rfl u rfl t _ v'
    exact mem_union_left _ (mem_image.mpr ⟨(a,v), mem_product.mpr ⟨mem_univ a,mem_sdiff.mpr ⟨r.half_box t _,h'⟩⟩, congrArg r.assemble (Prod.ext rfl (wrap_lift _))⟩)
 have he:Lattice.box l ⊆ Lattice.box f:=by
    intro i h; obtain ⟨h,p⟩:= box_test.mp h; have hl:l ≤ f:= Nat.sub_le ..; refine box_test.mpr ⟨fun j=>?_,fun j=>?_⟩; all_goals first | (specialize h j; omega) | (specialize p j; omega)
 refine (card_le_card hs).trans ((card_union_le ..).trans ((add_le_add card_image_le card_image_le).trans_eq ?_))
 simp only [P,Q,C,card_product,card_univ,card_sdiff_of_subset he, Corona.box_size,site_card]; have hf:f+f+1=X:=by obtain ⟨k,h⟩:=t; unfold f X; omega
 unfold largerBill; rw [hf,show r.count.val/2-m=l from rfl,show l+l=l*2 from (by omega)]
namespace Etch
variable [Fintype I](A:Etch G I)(B:Z.Bounds q η C S)(P:Attached H Z)(L:Floor H q n δ w)(O:Bid.Sworn H n G) (R:Rules G)
abbrev payroll : ℕ:= ∑ i:I, ∑ s:Signed,(skewSlot G (A.slot i) s).length
lemma payroll_paid (i:I)(s:Signed) : (skewSlot G (A.slot i) s).length ≤ A.payroll:= sum_to_me i s (fun i s=> (skewSlot G (A.slot i) s).length)
where sum_to_me (i:I)(s:Signed)(f:I→ Signed → ℕ): f i s≤ ∑ i,∑ s,f i s:= (single_le_sum (f:=f i) (fun _ _=> Nat.zero_le _) (mem_univ s)).trans (single_le_sum (f:=fun i=> ∑ s,f i s) (fun _ _=>Nat.zero_le _) (mem_univ i))
variable (a y:ℝ)
abbrev priceS (ρ:ℝ)(v:ℝ):ℝ:= A.favor* |ρ| * slotError R A.payroll v
lemma priceS_pos :0≤ A.priceS R y v:=by unfold priceS slotError faceCutError; have h:= G.colorScale_pos; have g:=R.positive; positivity
private lemma slot_err(r:ℕ) (z:ℝ): 0 ≤ slotError R r z:=by unfold slotError faceCutError; have h:= G.colorScale_pos; have l:=R.positive; positivity
lemma inside_award(h:A.payroll ≤ m)(s:Signed){o:Site n}(g:Safe r T (hallBill m) o){V Y:Dir G n}{U:Config G n}(l:TrustLogs (V+Y) U r T v)(K:0 ≤ v)(d:v ≤ R.c)(f:0<β): |A.palette y s o U - A.chalk q (y*coupling β) s o (starCost B P r T m Y β V)| ≤ A.priceS R y v:=by
 rw [pin, chalk]; let D(i:I):=skewSlot G (A.slot i) s; let L(i:I):= slotFace (D i) o; let E(i:I):=skewSig G (A.slot i) s
 let x(i:I):= y • E i • (D i).atSite U o; let Y'(i:I):=(y*coupling β) • E i • river q (L i) (starCost B P r T m Y β V); let a:= A.priceS R y v
 have he: ‖x-Y'‖ ≤ |y| * slotError R A.payroll v:=by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg y) (slot_err R A.payroll v))).mpr (fun i=>?_)
    have ht:= A.payroll_paid i s; have hp:insideB r T m (L i):=g.shift (by apply le_trans (Nat.add_le_add_right (((Work.E04.slot_separation (D i) o).trans ht).trans h) (Sequest m)); unfold hallBill Sequest; omega)
    have hY: Y' i= y • E i • faceCurl (L i) (V+Y):=by
       unfold Y' starCost; rw [map_smul,river_here _ B P _ V Y hp]; rw [mul_smul,smul_comm (coupling β) (E i), smul_inv_smul₀ (coupling_pos f).ne']
    rw [Pi.sub_apply,hY,show x i= y • E i • (D i).atSite U o from rfl,←smul_sub,←smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,show |E i|=1 from skewSq ..,one_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg y); exact grantSlot l K d _ (g.shift (y:=o) (by simp [hallBill,Sequest]; omega)) ht
 rw [←Real.norm_eq_abs]; exact ((A.steady.norm_sub_le x Y').trans (mul_le_mul_of_nonneg_left he A.favor.prop)).trans_eq (mul_assoc ..).symm
variable [Fintype J](t:J→Signed) (o:J→Site n)(p':Injective o) {F:ChartRatio G}
include p' in
lemma stipend (h:A.payroll ≤ m)(l: Odd r.count.val)(u:hallBill m ≤ r.count.val/2)(hS:0 ≤ v)(e:v ≤ R.c)(d:0<β) : SceneLease B P p r m β v (|a| * A.priceS R y v*Fintype.card J+ (|a| *A.arc)*(trap r m T)) T a (A.gallery y t o) (A.layoutC q (y*coupling β) t o):=by
 intro U V Y _ _ S'; let X:= univ.filter fun i:J=> ¬ Safe r T (hallBill m) (o i); let Z:= starCost B P r T m Y β V; let k:= |a| *A.arc*2; have hp(i): A.palette y (t i) (o i) U ≥ -A.arc:=(abs_le.mp (A.panel_bound y _ _)).1
 let F:= fun i:J=>a*A.palette y (t i) (o i) U-a*A.chalk q (y*coupling β) (t i) (o i) Z; let c₁:= |a| * A.priceS R y v; have he:0≤ c₁:=mul_nonneg (abs_nonneg _) (A.priceS_pos R y); have hK:0≤A.arc:= A.arc_non
 have hX(i:J): F i ≤ c₁ + if i∈ X then k else 0:=by
    refine le_trans (le_abs_self _) ?_; unfold F; rw [←mul_sub,abs_mul]; split_ifs with h
    · apply le_trans _ (le_add_of_nonneg_left he); apply le_trans (mul_le_mul_of_nonneg_left (le_trans (abs_sub ..) (add_le_add (A.panel_bound ..) (A.chalk_bound ..))) (abs_nonneg _)); unfold k; apply le_of_eq; ring -- abs_sub name
    have hx: Safe r T (hallBill m) (o i):=by simpa [X] using h
    rw [add_zero]; exact mul_le_mul_of_nonneg_left (A.inside_award B P R y ‹_› (t i) hx S' hS e d ) (abs_nonneg _)
 have hx: (∑ i:J,F i) ≤ (∑ i:J,(c₁+(if i∈ X then k else 0))):= sum_le_sum (fun i _=>hX i)
 rw [sum_add_distrib] at hx; have hu:X.card ≤ (Fintype.card (Site c)* largerBill r.count.val (hallBill m) + T.card * r.count.val^4):= (cool_home l u).trans' ((card_le_card (s:=X.image o) ?_).trans' (card_image_of_injective X p').symm.le)
 · apply (sub_le_iff_le_add').1; unfold gallery layoutC; rw [Finset.mul_sum,Finset.mul_sum,← sum_sub_distrib]; refine hx.trans (?_); let μ:ℝ:= (Fintype.card (Site c):ℝ)* largerBill r.count.val (hallBill m)+ T.card*(r.count.val:ℝ)^4
   rw [← sum_filter]; simp -- replace by `simp [...]`
   have hv:(X.card:ℝ) ≤ μ:=by unfold μ; refine (Nat.cast_le.mpr hu).trans_eq (?_); push_cast; ring
   change _≤ c₁* (Fintype.card J:ℝ)+ |a| * A.arc*(4*μ); unfold k; nlinarith only [mul_le_mul_of_nonneg_left hv (mul_nonneg (abs_nonneg a) hK),mul_nonneg (mul_nonneg (abs_nonneg a) hK) (Nat.cast_nonneg (α:=ℝ) X.card)]
 intro z ht; obtain ⟨i,p,rfl⟩:= mem_image.mp ht; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2⟩

-- payout matching schedule with actual cloud factor. x = observer ℶ. conductor ℑ choices paid separately.
open Gleam.clocks

lemma railB {x:ℝ} (t:x/2 ≤ β)(w: β ≤ 2*x)(p:0<x) : let a:=Real.sqrt x * coupling β; 1/2≤ a ∧ a ≤2:=by -- remove x implicit
 intro a
 let X:= Real.sqrt x; let Y:= Real.sqrt β; have h:0 < X:=Real.sqrt_pos.mpr p; have hy:0 < Y:=Real.sqrt_pos.mpr ((half_pos p).trans_le t)
 have he:= Real.sq_sqrt (x:=x) p.le; have hh:=Real.sq_sqrt (x:=β) ((half_pos p).trans_le t).le; change X^2=x at he; change Y^2=β at hh
 rw [show a=X/Y from div_eq_mul_inv ..|>.symm]; refine ⟨(le_div_iff₀ hy).2 ?_, (div_le_iff₀ hy).2 ?_⟩<;> nlinarith
lemma wanes (L:Side) : Tendsto (fun x:ℝ=> A.priceS R (Real.sqrt x) (pace L x)) atTop (𝓝 0):=by
 let z(x:ℝ):= Real.sqrt x * (pace L x)^2; have hg:Tendsto z atTop (𝓝 0):=by
    have he:Tendsto (fun x:ℝ=> pace L x) atTop (𝓝 0):=by simpa using heel L 0
    have ht:= (he.mul (pillar L 0)).sqrt; rw [mul_zero,Real.sqrt_zero] at ht; apply ht.congr'; filter_upwards [eventually_ge_atTop 0] with x hx
    change Real.sqrt (pace L _* _)=z x; rw [pow_zero,one_mul, show pace L x* (x* pace L x ^3)= x*((pace L x)^2)^2 from (by ring), Real.sqrt_mul hx, Real.sqrt_sq (sq_nonneg _)]
 have hp:= (hg.const_mul ((A.favor:ℝ)*(G.colorScale*16+R.C*4+ 8* G.colorScale* A.payroll))); rw [mul_zero] at hp
 apply hp.congr; intro x; unfold z priceS slotError faceCutError; rw [abs_of_nonneg (Real.sqrt_nonneg _)]; ring
/-- quadratic remaining after perturb. -/
abbrev aftermath (A:Etch G I)(q:Clip) :ℝ:= trend*(A.lensLimit q 2)^2
lemma aftermath_pos : 0 ≤ A.aftermath q:=by unfold aftermath trend; positivity
universe u
omit [Fintype J] o p' t
-- n B P are dependent; unify ∀ n
include R in
lemma cloakB (q: Clip)(f:LocalRatio D)(ℓ:Side)(v:ℝ)(p:0<η)(g:0≤C)(S:ℝ)(h:0 ≤ v)(κ e':ℝ)(r':0<e') : ∀ᶠ x:ℝ in atTop, ∀ u:Side, Odd u.val → moder (height x) u.val ℓ → ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ (n c:Side)(Q:Ratio c n),2*(Q.count.val+1)<n.val → Q.count=u → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B:Z.Bounds q η C S){μ y:ℝ}(L:Floor H q n μ y),0<μ → Bid.Sworn H n G → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ v) → ∀ {J:Type u}[Fintype J] (o:J→Site n)(t:J→Signed),Injective o→ (∫ U:Config G n,angBill Z q p' β κ U * Real.exp (a* A.gallery (Real.sqrt x) t o U) ∂prior G n) ≤ Real.exp (Roof D β n H + 2*e'*Fintype.card (Site n)+ Fintype.card J* (a*A.muρ q B P (Real.sqrt x * coupling β) n+ A.aftermath q*a^2)):=by
 let W:= |a| * A.arc
 have he:= (wanes A R ℓ).const_mul |a|; rw [mul_zero] at he
 filter_upwards [eventually_gt_atTop 0,Work.E08.eventual_radiusB A.payroll, (heel ℓ 0).eventually (ge_mem_nhds R.radius), taller 0 ℓ 1 (by simp) (by simp), jewel q R f v ℓ p g S h κ e' r' W (mul_nonneg (abs_nonneg _) A.arc_non), he.eventually (ge_mem_nhds r')] with x hp hu ht hL hT hb u ho hv p' β hβ e n c Q k pQ H Z P B μ y L hμ O s J f o t hy -- D.elab G
 apply forEach B (A.museum ..) _ a; intro l; simp_rw [A.entourage]
 let m:=height x; let ρ:=Real.sqrt x; let Y:= ρ * coupling β; let TQ(j:J):=l*t j; let w(j:J):=affine l 0 (o j); let bJ:= (Fintype.card J:ℝ); let u':= A.layoutC q Y TQ w; have pW:Injective w:= fun a b g=> hy (l.act_injective (add_right_cancel g))
 have hx:Odd Q.count.val:= pQ.symm ▸ ho
 have hs: v ≤ v:= le_rfl; -- n
 let D':= A.lensLimit q Y*Real.sqrt bJ; let F:=|a| * A.priceS R ρ (pace ℓ x)* bJ
 have hX:= hT u ho hv p' β hβ e n c Q k pQ P B L hμ s a F (bJ*A.arc) D' (A.museum w ρ TQ) (A.encase w ρ TQ) u' (A.planSmooth q w Y TQ) (fun i=> A.planBound q w Y TQ i) (A.rays_steady q w pW Y TQ) (fun z=> A.stipend B P R a ρ TQ w pW hu hx (hL _ hx (pQ.symm ▸ hv)).1 (surge ℓ x hp.le) (show _ from ?_) ((half_pos hp).trans_le hβ.1))
 swap; · simpa using ht -- show given pace 
 refine hX.trans (Real.exp_monotone ?_)
 rw [show plumeCost B P u' a=_ from A.gallery_fee q w Y TQ B P L O a]; have hy: bJ ≤ Fintype.card (Site n):= Nat.cast_le (α:=ℝ).2 (Fintype.card_le_of_injective o hy)
 have hf:F ≤ e'*(Fintype.card (Site n):ℝ):= mul_le_mul hb hy (by unfold bJ; positivity) r'.le
 obtain ⟨g,h⟩:= railB hβ.1 hβ.2 hp
 have hf': A.lensLimit q Y ≤ A.lensLimit q 2:=by unfold lensLimit rays; have p:0 ≤ Y:= le_trans (by norm_num) g; rw [abs_of_nonneg p]; rw [abs_of_nonneg (by norm_num: (0:ℝ)≤2)]; gcongr
 have he: D'^2 ≤ bJ*(A.lensLimit q 2)^2:=by unfold D'; rw [mul_pow,Real.sq_sqrt (by unfold bJ; positivity),mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (A.lensLimit_non ..) hf' _) (by unfold bJ; positivity)
 change Roof _ _ _ _+_+F+bJ*(a*A.muρ q B P Y n)+_ ≤ _; unfold aftermath; change _ ≤ Roof D β n H + 2*e'* _+ bJ*(a*A.muρ q B P Y n + (trend*(A.lensLimit q 2)^2)*a^2)
 nlinarith only [hf, mul_le_mul_of_nonneg_left he (show 0 ≤ a^2*trend from mul_nonneg (sq_nonneg _) (by unfold trend; positivity))]
-- choose ε>0 scale factor. combines earned costs
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.Etch.stipend

#print axioms YM.Regis.Head.Etch.cloakB
