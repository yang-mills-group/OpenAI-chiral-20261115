import YM.SU5.FiniteGaugeData.LapisQ.EPOCH
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 620000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Tulipe
open Vulcan Willow Nosh Cordon
namespace IndigoLX
variable {ι:Type}[Fintype ι][Nonempty ι] (X:ι→ Cover)
variable {n:Side} {σ K C ρ ε:ℝ} {u:Stage}{P:Bed}
variable {T:Matrix (Body 2 n) (Body 2 n) ℝ}
local notation "ΦA"=> (Fintype.card ι:ℝ)
local notation "Su"=> Site n
variable (t y: Site n)(g:Gate u P ρ C σ K n T)
noncomputable abbrev Herald (J:Matrix (Body 2 n) (Body 2 n) ℝ)(x:Site n):ℝ:= (Fintype.card ι:ℝ)⁻¹* ∑ i:ι,songV J (x-wrap n (X i))
noncomputable abbrev sonar (t:Site n):ℂ:= ((Fintype.card ι:ℝ)⁻¹:ℝ) • ∑ i:ι, cell t (wrap n (X i))
noncomputable abbrev hue (J:Matrix (Body 2 n) (Body 2 n) ℝ)(x:Site n): ℂ:= Cordon.lord (fun t => ↑(Herald X J t)) x
lemma shiftsY (T:Matrix (Body 2 n) (Body 2 n) ℝ) (p:Site n): lord (fun x:Site n=> (songV T (x-p):ℂ)) t= cell t p * facet T t f0 f0:=by
 unfold lord; change _ = _* ∑ x:Site n, _; rw [Finset.mul_sum]; symm; apply Fintype.sum_equiv (Equiv.addRight p) _ _; intro i; rw [show (Equiv.addRight p) i=i+p from rfl]; simp only [add_sub_cancel_right,cell_add]; unfold songV; ring
lemma colorate (T:Matrix (Body 2 n) (Body 2 n) ℝ) : hue X T t= sonar X t * facet T t f0 f0:=by
 unfold hue sonar Herald; let f(i:ι)(x:Site n):ℂ:=↑(songV T (x - wrap n (X i))); let A₁:ℂ:= (( (Fintype.card ι:ℝ)⁻¹:ℝ):ℂ) -- illcast
 have hx: lord (fun x:Site n=> ((ΦA⁻¹*∑ i:ι,songV T (x-wrap n (X i)) :ℝ):ℂ)) t=A₁*∑ i:ι,lord (f i) t:=by unfold lord; simp_rw [Complex.ofReal_mul,Complex.ofReal_sum,mul_assoc,Finset.sum_mul,←Finset.mul_sum]; refine congrArg (A₁*·) ?_; exact sum_comm
 rw [hx]; have he(i:ι): Cordon.lord (f i) t= cell t (wrap n (X i))*facet T t f0 f0:=shiftsY t T _; rw [sum_congr rfl (fun i _ => he i), ← Finset.sum_mul, ← mul_assoc]; rfl
include X
lemma avia : 0 < (Fintype.card ι:ℝ):=by positivity
lemma sonB : ‖sonar X t‖ ≤ 1:=by unfold sonar; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (avia X)).le]; exact ((mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_pos.mpr (avia X)).le)).trans_eq (by simp only [cell_pay,sum_const,card_univ,nsmul_eq_mul,mul_one]; exact inv_mul_cancel₀ (avia X).ne')
omit X
lemma voice (i:Axis): ‖cell t (step i)-1‖≤ ‖harp t‖:= (show ‖_‖≤ _ from (by rw [←harpC]; exact norm_le_pi_norm _ _)) -- tune
lemma voc (d:Step): ‖cell t (d.vec)-1‖ ≤ ‖harp t‖:=by
 rcases d with ⟨i,v|v⟩; · exact voice t i
 change ‖cell t (-step i)-1‖≤_; rw [cell_inverse, ←cell_bar]; change ‖star (cell t (step i))-1‖≤_; rw [← show (star (1:ℂ))=1 from star_one ℂ, ←star_sub,norm_star]; exact voice t i
lemma starStep (d:Step): ‖cell t (y+d.vec)-cell t y‖≤ ‖harp t‖:=by
 rw [cell_add]; nth_rw 2 [← mul_one (cell t y)]
 rw [←mul_sub,norm_mul,cell_pay,one_mul]; exact voc t d
lemma starTrial (U:Walk): ‖cell t (stop y U)-cell t y‖≤ U.length *‖harp t‖:=by
 induction U generalizing y with
 | nil=>simp [stop]
 | cons i l ih=> let Q:= cell t (y+i.vec); apply (norm_sub_le_norm_sub_add_norm_sub (cell t (stop (y+i.vec) l)) Q _).trans; exact (add_le_add (ih _) (starStep ..)).trans_eq (by rw [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul])
noncomputable abbrev choiceLL(x:Cover):= Lattice.route 0 x 1
lemma bear (x:Cover): ‖cell t (wrap _ x)-1‖ ≤ (choiceLL x).length*‖harp t‖:=by
 let A':= choiceLL x; have hx: stop 0 A'=x:=route_end ..; rw [← cell_origin t, ← show stop (0:Site n) A'= wrap n x from (by rw [← map_zero (wrap n),←wrap_stop_cover,hx])]; exact starTrial ..
noncomputable abbrev CapP (X:ι→ Cover):ℝ:= (Fintype.card ι:ℝ)⁻¹ * ∑ i:ι, ((choiceLL (X i)).length:ℝ)
include X
lemma sonΔ : ‖sonar X t-1‖≤ CapP X* ‖harp t‖:=by
 have hx: ( (Fintype.card ι:ℝ)⁻¹ • ∑ _:ι,(1:ℂ))=1:=by rw [sum_const,card_univ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (avia X).ne', one_smul] -- spelling
 rw [sonar,←hx,←smul_sub, ← Finset.sum_sub_distrib,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (avia X)).le]; unfold CapP; rw [mul_assoc, Finset.sum_mul]; apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (avia X)).le; exact (norm_sum_le ..).trans (sum_le_sum (fun i _=>bear t _))
include g in
lemma iconB : ‖hue X T t‖≤1/ρ:=by rw [colorate,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (sonB X t)).trans (frontier_entry g t _ _)
lemma needCap : 0 ≤ CapP X:= by unfold CapP; positivity
lemma songPP (σ ρ K:ℝ)(p:0<ε): ∃ x:ℝ,0<x∧∀ {n:Side}{t:Site n}{P:Bed}{u:Stage}{C:ℝ}{Y:Matrix (Body 2 n) (Body 2 n) ℝ},Gate u P ρ C σ K n Y → Exterior.q (mon t)≠0→‖Exterior.q (mon t)‖≤x→ ‖hue X Y t-camp (Exterior.q (mon t)) f0 f0‖ ≤ ε:=by
 let c:= CapP X; obtain ⟨x,u,f⟩:= promise σ ρ K (half_pos p); have hc:=needCap X; have h0:0<c+1:=add_pos_of_nonneg_of_pos hc zero_lt_one; let r:=min x (ε/2/(c+1)); refine ⟨r,lt_min u (div_pos (half_pos p) h0),?_⟩; intro n t P u C A' g hp hv; let H:=Exterior.q (mon t); let z:= camp H f0 f0; let U:= facet A' t f0 f0; let W:= sonar X t; have he:‖W-1‖ ≤ ε/2:= (sonΔ X t).trans ((mul_le_mul (le_add_of_nonneg_right zero_le_one) hv (norm_nonneg _) h0.le).trans (by rw [mul_comm]; exact (le_div_iff₀ h0).mp (min_le_right ..)))
 change ‖hue X A' t-z‖≤_; rw [colorate]; change ‖W*U-z‖ ≤_; rw [show W*U-z=W*(U-z)+(W-1)*z from (by ring)]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact (add_le_add ((mul_le_of_le_one_left (norm_nonneg _) (sonB X t)).trans (f g hp (hv.trans (min_le_left ..)) _ _)) ((mul_le_of_le_one_right (norm_nonneg _) (passport H hp _ _)).trans he)).trans_eq (add_halves ε) -- A notation conflict

variable {z:Phase4}
noncomputable abbrev bridgeX (X:ι→ Cover)(A:Matrix (Body 2 n) (Body 2 n) ℝ)(r:ℕ) (t:Site n):= lore t r (hue X A)
local notation "V"=> Phase4
lemma pillarP (σ ρ K:ℝ)(p:0<ε) :∃ x:ℝ,0<x∧∀ z:Phase4,z≠0→‖z‖<x→∃ δ:ℝ,0<δ ∧ ∀ᶠ r:ℕ in atTop,∀ {n:Side}{A:Matrix (Body 2 n) (Body 2 n) ℝ}{u:Stage}{P:Bed}{C:ℝ}{t:Site n}, Gate u P ρ C σ K n A → r+1<n.val→‖harp t-z‖≤δ →‖bridgeX X A r t-camp z f0 f0‖≤ε :=by
 let μ:= ε/4; have hm:0<μ:=by unfold μ; positivity
 obtain ⟨x,u,h⟩:= songPP X σ ρ K hm; refine ⟨x,u, fun z v w=>?_⟩
 let Q: Set V:= {y|‖y‖ < x ∧ y≠0∧ ‖camp y f0 f0-camp z f0 f0‖ < μ }
 have hQ : Q∈𝓝 z:=by
    have he: {y:Phase4|y≠0}∈𝓝 z:=compl_singleton_mem_nhds v
    filter_upwards [he,(continuous_norm.continuousAt (x:=z)).tendsto.eventually (gt_mem_nhds w), (cap_C z v f0 f0).tendsto.eventually (Metric.ball_mem_nhds _ hm)] with x t p p'; exact ⟨p,t,show _ from (by rwa [dist_eq_norm] at p')⟩
 obtain ⟨d,b,v0⟩:=Metric.mem_nhds_iff.mp hQ
 let δ:= d/4; have hd:0<δ:=by unfold δ; positivity
 let C':=(1/ρ+1)/(δ^2); have hb:Tendsto (fun r:ℕ=> C'*(8/(r+1:ℝ))) atTop (𝓝 0):=by -- simple denom tendsto
    have hp:Tendsto (fun r:ℕ=> (r:ℝ)+1) atTop atTop:= Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R:=ℝ)) tendsto_const_nhds -- name
    simpa using (tendsto_const_nhds.div_atTop hp |>.const_mul C') -- type infer
 refine ⟨δ,hd,?_⟩; filter_upwards [hb.eventually (ge_mem_nhds hm)] with r v_ n A u P C t g b0 ht -- shadow `b` from previous
 -- v0 subset function.V window; need η positive from Q. Ring.
 have hρ:0<ρ:=g.cost; have hv:0 ≤ C':=by unfold C'; positivity
 have he(y:Site n): ‖hue X A (t+y)-camp z f0 f0‖ ≤ μ*2+C' *sqLength (harp y):=by
    let u:=harp (t+y); by_cases he:‖harp y‖ ≤ δ
    · have hy:u∈Q:=by
         apply v0; rw [Metric.mem_ball,dist_eq_norm]; refine lt_of_le_of_lt ((norm_sub_le_norm_sub_add_norm_sub u (harp t) z).trans (add_le_add ((bendW t y).trans he) ht)) ?_; unfold δ; linarith only [b]
      refine (norm_sub_le_norm_sub_add_norm_sub (hue X A (t+y)) (camp u f0 f0) (camp z f0 f0)).trans (le_trans (add_le_add (h g hy.2.1 hy.1.le) hy.2.2.le) ?_); nlinarith only [mul_nonneg hv (sqLength_nonneg (harp y))]
    apply le_trans (norm_sub_le ..)
    have hz: ‖hue X A (t+y)‖≤1/ρ:= iconB X _ g -- v lost binder!
    have hh: δ^2 ≤ sqLength (harp y):= (pow_le_pow_left₀ hd.le ((lt_of_not_ge he).le) 2).trans (flareA _); -- fix
    have hw:1/ρ+1≤ C'*sqLength (harp y):=((div_mul_cancel₀ ((1:ℝ)/ρ+1) (pow_pos hd 2).ne').symm).le.trans (mul_le_mul_of_nonneg_left hh hv)
    linarith only [hm, passport z ‹_› f0 f0,hz,hw]
 apply le_trans (tender b0 _ (μ*2) C' _ t he); have hp:C'* (8/(r+1:ℝ)) ≤ μ:=v_; unfold μ at *; linarith only [hp,hm]

variable (m:ℕ→Side) (v:Tendsto (fun i=>(m i).val) atTop atTop)(ℓ:ℕ)
omit X in
private lemma fee_δ (z y x v d:ℂ)(h:‖z-x‖≤ ε/3)(p:‖y-v‖ ≤ ε/3) (t: ‖x-v-d‖ ≤ ε/3) : ‖z-y-d‖≤ ε:=by
 calc _= ‖((z-x)-(y-v))+(x-v-d)‖ := by congr 1; ring
      _ ≤ (ε/3+ε/3)+ε/3:= (norm_add_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add h p)) t)
      _ = _:=by ring
include v
lemma stalePP (σ ρ K:ℝ) : ∃ (s p q:Melody m),∀ᶠ r:ℕ in atTop,∀ᶠ i:ℕ in atTop, r+1<(m i).val ∧∀ {u:Stage}{P:Bed}{C:ℝ}{A:Matrix (Body 2 (m i)) (Body 2 (m i)) ℝ}, Gate u P ρ C σ K (m i) A → MtRequest (s i) ℓ (p i) (q i) (bridgeX X A r) :=by
 let e:= payable ℓ/3; have he: 0<e:=by have hx:= part_p ℓ; unfold e; positivity
 obtain ⟨x,u,h⟩:= pillarP X σ ρ K he; obtain ⟨t,L,hT⟩:= buildH ℓ x u he
 obtain ⟨s,p⟩:= aria m v (uniformM t) (by funext; simp [uniformM]); choose y hv using fun i:Axis=> aria m v (rung L i) (by funext t; by_cases he:t=i <;> simp [he,rung,pureW] -- tune eq
                                                                            )
 let P(a:Axis)(j:colorX ℓ):= fun i:ℕ=> y a i+ shiftU (s i) ℓ j
 have hx(a:Axis)(j:colorX ℓ):note m (P a j) (dyad ℓ j t L a):= nOrder m _ _ _ _ (hv a) (leadR m s (uniformM t) ℓ p j)
 let F(j:colorX ℓ)(a:Axis):= Exterior.q (dyad ℓ j t L a)
 have hX(a:Axis)(j:colorX ℓ)(z:F j a≠0)(v0:‖F j a‖<x) : ∀ᶠ r:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ {u:Stage}{P':Bed}{C:ℝ}{A:Matrix (Body 2 (m i)) (Body 2 (m i)) ℝ}, Gate u P' ρ C σ K (m i) A → ‖bridgeX X A r (P a j i)-camp (F j a) f0 f0‖ ≤ e:=by
    obtain ⟨δ,q,c⟩:= h (F j a) z v0; filter_upwards [c] with r f; filter_upwards [v.eventually_gt_atTop (r+1),(Metric.tendsto_nhds.mp (hx a j) δ q)] with i v h u P' C A g; exact f g v (le_of_lt (show ‖harp (P a j i)-F j a‖<δ from (by rwa [dist_eq_norm] at h)))
 refine ⟨s,y 0,y 2,?_⟩
 have he(j:colorX ℓ):= hT j; let P' := (Tendsto (fun x:ℕ=>x) atTop atTop)
 filter_upwards [(eventually_all.mpr (fun i=> hX 0 i (hT i).1 (hT i).2.2.1)),eventually_all.mpr (fun i=> hX 2 i (hT i).2.1 (hT i).2.2.2.1)] with r p h
 filter_upwards [v.eventually_gt_atTop (r+1),eventually_all.mpr p,eventually_all.mpr h] with i u p h; exact ⟨u,fun g j=> fee_δ _ _ _ _ _ (p j g) (h j g) (hT j).2.2.2.2⟩
-- to all periods. eventually on r uniform k.
omit v X
private abbrev Pplus (i:ℕ):Side:=⟨i+1,by omega⟩
private lemma leads : Tendsto (fun i=>(Pplus i).val) atTop atTop:=by
 refine tendsto_atTop.mpr (fun i=>(eventually_ge_atTop i).mono (fun z v=> le_trans v (Nat.le_succ _)))
include X in
lemma catchPX (σ ρ K:ℝ): ∀ᶠ r:ℕ in atTop,∃ N:ℕ,∀ n:Side,N≤n.val→ r+1<n.val ∧∃ s p q:Site n,∀ {u:Stage}{P:Bed}{C:ℝ}{A:Matrix (Body 2 n) (Body 2 n) ℝ},Gate u P ρ C σ K n A → MtRequest s ℓ p q (bridgeX X A r):=by
 obtain ⟨s,p,q,H⟩:= stalePP X Pplus leads ℓ σ ρ K; filter_upwards [H] with r y; obtain ⟨N,u⟩:= eventually_atTop.mp y; refine ⟨N+1,fun n v=>?_⟩; let i:= n.val-1; have w:N≤ i:= (by omega); let b:= Pplus i; have he: n=Pplus i:=Subtype.ext (by change n.val=i+1; omega); rw [he]; exact ⟨(u i w).1,s i,p i,q i,(u i w).2⟩ -- dep eq error rwp.C.
-- now real gauge coefficient.YA.UV statistic witness
omit m in
private lemma fareMX(r ℓ:ℕ):∃ c:ℝ,0<c∧tariffMX r ℓ c<1/2:=by
 -- use filter due denominator tiny.L.
 let f(x:ℝ):= tariffMX r ℓ x; have hh:f 0=0:=by simp [f,tariffMX]
 have hp:Tendsto f (𝓝[>] 0) (𝓝 0):=by simpa only [hh] using ((show Continuous f from (by unfold f tariffMX; fun_prop)).continuousAt (x:=0)|>.tendsto).mono_left (@nhdsWithin_le_nhds ℝ _ 0 (Set.Ioi 0)) -- syntax
 obtain ⟨c,h,u⟩:= ((hp.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and self_mem_nhdsWithin).exists; exact ⟨c,u,h⟩

include X in
lemma spinster (σ ρ K:ℝ): ∃ c:ℝ,0<c∧∃ r N:ℕ,∀{n:Side}{u:Stage}{P:Bed}{C:ℝ}{A:Matrix (Body 2 n) (Body 2 n) ℝ},Gate u P ρ C σ K n A →N≤ n.val→ ∃ y∈ marketZ r,lapse ℓ y∧ c< |Herald X A (wrap n y)|:=by
 obtain ⟨r,N,u⟩:= (catchPX X ℓ σ ρ K).exists; obtain ⟨c,h,t⟩:=fareMX r ℓ; refine ⟨c,h,r,N,fun {n u' P C A} g v=>?_⟩; obtain ⟨he,s,p,q,h'⟩:=u n v; by_contra! y
 let X₁:=machine s ℓ p q (bridgeX X A r); let U(x: Site n):ℂ:= ↑(Herald X A x); refine t.not_ge ((earnsMX s p q ℓ _ (h' g)).trans (priceMX s p q ℓ r U he h.le (fun x t v=> by unfold U; rw [Complex.norm_real]; exact y x t v)))

#print axioms spinster
end IndigoLX
end Tulipe
end YM.SU5.FiniteGaugeData.LapisQ
