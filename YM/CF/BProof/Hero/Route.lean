import YM.CF.BProof.Hero.Bill
/-! Budget for standard dictionaries before h and reach; uniform derivative bounds.
Coordinates incl full route for comparisons. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hero
open Function Dream Cube Spin Extension Filter Set Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Finset Lattice
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
abbrev TimeR:=Set.Icc (0:ℝ) 2
@[simp] lemma timeR0 : (0:ℝ)∈TimeR:=⟨le_rfl,by norm_num⟩
@[simp] lemma timeR1 : (1:ℝ)∈TimeR:=⟨by norm_num,by norm_num⟩
@[simp] lemma timeR2 : (2:ℝ)∈TimeR:=⟨by norm_num,le_rfl⟩
abbrev CostZ:= Zone ×ˢ TimeR
variable {A : Type*}[NormedAddCommGroup A][NormedSpace ℝ A]
structure ScrollZ (F:ℝ→ℝ→A)(K:ℝ): Prop where
 entries : Lip CostZ K (Function.uncurry F)
 flux (x:ℝ)(p:x∈Zone)(t:ℝ)(q:t∈TimeR): ‖deriv (F x) t‖≤K
lemma derivPath (x:ℝ)(t:ℝ)(F:ℝ→ℝ→A)(h: DifferentiableAt ℝ (Function.uncurry F) (x,t)) : deriv (F x) t=fderiv ℝ (Function.uncurry F) (x,t) (0,1):= (HasFDerivAt.comp_hasDerivAt t (show HasFDerivAt (Function.uncurry F) _ (x,t) from h.hasFDerivAt) (HasDerivAt.prodMk (hasDerivAt_const t x) (hasDerivAt_id t))).deriv -- tune
lemma deriv_c (F:ℝ→ℝ→A)(h:ContDiff ℝ ∞ (Function.uncurry F)): Continuous (fun x : ℝ × ℝ=>deriv (F x.1) x.2):=by simp_rw [fun x t=> derivPath x t F (h.differentiable (by simp) _)]; exact (h.continuous_fderiv (by simp)).clm_apply continuous_const
lemma scrollZ(F:ℝ→ℝ→A)(h:ContDiff ℝ ∞ (Function.uncurry F)): ∃ K:ℝ,0<K∧ScrollZ F K:=by
 have hc:IsCompact CostZ:= isCompact_Icc.prod isCompact_Icc; obtain ⟨K,hK,H⟩:= Mar.suit_cost CostZ (Function.uncurry F) hc ((convex_Icc ..).prod (convex_Icc ..)) (fun x hx=>h.contDiffAt); obtain ⟨L,hL⟩:= hc.bddAbove_image (f:=fun x=> ‖deriv (F x.1) x.2‖) (deriv_c F h).norm.continuousOn
 refine ⟨max K L,hK.trans_le (le_max_left ..),H.mono Subset.rfl (le_max_left ..),fun x hx t ht=> ((hL ⟨(x,t),⟨hx,ht⟩,rfl⟩)).trans (le_max_right ..)⟩ -- nested? tune
namespace ScrollZ
variable {F:ℝ→ℝ→A}{x z u v K:ℝ}(h:ScrollZ F K)
include h
lemma leT {s:ℝ}(p:K≤s): ScrollZ F s:=⟨h.entries.mono Subset.rfl p,fun x hx y hy=>(h.flux x hx y hy).trans p⟩ -- h binder include
lemma span (p:x∈Zone)(t:u∈TimeR)(q:z∈Zone)(e:v∈TimeR): ‖F x u-F z v‖ ≤ K*max |x-z| |u-v|:=by simpa only [Prod.dist_eq,Real.dist_eq,Function.uncurry_apply_pair] using h.entries (x,u) ⟨p,t⟩ (z,v) ⟨q,e⟩ -- tune uncurry
lemma horizon (p:x∈Zone)(t:u∈TimeR)(q:z∈Zone) : ‖F x u-F z u‖≤ K*|x-z| := by have he:= h.span p t q t; simpa only [sub_self,abs_zero,max_eq_left (abs_nonneg (x-z))] using he
end ScrollZ

def lung (x:ℝ):=ease (15*(1/6-x))
lemma lungS:ContDiff ℝ ∞ lung:= ease_s.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
lemma lung_z {x:ℝ}(h:1/6≤x): lung x=0:= ease_low _ (by linarith)
lemma lung_b {x:ℝ}(h:x≤1/10): lung x=1:= ease_up _ (by linarith)
structure Trip(K:ℝ):Prop where
 one:1≤K
 BMw: ScrollZ BM K
 TGw(i:Fin 5): ScrollZ (TG i) K
 amend(i:Fin 5): ScrollZ (Dream.amend i) K
 XGw(i:Fin 5): Lip Zone K (fun x=>(XG i x).val)
 lungw : Lip Zone K lung
 easeW : Lip Zone K ease -- maybe needed other intervals
lemma plan : ∃ K,Trip K:=by
 have h:IsCompact Zone:=isCompact_Icc; have hz:Convex ℝ Zone:= convex_Icc ..; choose k b hk using (fun i=>scrollZ (TG i) (TG_s i)); obtain ⟨i,-,hi⟩:= exists_max_image univ k univ_nonempty; choose a ha e using (fun i=> scrollZ (Dream.amend i) (amend_s i)); obtain ⟨j,-,hj⟩:= exists_max_image univ a univ_nonempty; choose d hd g using fun i=> Mar.suit_cost Zone (fun x=>(XG i x).val) h hz (fun x hx=> (XG_s i).contDiffAt); obtain ⟨m,-,hm⟩:= exists_max_image univ d univ_nonempty; obtain ⟨P,p,W⟩:= scrollZ BM BM_s; obtain ⟨Q,q,V⟩:= Mar.suit_cost _ lung h hz (fun _ _=>lungS.contDiffAt); obtain ⟨r,hr,H⟩:= Mar.suit_cost _ ease h hz (fun _ _=>ease_s.contDiffAt);
 let K:=1+k i+a j+d m+P+Q+r; have ht:=b i; have he:=ha j; have hg:=hd m
 refine ⟨K,by unfold K; linarith,W.leT ?_,fun x=>(hk x).leT ((hi _ (mem_univ _)).trans ?_),fun x=>(e x).leT ((hj _ (mem_univ _)).trans ?_),fun x=>(g x).mono Subset.rfl ((hm _ (mem_univ _)).trans ?_),V.mono Subset.rfl ?_,H.mono Subset.rfl ?_⟩ <;> unfold K <;> linarith

def rateH := plan.choose
lemma expenses : Trip rateH:= plan.choose_spec
lemma rate_p : 0<rateH:=zero_lt_one.trans_le expenses.one
-- useful real path Stamp motion.
lemma flowS {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](v:E){F:X→Stamp}(h:ContDiff ℝ ∞ F): ContDiff ℝ ∞ (motion v∘ F):=moldS contDiff_const h
lemma movingH(v:E) : ∃ L:Stamp →L[ℝ] Stamp,(↑L:Stamp→Stamp)=motion v :=by
 let L: Stamp →ₗ[ℝ] Stamp:= {toFun:=motion v,map_add':=fun x y=> (by unfold motion congrC; rw [mul_add,add_mul]),map_smul':=fun x y=> (by unfold motion congrC; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rfl)}; exact ⟨L.toContinuousLinearMap,rfl⟩
lemma motionDer (v:E){F:ℝ→Stamp}(h:ContDiff ℝ ∞ F)(x:ℝ): deriv (motion v∘F) x=motion v (deriv F x):=by obtain ⟨L,e⟩:=movingH v; rw [←e]; exact (L.hasFDerivAt.comp_hasDerivAt x ((h.differentiable (by simp) x).hasDerivAt)).deriv
-- suitability for Loft & tapes
abbrev Money (M:ℝ→Stamp) : Prop:= (∀ x,SealH (M x))∧ ContDiff ℝ ∞ M∧ ∀ t∈TimeR, ‖deriv M t‖≤ rateH
namespace Money
variable {f:ℝ→Stamp}(h: Money f)
include h
lemma weight(t:ℝ) : ‖f t‖=1:= CStarRing.norm_of_mem_unitary (h.1 t).norm
lemma pile (v:E): Money (motion v ∘ f):= ⟨fun x=> seal_move v (h.1 x),flowS _ h.2.1, fun x hx=> (motionDer v h.2.1 x).symm ▸ (seat_norm v (deriv f x)).trans_le (h.2.2 x hx)⟩ -- tune
lemma budget (x y:ℝ)(hx:x∈TimeR)(hy:y∈TimeR) : ‖f x-f y‖≤ rateH*|x-y|:=(by rw [←Real.norm_eq_abs]; exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x h'=> (((h.2.1).differentiable (by simp) x).hasDerivAt).hasDerivWithinAt) (h.2.2) (convex_Icc ..) hy hx) -- tune name
lemma shrink (p:ℝ)(v:p∈ Zone): Money (fun x=> f (p*x)):=by
 let F:=fun (x:ℝ)=>p*x; refine ⟨fun x=> h.1 _,(h.2.1).comp (contDiff_const.mul contDiff_id),fun x hx=>?_⟩; have he:F x∈TimeR:= ⟨mul_nonneg v.1 hx.1,(mul_le_of_le_one_left hx.1 v.2).trans hx.2⟩
 have hh(x):HasDerivAt F p x:=by have ht:HasDerivAt F (p*1) x:=(hasDerivAt_id x).const_mul p; simpa using ht
 change ‖deriv (f∘F) x‖≤rateH
 rw [(HasDerivAt.scomp x ((h.2.1.differentiable (by simp) (F x)).hasDerivAt) (hh x)).deriv,norm_smul,Real.norm_of_nonneg v.1]; exact (mul_le_of_le_one_left (norm_nonneg _) v.2).trans (h.2.2 _ he) -- tune `rw` under defeq
end Money
lemma quietM (U:Stamp)(h:SealH U):Money (fun _=>U):= ⟨fun _=>h, contDiff_const,fun _ _=> by simp [rate_p.le]⟩
lemma seatedM {F:ℝ→ℝ→ Stamp}(h:ScrollZ F rateH)(p:ContDiff ℝ ∞ (Function.uncurry F))(H:∀ i j,SealH (F i j))(i:ℝ)(hx:i∈Zone): Money (F i):= ⟨H _,p.comp (contDiff_const.prodMk contDiff_id),h.flux i hx⟩
lemma moneyB {t:ℝ}(h:t∈Zone): Money (BM t):= seatedM expenses.BMw BM_s BM_seal _ h
lemma moneyA(i:Fin 5){t:ℝ}(h:t∈ Zone): Money (amend i t):= seatedM (expenses.amend i) (amend_s i) (amend_seal i) _ h
lemma moneyT(i:Fin 5){t:ℝ}(h:t∈Zone): Money (TG i t):= seatedM (expenses.TGw i) (TG_s i) (TG_seal i) _ h
end YM.CF.BProof.Hero
