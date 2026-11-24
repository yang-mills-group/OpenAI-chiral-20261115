import YM.OS.Core
/-!
# Canonical continuous part of an abstract germ unitary group

Suppose the action of a dense grid of translations is known, *without any
measurability or continuity assumptions*. We can still exploit continuity of
coefficients **at specific points** (e.g. matching OS kernels separated far in one
coordinate). Removing the discontinuous sectors does not affect these values.
Reason: orthogonal projection on continuous vectors is in the hull of
arbitrarily small translates. Use parallelogram (no mean or countability). Only
R subgroup asserted here; can apply in components independently.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Set Function Filter Metric Complex
open scoped Topology InnerProductSpace ComplexOrder
namespace Germ
structure Players (Γ : AddSubgroup ℝ) (H:Hilbert) where
 play : Γ → H.Op
 pulls (i:Γ)(x:H) : ‖play i x‖ ≤ ‖x‖
 play_zero:play 0=ContinuousLinearMap.id ℂ _
 piles(i j:Γ):(play i).comp (play j)=play (i+j)
variable {Γ : AddSubgroup ℝ}(H:Hilbert)(P:Players Γ H)
namespace Players
lemma paved (i j:Γ)(x:H):P.play i (P.play j x)=P.play (i+j) x:=by rw [←ContinuousLinearMap.comp_apply,P.piles]
lemma symmetric (i j:Γ)(x:H):P.play i (P.play j x)=P.play j (P.play i x):=by rw [P.paved,P.paved,add_comm]
lemma wins (i:Γ)(x:H): ‖P.play i x‖=‖x‖:=le_antisymm (P.pulls ..) (by have h:=P.pulls (-i) (P.play i x); rwa [P.paved,neg_add_cancel,P.play_zero] at h)
lemma rigid (i:Γ)(x y:H): dist (P.play i x) (P.play i y)=dist x y:=by simp only [dist_eq_norm,←map_sub,P.wins]
lemma returns(i:Γ)(x:H):P.play (-i) (P.play i x)=x:= by rw [P.paved,neg_add_cancel,P.play_zero]; rfl
lemma inner_g (i:Γ)(x y:H): inner ℂ (P.play i x) (P.play i y)=inner ℂ x y:=
 LinearIsometry.inner_map_map (𝕜:=ℂ) (show H.space →ₗᵢ[ℂ] H.space from { (P.play i).toLinearMap with norm_map':=P.wins H i}) x y
lemma shift_g(i:Γ)(x y:H):inner ℂ x (P.play i y) = inner ℂ (P.play (-i) x) y:=by rw [←P.inner_g H (-i) x (P.play i y),P.returns]

def lives : Submodule ℂ H where
 carrier:={x|ContinuousAt (fun i=>P.play i x) 0}
 zero_mem':=by simp only [mem_setOf,map_zero]; exact continuousAt_const
 add_mem':=fun {x y} (p:ContinuousAt (fun i=>P.play i x) 0)(q: ContinuousAt (fun i=>P.play i y) 0) =>by
   change ContinuousAt (fun i=>P.play i (x+y)) _; simp only [map_add]; exact p.add q
 smul_mem':=fun c {x} (p:ContinuousAt (fun i=>P.play i x) 0) =>by
   change ContinuousAt (fun i=>P.play i (c•x)) _; simp only [map_smul]; exact continuousAt_const.smul p
-- switch to epsilon estimate
variable {H}
lemma living {x:H}:x∈ lives H P ↔ ∀ ε:ℝ, 0<ε → ∃ δ:ℝ, 0<δ ∧ ∀ i:Γ, |(i:ℝ)| < δ → dist (P.play i x) x < ε:=by
 change ContinuousAt (fun i=>P.play i x) 0 ↔ _
 rw [Metric.continuousAt_iff]; simp only [P.play_zero]
 have h(i:Γ): dist i (0:Γ)=|(i:ℝ)|:=by change dist (i:ℝ) (0:ℝ)=_; exact Real.dist_0_eq_abs _
 simp only [h,ContinuousLinearMap.id_apply]
lemma lives_closed : IsClosed (P.lives H:Set H):=by
 rw [← closure_subset_iff_isClosed]; intro x hx
 refine (P.living).mpr fun ε h=> ?_
 obtain ⟨i,hi,p⟩:=Metric.mem_closure_iff.mp hx (ε/3) (by positivity)
 obtain ⟨δ,q,t⟩:=P.living.mp hi (ε/3) (by positivity)
 refine ⟨δ,q,fun w hw=> ?_⟩
 calc dist (P.play w x) x ≤ dist (P.play w x) (P.play w i)+dist (P.play w i) x:=dist_triangle ..
   _ ≤ dist x i+(dist (P.play w i) i+dist i x):=by rw [P.rigid H]; exact add_le_add_right (dist_triangle (P.play w i) i x) _
   _ < ε:=by rw [dist_comm i x]; linarith [t w hw]
instance complete : CompleteSpace (P.lives H):=(P.lives_closed.completeSpace_coe)
noncomputable def pi_c:H.Op:=(P.lives H).starProjection
lemma repaired (x:H):P.pi_c x∈ P.lives H:=(P.lives H).starProjection_apply_mem _

-- lemma names check
-- Uniform continuity of those orbits even for whole Γ
lemma far{x:H}(t:x∈lives H P):UniformContinuous (fun i=>P.play i x):=by
 rw [Metric.uniformContinuous_iff]; intro ε p
 obtain ⟨δ,e,z⟩:= P.living.mp t ε p
 refine ⟨δ,e,fun i j h=> ?_⟩
 have hz:P.play j (P.play (i-j) x)=P.play i x:=by rw [P.paved,add_comm,sub_add_cancel]
 rw [←hz,P.rigid H]; exact z _ (by simpa [Real.dist_eq] using (show dist (i:ℝ) (j:ℝ)<_ from h))

local notation "mid" x:max y:max=> ((1/2:ℂ) • (x+y))
lemma midpar (H:Hilbert) (x y:H) : 4*‖mid x y‖^2+dist x y^2=2*(‖x‖^2+‖y‖^2):=by
 rw [dist_eq_norm,norm_smul]
 norm_num
 nlinarith [parallelogram_law_with_norm_mul ℂ x y]
-- hull of arbitrarily small shifts, enough to allow dyadic midpoint
inductive hull (Γ:AddSubgroup ℝ) (H:Hilbert)(P:Players Γ H)(ε:ℝ)(x:H): H→Prop where
 | point (i:Γ)(h: |(i:ℝ)| < ε): hull Γ H P ε x (P.play i x)
 | midline {a b} (i:hull Γ H P ε x a)(h:hull Γ H P ε x b): hull Γ H P ε x (mid a b)
private lemma sale{ε δ:ℝ}(p:ε ≤ δ){x y:H}(q:hull Γ H P ε x y):hull Γ H P δ x y:=by
 induction q with
 | point i h=> exact hull.point i (h.trans_le p)
 | midline i h t₀ t₁=> exact t₀.midline t₁
private lemma oneself{ε:ℝ}(p:0< ε){x:H}:hull Γ H P ε x x:=by
 have t:hull Γ H P ε x (P.play 0 x):=hull.point _ (by simpa using p)
 rwa [P.play_zero] at t
private lemma shifts_hull {ε:ℝ}{x y:H}(p:hull Γ H P ε x y)(i:Γ): hull Γ H P (ε+|(i:ℝ)|) x (P.play i y) :=by
 induction p with
 | point j a=> rw [P.paved]; apply hull.point; rw [AddSubgroup.coe_add]; apply (abs_add_le _ _).trans_lt; linarith
 | midline j a b c=> simp only [map_smul,map_add]; apply hull.midline b c

private def lown(ε:ℝ)(x:H):ℝ:=sInf ((fun y:H=>‖y‖^2) '' {y|hull Γ H P ε x y})
private lemma min_fee {ε:ℝ}{x y:H}(p:hull Γ H P ε x y): lown P ε x ≤ ‖y‖^2:= csInf_le (by use 0; rintro _ ⟨a,t,rfl⟩; exact sq_nonneg _) ⟨y,p,rfl⟩
private def level(x:H):ℝ:=sSup ((fun u=>lown P u x) '' Set.Ioi 0) -- parser
private lemma reach_level {ε:ℝ}(e:0<ε)(x:H):lown P ε x ≤ level P x:= by
 refine le_csSup (a:= lown P ε x) ?_ ⟨ε,e,rfl⟩
 use ‖x‖^2
 rintro _ ⟨a,t,rfl⟩
 exact min_fee P (oneself P t)
private lemma challenge (x:H)(v:ℝ)(h:v<level P x):∃ ε:ℝ,0<ε ∧ v<lown P ε x:=by
 obtain ⟨v,h,hv⟩:= exists_lt_of_lt_csSup (s:= (fun u=>lown P u x) '' Set.Ioi 0) (by use lown P 1 x; exact ⟨1,Set.mem_Ioi.mpr one_pos,rfl⟩) h
 obtain ⟨z,e,rfl⟩:=h; exact ⟨z,e,hv⟩
private lemma candidate {ε:ℝ}(p:0<ε)(x:H){v:ℝ}(h:lown P ε x<v):∃ y:H,hull Γ H P ε x y∧‖y‖^2<v:=by
 let s:= (fun y:H=>‖y‖^2) '' {y|hull Γ H P ε x y}
 obtain ⟨v,t,r⟩:=exists_lt_of_csInf_lt (s:=s) (by use ‖x‖^2; exact ⟨x,oneself P p,rfl⟩) h
 obtain ⟨y,t,rfl⟩:=t; exact ⟨y,t,r⟩
private lemma ideal (x:H):∃ z:H, ‖z‖^2 ≤ level P x ∧ ∀ ε:ℝ, 0< ε→ z∈ closure {y|hull Γ H P ε x y}:=by
 let δ(n:ℕ):ℝ:= (1/2)^n
 have h(n): 0 < δ n :=by unfold δ; positivity
 have ht(n):lown P (δ n) x<level P x+δ n:=(reach_level P (h n) x).trans_lt (by linarith [h n])
 choose w hw hq using fun n=>candidate P (h n) x (ht n)
 have hδ:Tendsto δ atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 have he:Tendsto (fun i=>level P x+δ i) atTop (𝓝 (level P x)):=by simpa using (tendsto_const_nhds (x:=level P x)).add hδ
 have p:CauchySeq w:=by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let c:=level P x; let a:=ε^2/10
    have ha:0<a:=by unfold a; positivity
    obtain ⟨b,hb,hz⟩:=challenge P x (c-a) (by change c-a<c; linarith)
    obtain ⟨N,t⟩:=eventually_atTop.mp (hδ.eventually (gt_mem_nhds (lt_min ha hb)))
    refine ⟨N,fun u hu v hv=>?_⟩ -- arg order
    have h₁: hull Γ H P b x (w u) :=sale _ ((t _ hu).le.trans (min_le_right ..)) (hw u)
    have h₂: hull Γ H P b x (w v) :=sale _ ((t _ hv).le.trans (min_le_right ..)) (hw v)
    have hMera:=hz.trans_le (min_fee P (h₁.midline h₂))
    have hM (i) (p:N ≤ i) : ‖w i‖^2 ≤ c+a:=(hq i).le.trans (add_le_add_right ((t i p).le.trans (min_le_left ..)) _)
    have hp:=dist_nonneg (x:=w u) (y:=w v)
    apply (sq_lt_sq₀ hp hε.le).mp
    have hhalf:=midpar H (w u) (w v); unfold a at *; linarith [hM u hu,hM v hv]
 obtain ⟨z,hz⟩:=cauchySeq_tendsto_of_complete p
 refine ⟨z, le_of_tendsto_of_tendsto' (hz.norm.pow 2) he (fun i=>(hq i).le),fun ε hε=> mem_closure_of_tendsto hz ?_⟩
 exact (hδ.eventually (gt_mem_nhds hε)).mono fun i hi=>sale _ hi.le (hw i)

-- minimal point lives
private lemma minor_lives {x z:H}(t: ‖z‖^2 ≤ level P x)(p:∀ ε:ℝ, 0< ε → z∈ closure {y| hull Γ H P ε x y}): z∈ lives H P:=by
 rw [living]; intro ε e
 let c:=level P x; let a:=ε^2/8
 have ha:0<a:=by unfold a; positivity
 obtain ⟨b,hb,hv⟩:=challenge P x (c-a) (by change c-a<c; linarith)
 let S:Set H:={w| hull Γ H P b x w}
 have he {w y:H}(h:w∈ closure S)(t:y∈ closure S):lown P b x ≤ ‖mid w y‖^2:=by
    have hcl : IsClosed ({z:H×H | lown P b x ≤ ‖mid z.1 z.2‖^2}) :=isClosed_le continuous_const (by fun_prop)
    have ht: S ×ˢ S ⊆ {z:H×H | lown P b x ≤ ‖mid z.1 z.2‖^2}:=fun i u=> min_fee _ (hull.midline u.1 u.2)
    exact closure_minimal ht hcl (show (w,y)∈ closure (S ×ˢ S) by rw [closure_prod_eq]; exact mem_prod.mpr ⟨h,t⟩)
 refine ⟨b/2,by positivity,fun i hi=> ?_⟩
 have h₁: P.play i z ∈ closure S:=by
    apply MapsTo.closure (f:=(P.play i : H → H)) (t:=S) (s:={y|hull Γ H P (b/2) x y}) ?_ (P.play i).continuous (p (b/2) (by positivity))
    intro y T; exact sale _ (by linarith : b/2 + |(i:ℝ)| ≤ b) (shifts_hull P T i)
 have hhalf := midpar H (P.play i z) z
 have hMera:=hv.trans_le (he h₁ (p b hb))
 rw [P.wins H] at hhalf
 apply (sq_lt_sq₀ dist_nonneg e.le).mp
 change ‖z‖^2≤ c at t; unfold a at hMera; nlinarith

-- local continuity of a given coefficient means it agrees with the ideal
-- (polarized with arbitrary v, no hysteresis); expressed directly
private lemma patch {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y](L:H→L[ℂ]Y){x z:H}(p:∀ ε:ℝ,0< ε→z∈closure {y|hull Γ H P ε x y})(t:ContinuousAt (fun i=> L (P.play i x)) 0): L z=L x:=by
 apply eq_of_forall_dist_le (x:=L z) (y:=L x); intro ε q
 obtain ⟨δ,hδ,h⟩:=Metric.continuousAt_iff.mp t ε q
 let s:= closedBall (L x) ε
 have hi(i:Γ)(p:|(i:ℝ)| < δ): L (P.play i x)∈ s:=by
    have hp:dist i (0:Γ)< δ:=by change dist (i:ℝ) (0:ℝ)<_; rw [Real.dist_0_eq_abs]; exact p
    have he:=h hp; change dist (L _) (L _)<_ at he; simpa [s, P.play_zero] using he.le
 have hw:MapsTo L {y|hull Γ H P δ x y} s:=by
    intro y hy; induction (show hull _ _ _ _ _ y from hy) with
    | point i h=> exact hi i h
    | midline i k hi hk=>
      rename_i a b
      rw [Metric.mem_closedBall] at hi hk ⊢; simp only [map_add,map_smul]; rw [dist_eq_norm] at hi hk ⊢
      have hx (u v:Y): (1/2:ℂ)•(u+v)-L x=(1/2:ℂ)•((u-L x)+(v-L x)):=by simp_rw [smul_add,smul_sub]; rw [←add_sub_add_comm, ← add_smul]; norm_num
      rw [hx,norm_smul]; norm_num; nlinarith [norm_add_le (L a-L x) (L b-L x) , hi i,hk k]
 exact hw.closure_left L.continuous Metric.isClosed_closedBall (p δ hδ)

-- consequence: retain any locally continuous coefficient (even if orbit is discontinuous)
lemma retain {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y](L:H→L[ℂ]Y)(x:H)(p:ContinuousAt (fun i=>L (P.play i x)) 0):L (P.pi_c x)=L x:=by
 obtain ⟨z,t,h⟩:=ideal P x
 have e:= minor_lives _ t h
 have hπ:P.pi_c x=z:=by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero e
    intro y k
    rw [inner_sub_left,sub_eq_zero]
    have hz: ContinuousAt (fun i=>innerSL ℂ y (P.play i x)) 0:=by
       change ContinuousAt (fun i=>inner ℂ y (P.play i x)) 0
       simp_rw [P.shift_g H]
       have g: ContinuousAt (fun i:Γ=>P.play (-i) y) 0 := (P.far k).continuous.continuousAt.comp (continuous_neg (G:=Γ)).continuousAt
       exact g.inner continuousAt_const
    have hv:=patch P (innerSL ℂ y) h hz
    simpa only [innerSL_apply_apply, inner_conj_symm] using (congrArg (starRingEnd ℂ) hv).symm
 rw [hπ]; exact patch P L h p

lemma commutes(T:H.Op)(p:∀ i,(P.play i).comp T=T.comp (P.play i))(q:∀ i,(P.play i).comp T.adjoint=T.adjoint.comp (P.play i)): T.comp P.pi_c = P.pi_c.comp T:=by
 let S:=P.lives H
 have he(T:H.Op)(p:∀ i,(P.play i).comp T=T.comp (P.play i))(x:H)(h:x∈ S):T x∈ S:=by
    have q:ContinuousAt (fun i=>T (P.play i x)) 0:=T.continuous.continuousAt.comp (show ContinuousAt _ 0 from h)
    change ContinuousAt (fun i=>P.play i (T x)) 0
    exact q.congr (Eventually.of_forall fun i=> congr_fun (congrArg DFunLike.coe (p i).symm) x)
 ext v
 change T (P.pi_c v) = S.starProjection (T v)
 symm; apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (he T p _ (P.repaired v))
 intro y k; rw [←map_sub,←ContinuousLinearMap.adjoint_inner_right T]
 exact Submodule.starProjection_inner_eq_zero _ _ (he T.adjoint q y k)

lemma neg_adjoint(i:Γ):(P.play i).adjoint=P.play (-i):=by
 ext1 x; apply ext_inner_right ℂ; intro y
 rw [ContinuousLinearMap.adjoint_inner_left,P.shift_g H]
lemma commutes_c(T:H.Op)(p:∀ i,(P.play i).comp T=T.comp (P.play i)): T.comp P.pi_c = P.pi_c.comp T:=by
 apply commutes P T p; intro i
 have h:=congrArg ContinuousLinearMap.adjoint (p (-i))
 rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,P.neg_adjoint,neg_neg] at h
 exact h.symm
lemma pi_adj: P.pi_c.adjoint=P.pi_c:=by
 ext1 x; apply ext_inner_left ℂ; intro y
 rw [ContinuousLinearMap.adjoint_inner_right]
 exact (P.lives H).inner_starProjection_left_eq_right _ _

-- Need interaction between two reps of same group with matching coeff *not*
-- known to be continuous (e.g. common transverse motions in axis turn).
-- π produces canonical continuous part. Claim their projected values equal:
-- average on F's orbit converging πF also produces continuous on G? its
-- coefficients against G variations determined by equality only for given
-- x*,x and y*,y. Want inner π value given same coeff on a neighborhood.
-- Since nearby shifts don't converge to π weak except designed averages on
-- x, their application to y may fail to π. But work on direct sum x ⊕ y,
-- Players direct sum π splits; one hull average produces both!
-- Prove without making L on direct sum, reuse retain with difference zero.
-- model complex product Hilbert using WithLp 2. TODO.
lemma pi_fixer {x:H}(p:x∈P.lives H):P.pi_c x=x:=Submodule.starProjection_eq_self_iff.mpr p
lemma pi_idem(x:H):P.pi_c (P.pi_c x)=P.pi_c x:=pi_fixer P (P.repaired _)
lemma pi_play (x:Γ): (P.play x).comp P.pi_c=P.pi_c.comp (P.play x):=P.commutes_c _ (fun i=> ContinuousLinearMap.ext (fun y=>P.symmetric H i x y))
lemma retains_at {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y](L:H→L[ℂ]Y)(x:H)(c:Γ)(t: ContinuousAt (fun i=>L (P.play i x)) c): L (P.play c (P.pi_c x))=L (P.play c x):=by
 apply retain P (L.comp (P.play c)) x
 change ContinuousAt (fun i=> L (P.play c (P.play i x))) _; simp_rw [P.paved]
 apply ContinuousAt.comp_of_eq t (continuous_const.add continuous_id).continuousAt
 exact add_zero _
end Players
end Germ
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Players.retain
#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Players.retains_at
