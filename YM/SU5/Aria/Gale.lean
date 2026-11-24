import YM.SU5.FiniteGaugeData.Tower.GermUnit
/- Copy private utilities & proof from GermUnit.lean to expose the hull projection assertion itself (changing its `retain` proof conclusion). Uses only abstract Hilbert spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Set Function Filter Metric Complex
open scoped Topology InnerProductSpace ComplexOrder
namespace Germ
variable {Γ : AddSubgroup ℝ}(H:Hilbert)(P:Players Γ H)
namespace Players
variable {H}
local notation "mid" x:max y:max=> ((1/2:ℂ) • (x+y))
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

lemma haze_projection (x:H)(ε:ℝ)(δ:0 < ε):P.pi_c x ∈ closure {y:H| hull Γ H P ε x y}:=by
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
 rw [hπ]; exact h ε δ
#print axioms haze_projection
end Players
end Germ
end YM.CF.Buffered.Afterglow.Tower
