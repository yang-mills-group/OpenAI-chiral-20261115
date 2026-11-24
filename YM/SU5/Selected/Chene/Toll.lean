import YM.SU5.Selected.Chene.Token
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Chene.Perks
open Function Filter MeasureTheory Metric Lattice Wilson RG Tree Precision Next.SectorChange AnalyticBridge.Annulus1AD SectorNext.Vacuum CF.Appel
open Next.Fluctuations Next.Fluctuations.Sector Pressure Pressure.Stores Matrix Trunk Pad Tail FreeResolvent AnalyticBridge.LocalGaussianLaws CF.Neige Next.Rank.Axial
open scoped Topology BigOperators ENNReal Classical MatrixOrder Matrix Kronecker
variable {G:Gauge}(L:ChartRatio G)(p:LocalRatio L) [Nonempty G.ColorIndex]{c f:Side}{S:StepData c f} {ρ μ E v z d x u:ℝ}
lemma lint (D:ℝ)(p:0<D):∃ θ:ℝ,0<θ∧ θ<1 ∧ |Real.log (1-θ)| ≤  D ∧ |Real.log (1+θ)| ≤  D:=by
 have hx:ContinuousAt (fun θ:ℝ=> |Real.log (1-θ)|) 0:= by apply ContinuousAt.abs; apply ContinuousAt.log (by fun_prop); norm_num
 have he:ContinuousAt (fun θ:ℝ=> |Real.log (1+θ)|) 0:= by apply ContinuousAt.abs; apply ContinuousAt.log (by fun_prop); norm_num
 let l:= hx.tendsto.eventually (ge_mem_nhds (by simpa using p: |Real.log (1-(0:ℝ))|< D)); let r:= he.tendsto.eventually (ge_mem_nhds (by simpa using p: |Real.log (1+(0:ℝ))|< D))
 obtain ⟨θ,h,h'⟩:= ((eventually_nhdsWithin_of_eventually_nhds ((gt_mem_nhds zero_lt_one).and (l.and r))).and (self_mem_nhdsWithin (α:=ℝ) (a:=0) (s:=Set.Ioi 0))).exists; exact ⟨θ,h',h⟩
abbrev cup (G:Gauge)(ε:ℝ):= ε/(100*(1+atoms0 G))
lemma cup_pos(p:0<v) : 0< cup G v:=by unfold cup atoms0; positivity
lemma stem (S:StepData c f): bulk c ≤ bulk f:= by unfold bulk; gcongr; apply Fintype.card_le_of_injective S.ratio.embed; intro i j h; rw [← S.ratio.embed_parent i,← S.ratio.embed_parent j,h]
lemma count_less (S:StepData c f)(F:Forest S.ratio): (Fintype.card F.Free:ℝ) ≤ 4*bulk f:=by rw [←bulk_edge]; apply Nat.cast_le.mpr; exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
lemma heads (S:StepData c f) : (shoots c:ℝ)≤4*bulk f := by rw [← bulk_edge]; exact Nat.cast_le.mpr ((show shoots c≤ quantity c from Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans (show quantity c ≤ _ from Nat.cast_le (α:=ℝ)|>.mp (by rw [bulk_edge,bulk_edge]; exact mul_le_mul_of_nonneg_left (stem S) (by norm_num)))) -- tune
lemma apex (F:Forest S.ratio)(G:Gauge) : (Fintype.card (Key F G):ℝ)=Fintype.card F.Free*atoms0 G:= by unfold atoms0; change (↑(Fintype.card (F.Free × _)):ℝ)=_; norm_cast; exact Fintype.card_prod ..
private lemma brief (ε:ℝ) (e:0<ε)(C Q F H N Z :ℝ)(hp:0≤Z)(hc:0≤H)(hk:0≤N)(v:C≤Z)(h:Q≤4*Z)(r:F≤4*Z)(t:H≤4*Z) : let j:= ε/(100*(1+N)); j*(Q+F+H*N/2)+2* F*N * j/2 ≤ ε*Z:=by
 intro j; have hj:0< j:= div_pos e (by positivity); -- int
 calc
    _ ≤ j*(4*Z+4*Z+(4*Z)*N/2)+2*(4*Z)*N*j/2:= add_le_add (mul_le_mul_of_nonneg_left (add_le_add (add_le_add h r) (by gcongr)) hj.le) (by gcongr; first|linarith|skip)
    _ ≤ _ := by
       unfold j; field_simp; nlinarith only [hp,mul_nonneg hk hp,mul_nonneg hk (mul_nonneg e.le hp)]
include p
/-- reusable with `Look`: coarse horizon/y before sizes; ALL tube and costs data in the call are real. -/
theorem tenure (Q:KernelChoices)(σ μ C:ℝ)(K:Side)(hσ:0<σ)(hμ:0<μ)(ρ:ℝ)(hρ:0<ρ) :
    ∃ B> (0:ℝ),∀ (c f:Side)(S:StepData c f) (F:Forest S.ratio) (T:Tube G S) (H H':Bed)(P:Towers S.patch.L) (q:S.Choices), T.high.direct=μ → S.kernel=Q → ∀ (X u a D d:ℝ), 0<X → 0<d → Towers.Diagonal S H H' P → Gap (H'.metric.acts c) d → (H'.metric.acts c)ᵀ=H'.metric.acts c → T.up.Bounds T.high σ C u → Attached H T.up → Floor H T.high f X a → Bid.Larger (G:=G) S → Bid.Sworn H f G → ∀ (x b b' j:ℝ), B ≤ x→ B≤b →0<b' → B≤j → |Real.log b'-Real.log b| ≤ cup G ρ → (0< (baseX T x (bareStores S) F q 1).det ∧ |tariff L T F q b x j-(schedule L f H b-schedule L c H' b')| ≤ ρ*bulk f):=by
 let θ:=cup G ρ; have ht:0<θ:=cup_pos hρ
 obtain ⟨z,hz,hw,hX,hY⟩:=lint θ ht
 obtain ⟨A,T⟩:= eventually_atTop.mp (hinges σ C μ z G K hσ hμ hz)
 obtain ⟨c,U⟩:= eventually_atTop.mp (perk L p Q θ ht)
 have hm:∀ᶠ r:ℝ in atTop, |Real.log (point G r)| ≤ θ:= ((point_limit G).log one_ne_zero|>.abs).eventually (ge_mem_nhds (by simpa using ht: |Real.log (1:ℝ)|<θ))
 obtain ⟨d,V⟩:= eventually_atTop.mp hm; let Y:= max 1 (max A (max c d)); have hY':0<Y:=lt_max_of_lt_left zero_lt_one; have hp: A ≤ Y:=(le_max_left ..).trans (le_max_right ..); have hc:c≤ Y:= le_trans (le_max_left ..) ((le_max_right ..).trans (le_max_right ..)); have hq:d ≤ Y:= le_trans (le_max_right c d) ((le_max_right ..).trans (le_max_right ..)); refine ⟨Y,hY',?_⟩
 intro c f S F T' H H' P q m Q' ξ ρ α D κ α0 κ0 S0 k_ p' h X hx v s x b b' j a a' t J K'; have he:=checkpoint F T' H q h v.1 X hx s x v α0 z hz.le hw (show rate_ell σ C (till x)/T'.high.direct ≤ z^2 from m.symm ▸ T x (hp.trans a)); let M:= Fintype.card F.Free; let k:= 2*(Fintype.card (Key F G):ℝ)
 have r:0≤ k:=by unfold k; positivity
 let w:=stem S; have z':max (abs (k*Real.log (1-z))) (abs (k*Real.log (1+z))) ≤ k*θ:= by rw [abs_mul k (Real.log (1-z)), abs_mul k (Real.log (1+z)), abs_of_nonneg r]; exact max_le (mul_le_mul_of_nonneg_left hX r) (mul_le_mul_of_nonneg_left hY r)
 refine ⟨he.2.1,?_⟩
 apply le_trans (budget L p T' F _ _ _ q h S0 X hx k_ p' v s α0 κ0 _ _ _ _ _ _ (hY'.trans_le J) (hY'.trans_le a') t θ he.2.2.1 he.2.2.2 _ (mul_nonneg r ht.le) z' (by rw [Q']; exact U b (hc.trans a') c f S Q') (V j (hq.trans J)) K')
 unfold k; rw [apex]; conv_lhs=> rw [←_root_.mul_assoc (2:ℝ) (M:ℝ)] -- tune expansion
 apply brief _ hρ (bulk c) _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) w ((bulk_edge ..).le.trans (mul_le_mul_of_nonneg_left w (by norm_num))) (count_less S F) (heads S)
end YM.Chene.Perks
#print axioms YM.Chene.Perks.tenure
