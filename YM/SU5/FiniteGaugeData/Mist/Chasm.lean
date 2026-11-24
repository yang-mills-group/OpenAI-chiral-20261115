import YM.SU5.FiniteGaugeData.Mist.Pulley
/-! # The sliding estimate using only the elect clock.

 Identify projector on continuous space from H readings (no complex singular spectrum extension).
 Approximate with finite lists of sticks costed arbitrarily SMALL spacings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace
variable {H:Hilbert}{T: Type}[NormedAddCommGroup T]
namespace Willow
variable (Q:Willow H T)(w x:H)(r:T)(u:ℝ)
local notation "S"=>Standard Q
-- want hull public type not requiring real via ℂ.Complex.Real.smul. induction
inductive Gem (w:H)(u:ℝ) : H→ Prop where
 | glide (t:T)(p: ‖t‖<u): Gem w u (Q.U t w)
 | mount {x y:H} : Gem w u x→ Gem w u y→∀ a b:ℝ,0 ≤ a→ 0 ≤ b→ a+b=1 → Gem w u ((a:ℂ) • x+(b:ℂ) • y)
abbrev gliding := closure {x:H| Q.Gem w u x}
lemma casts (p:0<u) : w∈ Q.gliding w u:= by apply subset_closure; change Q.Gem w u w; have h:Q.Gem w u (Q.U 0 w):= Gem.glide (0:T) (by simpa); rw [Q.init] at h; exact h
lemma inclusion (p:Q.Gem w u x)(v:ℝ)(e:u≤v): Q.Gem w v x := by induction p with
 | glide t p=> exact Gem.glide t (p.trans_le e)
 | mount _ _ _ _ b c q ih iw=> exact Gem.mount ih iw _ _ b c q
lemma awake {v:ℝ}(p:u ≤ v): Q.gliding w u⊆ Q.gliding w v:= closure_mono (s:={x:H|Q.Gem w u x}) (fun x p'=> Q.inclusion _ x _ p' _ p) -- binder x?
-- y in 1/2-radius, shift by r. preserve D via true group
lemma serves {v:ℝ}(p:‖r‖+u ≤ v) : Set.MapsTo (Q.U r) (Q.gliding w u) (Q.gliding w v):=by
 refine Set.MapsTo.closure ?_ (Q.U r).continuous; intro x t; change Q.Gem _ _ _; change Q.Gem _ _ _ at t; induction t with
 | glide x q=> rw [Q.both_inner]; exact Gem.glide _ ((norm_add_le ..).trans_lt ((add_lt_add_right q _).trans_le p))
 | mount _ _ a b p q z ih ig=> rw [map_add,map_smul,map_smul]; exact Gem.mount ih ig a b p q z
local instance realH (H:Hilbert): InnerProductSpace ℝ H:=InnerProductSpace.rclikeToReal ℂ H.space
lemma glide_con : Convex ℝ (Q.gliding w u):= by
 have he: Convex ℝ {z:H|Q.Gem w u z}:=fun _ x _ y _ _ p q z=> Gem.mount x y _ _ p q z; exact he.closure
private lemma parag (x y:H): dist x y^2 +‖x+y‖^2=2*(‖x‖^2+‖y‖^2):=by rw [dist_eq_norm,add_comm]; simpa only [pow_two] using parallelogram_law_with_norm_mul ℂ x y
-- radius scheme 1/(n+1), not using period/horizon estimates here.
abbrev fiss (n:ℕ):ℝ:= 1/ (n+1:ℝ)
lemma fiss_pos (n:ℕ):0 < fiss n:= by unfold fiss; positivity
lemma decline : Antitone fiss:= fun _ _ t=> by unfold fiss; gcongr
lemma falls : Tendsto fiss atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
variable (n k:ℕ)
local notation "G" k:max=> gliding Q w (fiss k)
private lemma chasm_exists (u:ℝ)(p:0<u) :∃ y:H,y∈ gliding Q w u ∧ ∀ x∈Q.gliding w u,‖y‖ ≤ ‖x‖:=by
 let S':=Q.gliding w u; obtain ⟨y,b,q⟩:= exists_norm_eq_iInf_of_complete_convex ⟨_,casts Q w u p⟩ isClosed_closure.isComplete (glide_con Q w u) 0
 refine ⟨y,b,fun x p=>?_⟩; rw [zero_sub,norm_neg] at q; calc
     ‖y‖ = _:= q
     _ ≤ ‖0-(⟨x,p⟩:↥(Q.gliding w u)).val‖:= ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _=> norm_nonneg _)⟩ _
     _ = ‖x‖:= by simp
-- min norm in shrinking hull of (TRUE) translations
protected def Bottom := (chasm_exists Q w (fiss n) (fiss_pos n)).choose
protected lemma trough : Q.Bottom w n∈Q.gliding w (fiss n) := (chasm_exists Q w (fiss n) (fiss_pos n)).choose_spec.1
protected lemma floor (p:x∈ Q.gliding w (fiss n)):‖Q.Bottom w n‖ ≤ ‖x‖:= (chasm_exists Q w (fiss n) (fiss_pos n)).choose_spec.2 x p
private lemma bottom_upper (w:H): ‖Q.Bottom w n‖ ≤ ‖w‖:=Q.floor _ _ _ (Q.casts _ _ (fiss_pos n))
private lemma bottom_mono (w:H): Monotone (fun n=> ‖Q.Bottom w n‖^2):=fun _ j p=> pow_le_pow_left₀ (norm_nonneg _) (Q.floor _ _ _ (Q.awake _ _ (decline p) (Q.trough w j))) _
protected def price (w:H):= ⨆ n:ℕ,‖Q.Bottom w n‖^2
private lemma money (w:H): Tendsto (fun n=> ‖Q.Bottom w n‖^2) atTop (𝓝 (Q.price w)):= tendsto_atTop_ciSup (bottom_mono Q w) ⟨‖w‖^2,Set.forall_mem_range.mpr (fun _=>pow_le_pow_left₀ (norm_nonneg _) (bottom_upper Q _ w) _)⟩
protected lemma closeB (p:x∈Q.gliding w (fiss n)): dist x (Q.Bottom w n)^2 ≤ 2*(‖x‖^2-‖Q.Bottom w n‖^2):=by
 let y:=Q.Bottom w n; let m:=(1/2:ℝ) • (x+y); have ht: m∈Q.gliding w (fiss n):=by
    rw [show m= (1/2:ℝ) •x+(1/2:ℝ) • y from smul_add ..]; exact Q.glide_con _ _ p (Q.trough w n) (by norm_num) (by norm_num) (by norm_num)
 have he:=pow_le_pow_left₀ (norm_nonneg _) (Q.floor w m n ht) 2; rw [show m=(1/2:ℝ) • (x+y) from rfl,norm_smul] at he; norm_num at he; have hp:= parag x y; unfold y at hp; linarith
protected lemma boat (w:H): CauchySeq (Q.Bottom w):=by
 refine Metric.cauchySeq_iff'.mpr fun r p=>?_ ; have h:CauchySeq fun n=> ‖Q.Bottom w n‖^2:= (money Q w).cauchySeq
 obtain ⟨N,t⟩:= Metric.cauchySeq_iff'.mp h (r^2/2) (by positivity)
 refine ⟨N,fun j v=>?_ ⟩; have he:= t j v; rw [Real.dist_eq, abs_of_nonneg] at he; swap; · exact sub_nonneg.mpr (bottom_mono Q w v)
 have hi:= Q.closeB w _ _ (Q.awake _ _ (decline v) (Q.trough w j)); nlinarith only [he,hi,p,dist_nonneg (x:=Q.Bottom w j) (y:=Q.Bottom w N)] -- arguments tune
protected lemma aboard : Tendsto (Q.Bottom w) atTop (𝓝 (planeP Q.Standard w)):=by
 obtain ⟨x,hx⟩:= cauchySeq_tendsto_of_complete (Q.boat w)
 have hp:Tendsto (fun n=> ‖Q.Bottom w n‖^2) atTop (𝓝 (‖x‖^2)):= hx.norm.pow _; have hb:Tendsto (fun n=> 2*(‖x‖^2-‖Q.Bottom w n‖^2)) atTop (𝓝 0):=by rw [show (𝓝 (0:ℝ))=(𝓝 (2*(‖x‖^2-‖x‖^2))) from congrArg _ (by ring)]; exact (tendsto_const_nhds (x:=‖x‖^2) |>.sub hp).const_mul 2
 let P:= planeP (S); have he(n:ℕ): x∈ Q.gliding w (fiss n):= isClosed_closure.mem_of_tendsto hx ((eventually_ge_atTop n).mono fun j h=>Q.awake _ _ (decline h) (Q.trough w j))
 have hv (u:ℝ)(p:0<u): x∈ Q.gliding w u:=by
    obtain ⟨k,t⟩:=(falls.eventually (gt_mem_nhds p)).exists; exact Q.awake _ _ t.le (he k)
 have hQ : x∈ Q.Standard:=by
    apply Metric.tendsto_nhds.mpr; intro ε p
    obtain ⟨i,y,h⟩:= ((Metric.tendsto_nhds.mp hx (ε/2) (by positivity)).and (hb.eventually (gt_mem_nhds (show 0<(ε/2)^2 from sq_pos_of_pos (half_pos p))))).exists
    filter_upwards [(tendsto_norm_zero (E:=T)).eventually (gt_mem_nhds (half_pos (fiss_pos i)))] with r hr
    have hK: Q.U r x ∈ Q.gliding w (fiss i) := Q.serves _ r _ (by linarith [show ‖r‖< fiss i/2 from hr]) (hv (fiss i/2) (half_pos (fiss_pos i)))
    let K:=Q.U r x; let X':=Q.Bottom w i; have he:= Q.closeB w K i hK; rw [show ‖K‖=‖x‖ from Q.keep ..] at he
    apply lt_of_le_of_lt (dist_triangle K X' x); change _ + dist X' x < _; have hz:dist K X'<ε/2:= (sq_lt_sq₀ dist_nonneg (by positivity)).1 (he.trans_lt h); linarith only [hz,(show dist X' x < ε/2 from y)]
 have hp (u:ℝ)(b:0<u) : dist (P x) (P w) ≤ u:=by
    have hp : P w∈ Q.Standard:= through w; let H':T→H:= fun t=> Q.U t (P w)
    have he: Tendsto H' (𝓝 0) (𝓝 (P w)):= hp
    obtain ⟨δ,v,g⟩:= Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp he u b)
    let C:=Set.preimage P (closedBall (P w) u)
    apply closure_minimal (t:=C) ?_ (isClosed_closedBall.preimage P.continuous) (hv _ v)
    intro z u'; change Q.Gem w δ z at u'; induction u' with
    | glide t p=>
        change dist _ _ ≤u; have ht : dist (H' t) (P w)<u:= g (mem_ball.mpr (by simpa using p))
        exact (le_of_eq (congrArg (fun x:H=>dist x (P w)) (DFunLike.congr_fun (Q.hot_keep t).eq w))).trans ht.le
    | mount ux uy a b p q v ih ig=>
        letI := IsScalarTower.restrictScalars ℝ ℂ H.space; exact ((convex_closedBall (P w) u).linear_preimage (P.restrictScalars ℝ).toLinearMap) ih ig p q v
 have h: P x=P w:= dist_eq_zero.mp (le_antisymm (le_of_forall_gt_imp_ge_of_dense hp) dist_nonneg) -- name
 rw [show P x =x from inlet hQ] at h; change Tendsto _ _ (𝓝 (P w)); rw [←h]; exact hx
-- Sufficient procedure: per x approximate by finite Gem. public link.
lemma immersion (p:0<u): planeP Q.Standard w∈ Q.gliding w u := by
 refine isClosed_closure.mem_of_tendsto (Q.aboard w) ((falls.eventually (gt_mem_nhds p)).mono fun i hp=> ?_); exact Q.awake _ _ hp.le (Q.trough w i)
theorem atGate (p:0<u)(ε:ℝ)(u':0<ε):∃ x,Q.Gem w u x∧ ‖planeP Q.Standard w - x‖<ε:=by
 obtain ⟨g,q,h⟩:= Metric.mem_closure_iff.mp (immersion Q w u p) ε u'; exact ⟨g,q,by simpa [dist_eq_norm] using h⟩
theorem currency : Q.price w=‖planeP Q.Standard w‖^2:= tendsto_nhds_unique (money Q w) ((Q.aboard w).norm.pow _)
#print axioms currency
end Willow
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
