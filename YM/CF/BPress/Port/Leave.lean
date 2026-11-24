import YM.CF.BPress.Port.Bells
/-!
Exact indicators & proof of trunk implication eq:B-trunc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(T:Sheet.Atlas)(p:Weave.Budget)(κ y:ℝ)
-- splice hard original everywhere on S. market-level severity locality and test equality
abbrev pick (x: Offers X):= chosen X κ y ((heart X).symm x)
def issueT (S: Branch.Seal X.Hcols)(w:Fills X)(h:Offers X) : Offers X := fun i=> if i∈ S then h i else rose B.D y (w i)
def Aback (v:Offers X): Bills X E:=(heart X).symm v
def checked (i:X.Hcols)(w:Market B.D):Prop:=∃ j:Hub B.D, κ*temp y < chord (w j) (bMag B.D y j)
lemma pick_eq (w:Offers X)(i:X.Hcols): i∈pick X κ y w↔ checked X κ y i (w i):= marksev ..
lemma pick_meas (S: Branch.Seal X.Hcols): MeasurableSet {U : Offers X|S=pick X κ y U}:=by
 have h:Set.preimage (heart X).symm {U|S=chosen X κ y U}={U : Offers X|S=pick X κ y U}:=rfl; rw [←h]; apply (heart X).symm.measurable; rw [show {U|S=chosen X κ y U}= ⋂ i:X.Hcols, if i∈ S then {U|i∈chosen X κ y U} else {U|i∈chosen X κ y U}ᶜ from ?_]; swap
 · ext1 U; simp only [Set.mem_setOf_eq,Set.mem_iInter,Finset.ext_iff]; refine forall_congr' fun i=>?_ ; by_cases p:i∈ S <;> simp [p]
 exact MeasurableSet.iInter fun i=> by split; exact choose_meas ..; exact (choose_meas ..).compl
@[fun_prop] lemma issue_meas (S:Seal X.Hcols): Measurable (uncurry (issueT X y S)):= measurable_pi_lambda _ fun i=> by dsimp only [uncurry,issueT]; split_ifs <;> first| exact (measurable_pi_apply i).comp measurable_snd| exact (rose_meas B.D y).comp ((measurable_pi_apply i).comp measurable_fst)

structure Afford (D:ℕ)(κ y:ℝ): Prop where
 young : 0<y
 kap : 0<κ
 logT : κ*temp y< T.δ
 welt : T.C*(κ*temp y) < J.radius
 swungH : g y * (faith D*(p.fore y D*truncv y))<J.radius
 backward : faith D*(p.flank y D *(T.C*κ*drift y)) ≤ truncv y
lemma afford (D:ℕ)(u:LocalRatio J)(q:0<κ) : ∀ᶠ i in atTop, Afford J T p D κ i := by
 have he : NPL (fun i=>g i * (faith D*(p.fore i D*truncv i))):=by
   convert ((p.buy_for D).times (npl_drift_g 2 1 zero_lt_one)).const_mul (faith D) using 1; ext i; unfold truncv; rw [Real.rpow_two,Real.rpow_one]; ring
 have hp:=(((p.buy_fla D).mul (PL.const (T.C*κ))).times (npl_drift 1 zero_lt_one)).const_mul (faith D)
 filter_upwards [(npl_temp.const_mul κ).drop.eventually (gt_mem_nhds T.size), ((npl_temp.const_mul κ).const_mul T.C).drop.eventually (gt_mem_nhds u.patch), he.drop.eventually (gt_mem_nhds u.patch), hp.drop.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ)] with y a b c e p'; refine ⟨p',q,a,b,c,?_⟩; unfold truncv; have hf:=drift_pos y; change faith D * (p.flank y D * (T.C*κ) * _)≤ 1 at e; rw [Real.rpow_one] at e; field_simp at e; nlinarith only [mul_le_mul_of_nonneg_right e hf.le]
variable {X J T κ y p}
namespace Afford
variable (u:LocalRatio J)(P: Afford J T p B.D κ y)
include P u
lemma cover (x:Offers X)(i:X.Hcols)(v:i∉pick X κ y x) : x i∈ pullCover B.D J y:=by
 let K:=(heart X).symm x; let g:=softAl X κ y K T; let f:=fun j:Hub B.D=>g (i,j); have he (j:Hub B.D):= unsevere κ y T P.logT K (i:=(i,j)) v; have hv:x i= rosin B.D y f:= funext fun j=> (he j).1; rw [hv]; refine rosin_cover B.D J y u (fun j _=>?_ ); exact Metric.mem_ball.mpr (by rw [dist_zero_right]; exact ((he j).2.trans_lt P.welt))
variable {F:Fare X}(S:Seal X.Hcols)(e:Summer X F p.upper (p.low y) (p.reach y) (p.chunks y))(h:Whole X S (F S) 1)(v:RaySpace X)
include e in
lemma outward (f:∀ i, ‖offer X v i‖ ≤ truncv y) :∀ i,wjson (F S) (offer X v) i∈mouthP B.D J y:=by -- include e
 intro i j _; apply Metric.mem_ball.mpr; rw [dist_zero_right]; apply lt_of_le_of_lt _ P.swungH; have hp:0 ≤ truncv y:= zero_le_one.trans (trunc_pos _); refine le_trans (c_bound _ _ j) ?_; rw [norm_smul, Real.norm_of_nonneg (g_pos P.young).le]; exact mul_le_mul_of_nonneg_left (hue_small p F _ _ e S (offer X v) i hp (fun i _=>f i)) (g_pos P.young).le -- tune E implicit
lemma log_sect (S:Seal X.Hcols)(v:RaySpace X)(w:Offers X)(HE:S=pick X κ y (issueT X y S (offer X v) w))(hm:∀ i∉S,offer X v i∈mouthP B.D J y)(i:X.Air) (g:i.1∉ S): softAl X κ y ((heart X).symm (issueT X y S (offer X v) w)) T i= (hew B.D y (offer X v i.1)) i.2:=by
 let K:=(heart X).symm (issueT X y S (offer X v) w); obtain ⟨a,d⟩:= unsevere κ y T P.logT K (i:=i) (by rw [← show S=chosen X κ y K from HE]; exact g); -- tune rw HE depends
 apply u.inject (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact d.trans_lt P.welt)) ((hm i.1 g) i.2 (Set.mem_univ _)); apply mul_left_cancel (a:=magnetH y i.2.2); rw [← show K i=_ from a]; change (issueT X y S _ _) i.1 i.2 = _; rw [issueT,if_neg g]; rfl
lemma thread (v:RaySpace X)(i:X.Air): hew B.D y (offer X v i.1) i.2=g y • lead X v i:=by ext j; rw [hew, colorL]; change g y* (offer X v i.1 (i.2,j))=_; rw [show offer X v i.1 (i.2,j)=_ from offer_hit X v (i,j)]; rfl
-- integrate even if proof irrelevant P needed? omit P u for thread.
include e h
-- while inverse cost proof avoids conditioning: arbitrary v post map; bound preincluded only on accepted fields and charts. w=F v. mask^c propagation.
lemma homebound (w:Offers X)(Z:RaySpace X)(z:Z= F S v)(a:S=pick X κ y (issueT X y S (offer X Z) w))(c:∀ i∉ S,offer X Z i∈ mouthP B.D J y)(t:∀ i∈S, ‖offer X Z i‖≤truncv y) : ∀ i:X.Hcols, ‖offer X v i‖ ≤ truncv y := by
 let K:= (heart X).symm (issueT X y S (offer X Z) w); let U:= T.C*κ*drift y; have hp:=T.span; have hv:=drift_pos y; have hu:0≤ U:=by unfold U; positivity [P.kap]
 let V:= keepOnly X Sᶜ Z; have H: 0≤p.flank y B.D:= by unfold Weave.Budget.flank Weave.Budget.choose_c grainSelect; positivity [e.hp,grain_nn B.D (p.chunks y * p.reach y)]
 let F':= sun X F p.upper S; have hk: F' V= keepOnly X Sᶜ v:=by
    unfold V; rw [z,←h.complement v]; exact congrArg (fun A:BEnd X=>A (keepOnly X Sᶜ v)) (e.inverse S).1
 intro i; by_cases p':i∈S; · rw [← whole_he (F S) h v i p', ← z]; exact t i p'
 rw [← show offer X (keepOnly X Sᶜ v) i=_ from (ray_part X Sᶜ v i).trans (if_pos (mem_compl.mpr p'))] -- tune branches opposite via lemma rewrite standalone
 apply le_trans _ P.backward; rw [← hk]; refine ray_mobile F' V i U _ (e.sun_cap S) (fun j p l e1=>?_ ) hu H; by_cases k:l.1.1∈ S; · unfold V; simpa [keepOnly,k]
 have hG:=g_pos P.young; let i:=l.1; let A:=lead X Z i; have he:‖g y • A‖≤T.C*(κ*temp y):=by unfold A; rw [← P.thread u]; rw [← P.log_sect u S Z w a c i k]; exact (unsevere κ y T P.logT K (i:=l.1) (by rw [← show S=chosen X κ y K from a]; exact k)).2 -- tune order
 rw [temp_eq, norm_smul, Real.norm_of_nonneg hG.le] at he
 have hx: ‖A‖ ≤ U:=by unfold U; apply le_of_mul_le_mul_left _ hG; nlinarith only [he]
 apply le_trans _ ((point_cost A l.2).trans hx); exact Eq.le (congrArg abs (show V l=A l.2 from if_pos (Finset.mem_compl.mpr k))) -- tune `using g_pos` lemma calc
end Afford
end YM.CF.BPress.Port
