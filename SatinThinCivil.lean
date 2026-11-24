import SatinThinValance

/-! # sum scan registers. Not a second-moving-point renormalization assumption.
 From existing Trophy, Archive -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)

variable {ε dbκ dbD yQ:ℝ}{Y0:Finset (Cell n)}

variable (I:Accounts J R q p r.count.val m β v Λ ε κ dbκ dbD yQ) (g0:2*(r.count.val+1)<n.val)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)

open Regis.Head
variable {death:ℝ}
variable (Q':0 ≤ z')
variable {κ' : ℝ}
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)
abbrev lowerFocal (x:ℝ)(p n:Side) := p -- unused here
abbrev rebateB (death μ U₀:ℝ)(n:Side): Prop := (∑ i:Finset (Cell n),Real.exp (U₀-death*i.card)) ≤ Real.exp (U₀+μ*Fintype.card (Site n))
variable (g:0<β)(d:0≤ κ')(l:0≤ C)
include B P L D I d g j wH uH Q'
include u h1 h2 a he g0 l
lemma harvest_civil {μ:ℝ}(Φ:∀ x, rebateB death μ x n) (pH:4*descendCost J β κ' z'*(r.count.val:ℝ)^4 ≤ yQ) (hω:4*descendCost J β κ' z'*(coldBill (hallBill m):ℕ)+death ≤ dbD) (Hx:GaugeInvariant φ) (v':∀ A:Support c, ∀ S:Finset (Cell n), ShelfScene B P p r m β v ε (Q+z'*(trap r m A+trap_s m S)) A S t φ W): (∫ U:Config G n,twice_rich Z q p β κ dbκ ε U*Real.exp (t*φ U)∂prior G n) ≤ Real.exp (Roof J β n H + rentRoom r R q m p β v η C S Λ (descendCost J β κ' z') + Q + plumeCost B P W t + trend*b₂^2*t^2 + Real.log 2*(Fintype.card (Site c):ℝ)+ μ*(Fintype.card (Site n):ℝ)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T; let D':= descendCost J β κ' z'
 let X:= fun U:Config G n=> twice_rich Z q p β κ dbκ ε U*Real.exp (t*φ U); change (∫ U,X U∂_) ≤ _; have H1:Envelope X:= (income_burs B).mul (expEnv u _); have h':= twice_gauge (ξ:=dbκ) (ε:=ε) (β:=β) (κ:=κ) (p:=p) (n:=n) B; rw [T.pack _ (H1.integrable _) (fun k y U=> by unfold X; rw [Hx,h' k])]; let U0:= Roof J β n H+rentRoom r R q m p β v η C S Λ D' + Q + plumeCost B P W t + trend*b₂^2*t^2; let F'(A:Support c)(Y0:Finset (Cell n)):= scanWave Z q p A Y0 T β κ dbκ ε t φ
 have hp(A:Support c)(Y0:Finset (Cell n)) : (∫ x,F' A Y0 x ∂T.order G)≤ Real.exp (U0-death*Y0.card) := by
    let p':=(qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩); have hg:= shelfPrize (W:=W) (Q:=Q) (b₂:=b₂) (t:=t) (K':=p') B P L D I Q' j wH uH g d A Y0 h pH hω; apply le_trans _ hg.2; exact sourcedDebt B P L D I g0 u a h1 h2 A hg.1 g l (cloak_growth (subset_univ F)) (v' A Y0)
 rw [show (fun x:T.Slice G=> X (T.drape x))=(fun x=>∑ i: Support c,∑ j:Finset (Cell n),F' i j x) from ?_]
 swap
 · funext x; let N:= T.drape x; let i:=broken r ε N; let j:=misdemean p.threshold N; let H:= twice_rich Z q p β κ dbκ ε N; have hφ(A:Support c)(B:Finset (Cell n)): F' A B x=(if (i,j)=(A,B) then X N else 0):=by
      unfold F' scanWave facePlay; split <;> rename_i h; · rw [if_pos (Prod.ext h.1 h.2)]
      rw [if_neg (by intro k; exact h ⟨congrArg Prod.fst k,congrArg Prod.snd k⟩),zero_mul]
   simp_rw [hφ]; rw [← Fintype.sum_prod_type (fun b=> if (i,j)=b then X N else 0)]; simp [N] -- nested
 rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ (fun j _=> (env_scanWave B u i t).integrable _)
 have hu:∀ i,(∫ x,(∑ j:Finset (Cell n),F' i j x)∂T.order G)≤ Real.exp (U0+μ*Fintype.card (Site n)):=by
    intro i; rw [integral_finsetSum]; exact (sum_le_sum (fun j _=>hp i j)).trans (Φ _); exact fun j _=> (env_scanWave B u i t).integrable _
 refine (sum_le_sum (fun i _=>hu i)).trans_eq (?_); rw [show Roof _ _ _ _ + _ + _ + _+_+_+_= U0+μ* (Fintype.card (Site n):ℝ) + Real.log 2* (Fintype.card (Site c):ℝ) from (by unfold U0; ring)]; simp only [sum_const,card_univ,nsmul_eq_mul, Real.exp_add (U0+_)] -- tune same support
 rw [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num)]; unfold Support; simp only [Fintype.card_finset]; push_cast; ring
omit B P L D I d g j wH uH Q' u h1 h2 a he g0 l

abbrev twice_angled (Z:PathData G)(q:Clip)(p:BudgetPoint) (β κ k ε:ℝ)(U:Config G n):ℝ:= Real.exp (-(Z.inChannels q p β U)+κ*(misdemean p.threshold U).card+k*(misdemean ε U).card)
include B in
lemma env_twice : Envelope (twice_angled Z q p β κ dbκ ε (n:=n)):= (((PathData.channels_env B p β).neg.add (conduct ..)).add (conduct ..)).exp
private lemma on_wind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))

include B u in
lemma forCivil (ξ:ℝ)(t:ℝ)(hh:∀ d: Signed,(∫ x:Config G n, twice_rich Z q p β κ dbκ ε x *Real.exp (t*φ (pull d 0 x)) ∂prior G n) ≤ ξ) : (∫ x:Config G n, twice_angled Z q p β κ dbκ ε x * Real.exp (t*φ x) ∂prior G n) ≤ ξ := by
 let M:ℝ:=Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 let w:= M⁻¹; let S:=twice_angled Z q p β κ dbκ ε (n:=n); let F (s: Signed) (x:Config G n):= twice_rich Z q p β κ dbκ ε x * Real.exp (t*φ (pull s⁻¹ 0 x)); let X:=prior G n; let Φ(s:Signed)(x:Config G n ):=F s (pull s 0 x)
 have hw:∑ _:Signed,w=1:= by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 have E(i:Signed) : Envelope (F i):=(income_burs B).mul ((fun p:Envelope (fun x:Config G n=> φ (pull i⁻¹ 0 x) )=>expEnv p t) ⟨u.meas.comp (by apply (prior_pull _ _).measurable), u.cost.choose,fun _=> u.cost.choose_spec _⟩); let G'(x: Config G n):= ∑ i: Signed,w*Φ i x
 have he(i:Signed): Integrable (fun x=>w*Φ i x) X:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable ((E i).integrable X)).const_mul w
 have hf:Integrable G' X:= integrable_finsetSum _ (fun i _=> he i)
 refine le_trans (integral_mono (show Integrable _ _ from ((env_twice (dbκ:=dbκ) (ε:=ε) (n:=n) (p:=p) (κ:=κ) (β:=β) B).mul (expEnv u t)).integrable X) hf ?_) ?_
 · intro x; let f(s:Signed):= Z.principal q p β (pull s 0 x); let g:= κ*(misdemean p.threshold x).card; let g':=dbκ*(misdemean ε x).card; let e(s:Signed):= -f s+g+g' + t*φ x; have ht(i:Signed): Φ i x=Real.exp (e i ):=by unfold Φ F twice_rich e; rw [on_wind,on_wind, pull_pull]; simp [affine,Real.exp_add]; ring -- maybe
   unfold G'; simp_rw [ht]; let tt:= (convexOn_exp.map_sum_le (w:=fun _ : Signed=>w) (fun i _=> inv_nonneg.mpr hM.le) hw (fun s _ => Set.mem_univ (e s)))
   rw [←Real.exp_add]
   change Real.exp _ ≤ ∑ i,w • _; apply tt.trans'; refine Eq.le (congrArg Real.exp ?_); unfold e; simp only [smul_eq_mul,mul_add,sum_add_distrib, mul_neg,sum_neg_distrib, ← mul_sum, sum_const, card_univ,nsmul_eq_mul]; change -(w*∑ s,f s)+ g + g' + t*φ x= -(w*∑ s,f s)+ w * (M*g) + w*(M*g') + w * (t*(M*φ x)); rw [mul_left_comm t M, inv_mul_cancel_left₀ hM.ne', inv_mul_cancel_left₀ hM.ne', inv_mul_cancel_left₀ hM.ne'] -- order
 unfold G'; rw [integral_finsetSum _ (fun i _=> he i)] -- signature lemma
 have h(i:Signed):(∫ x:Config G n, w*Φ i x∂X)=w*∫ x,F i x∂X:=by rw [integral_const_mul]; refine congrArg (w * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂X from (by have ht:= integral_map (μ:=prior G n) (f:=F i) t.measurable.aemeasurable (show AEStronglyMeasurable (F i) _ from (E i).meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht))
 simp_rw [h]; refine (Finset.sum_le_sum (g:=fun _=> w*ξ) (fun i _=>?_)).trans_eq ?_; · exact mul_le_mul_of_nonneg_left (hh i⁻¹) (by unfold w; positivity)
 rw [← Finset.sum_mul,hw,one_mul]
end YM.Gleam
#print axioms YM.Gleam.harvest_civil
#print axioms YM.Gleam.forCivil
