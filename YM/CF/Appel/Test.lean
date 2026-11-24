import YM.CF.Appel.Grace
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open Set Topology
open SectorNext.Remainder.Affine SectorNext.Remainder.Scales
abbrev pressG(G:Gauge)(P: RG.Patch)(v x:ℝ):ℝ:=activation G 0 0 v*fiery G x P.L
abbrev aimC(x:ℝ):ℝ:=(↑(radiusB x))^10
def hymn(G:Gauge)(L:Side)(x:ℝ):ℝ:= aimC x*(fiery G x L)^2
lemma bless {D Z:ℝ}(G:Gauge)(L:Side)(hD:0 ≤ D)(hZ:0 ≤ Z)(hm:0<temp x)(hp:temp x ≤ 2*fiery G x L): D*(tideF Z x)^2 ≤ (4*D*Z^2)*hymn G L x:=by
 have he:0 ≤ blockF x:=by unfold blockF; positivity
 refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ tideF Z x from mul_nonneg hZ (mul_nonneg he hm.le)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp he) hZ) 2) hD).trans_eq ?_; unfold blockF hymn aimC; ring
lemma crush (G:Gauge)(L:Side): Tendsto (fun x=> aimC x*fiery G x L) atTop (𝓝 0):=by
 have he:= tally_g G L 10 1; have hx:= year G L
 apply squeeze_zero' (Eventually.of_forall fun x=>mul_nonneg (by unfold aimC; positivity) (temp_nonneg _)) ?_ he
 refine Eventually.of_forall fun x=>?_ ; change aimC x*fiery G x L ≤ _
 apply (mul_le_mul_of_nonneg_right (show aimC x ≤ b x^10 from pow_le_pow_left₀ (by positivity) (by unfold b; linarith) _) (show 0≤fiery G x L from temp_nonneg _)).trans_eq; rw [fi]; ring
lemma news (G:Gauge)(L:Side)(d v:ℝ)(hd:0 ≤ d)(hv:0<v):∀ᶠ x in atTop,d*fiery G x L*Real.exp (-v*radiusB x) ≤ 2*hymn G L x:=by
 filter_upwards [smallF (n:=1) hv d,Work.E01.radiusB_tendsto.eventually_ge_atTop 1,Work.E07.temp_coarse_le G L] with x hx ht he
 have hp :0 ≤ fiery G x L:=temp_nonneg _; have hk:=one_le_pow₀ (show (1:ℝ) ≤ ↑(radiusB x) from by exact_mod_cast ht) (n:=10) -- tune
 let t:=fiery G x L; change d*t*_ ≤ _
 have hy: d*Real.exp (-v*radiusB x) ≤ 2*t:=calc
    _ ≤ Real.exp (-v*Stores.till x)*d:=by rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ hd; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left (Nat.cast_le.mpr ?_) (by linarith only [hv]); unfold Stores.till; omega
    _ ≤ _ :=by rw [pow_one] at hx; exact hx.trans he
 refine le_trans (show d*t*_=(d*Real.exp (-v*radiusB x))*t from by ring).le ((mul_le_mul_of_nonneg_right hy hp).trans ?_)
 unfold hymn; change _ ≤ 2*(aimC x*t^2); rw [mul_assoc,←pow_two]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sq_nonneg _) hk) (by norm_num)
abbrev RX (x κ:ℝ):ℝ:= 2*κ
-- lemma use earlier schedules, all heights
structure MossX (n l:ℕ)(x:ℝ)(A:Stores S)(F:Forest S.ratio)(T:Tube G S)(V:Config G c)(k:S.Choices)(D d t:ℝ)(q:Chi):Prop where
 moves : Continuous (fun Y=> liftN T x V k A F q d Y l)
 still (Y:LinkArray G (Frozen A x F)): credW T A F k q d x Y l V=credW T A F k q d x 1 l V
 jumps (Y: LinkArray G (Frozen A x F)): (Offset.b T x k A F q d Y V= Rows.blame T x V k (shots S x) A F q d Y ∧ Offset.mean T x k A F q d Y V=meanLog A F T x V k q d Y)∧
    Allows n (fun y=>liftN T x (Vmove x V y) k A F q d Y l) 0 (D*t) ∧
    Allows n (bankG T A F k q d x Y l ∘ Vmove x V) 0 (D*(aimC x*t^2)) ∧
    Allows n (Dira T A F k q d x Y l ∘ Vmove x V) 0 (D*(aimC x*t^2)) ∧
    Protected n (credW T A F k q d x Y l ∘ Vmove x V) 0 D∧ Protected n (fullV T A F k q d x Y l ∘ Vmove x V) 0 (D*lamp x) ∧
    IsUnit (credW T A F k q d x Y l V).det ∧ ‖paintO (credW T A F k q d x Y l V)⁻¹‖ ≤ D -- parse
 ready: Ready T x
lemma turnsX (n l:ℕ)(D:ℝ)(hD:0<D)(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(hn:2≤n)(hl:l≤18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1))(q:Chi):∃ C:ℝ,0<C∧ ∀ᶠ x in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x →∀ (A:Stores S)(F:Forest S.ratio)(V:Config G c),sizedP G P K S T F→ A.flags=RG.flags (temp x) V → ∀ k:S.Choices,MossX n l x A F T V k C (D*fiery G x S.patch.L) (fiery G x S.patch.L) q:=by
 obtain ⟨r,d,d',v,N,C,η,y,hr,hd,hd',hv,hN,hC,hη,hy,h⟩:= Offset.prices G P K D hD q n p
 let M:=activation G n 0 d*N; have hM:0≤M:=mul_nonneg (zero_le_one.trans (activation_one G n 0 hd)) hN.le
 obtain ⟨a,u,hu,H⟩:=shipped K P p n l hn hl W; let E:=4*a*u^2
 obtain ⟨θ,B,m,v',Q,L,hθ,hB,hm,hv',hQ,hL⟩:=jumpW K P n l hn hl p W
 let Z:= max L 0; let R:=2+ 2^n*Q*E; let F:=max (max (max R (2^n*Z*R)) Z) (2*L*L); let A₀:=max (M+E) F; let A:=max 1 A₀; have ha:A₀≤A:=le_max_right ..; have hY:F≤A:=(le_max_right ..).trans ha
 have he:Tendsto (fun x:ℝ=> 2*(D*fiery G x P.L)) atTop (𝓝 0):=by
    have he:= ((tally_g G P.L 0 1).const_mul D).const_mul 2; rw [mul_zero,mul_zero] at he; refine he.congr fun x=>?_; rw [fi]; ring
 refine ⟨A,zero_lt_one.trans_le (le_max_left ..),?_⟩
 filter_upwards [h,H,hL,news G P.L M v hM hv, (crush G P.L).eventually (ge_mem_nhds zero_lt_one), he.eventually (gt_mem_nhds (first_pos G)),monitors G P.L] with x h H hL hX he' hr' ht c f S T hT A' F' V hp he k
 obtain ⟨hα,hβ,hγ,Hx⟩:= hL; obtain ⟨hρ,Hk⟩:= Hx S T A' F' V hT he hp k
 let B':=fiery G x S.patch.L; have hB':0<B':=pos_of_mul_pos_right (ht.1.trans_le (by unfold B'; rw [hT.got]; exact ht.2.2)) (by norm_num) -- check order
 obtain ⟨hN',hZ⟩:=h.2 S T hT.got hT.size hT.funds.1 A' F' V he k; let H':=H.2.2.2 S T A' F' hT hp V he k q 0 1
 rw [← hT.got] at hr' he' ht hX
 refine ⟨mastV K hT.funds.1 H'.1 hl (mul_pos hD hB') hr' hZ,fun Y=>?_,fun Y=> ?_,H'.1⟩
 · unfold credW layX majorX; rw [looser (Z:=1) H'.1 hl]
 obtain ⟨hPx,hM⟩:= Hk q (D*B') Y; obtain ⟨h1,h2,h3,h4,h5,h6⟩:= cigar hZ hN.le ht.1 hd K hT he hp H hρ hPx; let F':= aimC x*B'^2
 have he := bless (D:=a) G S.patch.L H.2.2.1.le hu.le ht.1 ht.2.2 -- tune
 let e:= a*(tideF u x)^2; change e≤ E* F' at he
 have hP: F' ≤ B':=by unfold F'; rw [pow_two,← mul_assoc]; exact mul_le_of_le_one_left hB'.le he'
 have hD': M*B'+e  ≤  A*B':= ((add_le_add_right (he.trans (mul_le_mul_of_nonneg_left hP (by unfold E; exact mul_nonneg (mul_nonneg (by norm_num) H.2.2.1.le) (sq_nonneg _)))) (M*B')).trans ((add_mul M E B').symm.le.trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans ha) hB'.le)))
 let x':=M*B'*Real.exp (-v*radiusB x)+2^n*Q*e; have hx:x' ≤ R*F':= (add_le_add hX (mul_le_mul_of_nonneg_left he (by positivity))).trans_eq (by unfold R F' hymn at *; ring)
 have hp : Z≤A:=(le_max_right ..).trans ((le_max_left ..).trans hY)
 have ht':0 ≤ F':=by unfold F' aimC; positivity
 have hf:L≤A:=(le_max_left ..).trans hp
 have hv: x' ≤ A*F':=hx.trans (mul_le_mul_of_nonneg_right (((le_max_left ..).trans (le_max_left ..)).trans ((le_max_left ..).trans hY)) ht')
 have h₁:0≤Z:=le_max_right ..
 have h₂:2^n*L*x'≤A*F':=by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show L≤Z from le_max_left ..) (by positivity)) h3.nonneg).trans
    apply (mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2^n*Z)).trans; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right (((le_max_right ..).trans (le_max_left ..)).trans ((le_max_left ..).trans hY)) ht'
 exact ⟨h1,h2.mono hD',h3.mono hv,h4.mono h₂,h5.mono hf,h6.mono (mul_le_mul_of_nonneg_right hf (mul_nonneg (by positivity) (temp_nonneg _))), hM.vertex,hM.safe.trans ((le_max_right ..).trans hY)⟩
end YM.CF.Appel
