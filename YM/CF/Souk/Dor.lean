import YM.CF.Souk.Pure
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort Finset
open Next.SectorChange PatchReads Next.SectorChange.Wisps
variable {q:Clip}{p:ChartRatio G}{k:S.Choices}{d γ ν Λ α:ℝ}{R:PathData G}
variable {a:ℝ}
lemma lamplighter (p:R.Bounds q s C a)(U:Config G c)(d:ℝ)(i:ℕ):
 secondTerm q R U-secondTerm q (safeD R i) U= Patch.average fun t:Signed=>uncut (rod R i) (pull t 0 U):=by
 unfold secondTerm Patch.average; rw [← mul_sub,←Finset.sum_sub_distrib]; congrm _ * ?_
 refine Finset.sum_congr rfl fun t _ =>?_ ; unfold quadratic uncut; simp_rw [Fintype.sum_prod_type, Finset.sum_add_distrib,uncut_pair p, ← Finset.sum_sub_distrib]; simp_rw [Finset.sum_sub_distrib,add_sub_add_left_eq_sub]; rfl
lemma cap_f {a:ℝ}(p:R.Bounds q s C a)(h:Uniform.PaintSupply G 2 D)(hv:2 ≤c.val)(t:ℝ)(i:ℕ)(v:Fin 2→Primary c G) :
 let U(x:Mast G c):= draft t R q (tint G _ x)-draft t (safeD R i) q (tint G _ x)
 ContDiffAt ℝ ω U 0∧|Uniform.entry U 0 v|  ≤ (|t| *Stationary.gramCost G C+a)*(tollE s i*stip G 1 2 D s):=by
 intro U; let K(y:Mast G c):=represent (tint G _ y); let X(s:Signed)(y:Mast G c):=uncut (rod R i) (pull s 0 (K y)); let M(s:Signed)(y:Mast G c):= uncut (haste i R.loop) (pull s 0 (K y)); let A(s:Signed)(y:Mast G c):= t • X s y + M s y
 have hU: U= fun y=>Patch.average fun k:Signed=>A k y:=by
    funext y; unfold U A M X K; unfold draft; let Z:=represent (tint G _ y)
    rw [add_sub_add_comm,← mul_sub, lamplighter (a:=a) p Z t i]; unfold Precision.loop uncut Patch.average
    rw [sum_add_distrib, ← mul_sub, ← Finset.sum_sub_distrib]; simp_rw [uncut_high _ p.width p.two,← Finset.sum_sub_distrib,smul_eq_mul,←mul_sum]; unfold safeD Vol.batch; ring
 -- rewrite routines using facadeX defeq?
 have ht(t:Signed):= lead (rod R i) (hurry p i) p.width hv h t v; have hx(t:Signed):= lead (haste i R.loop) (pastA _ p.width p.two i) p.width hv h t v
 have hp(u):ContDiffAt ℝ ω (A u) 0:= ((ht u).1.const_smul t).add (hx u).1; rw [hU]; refine ⟨(ContDiffAt.sum (s:=Finset.univ) fun i _=> hp i).const_smul ((Fintype.card Signed:ℝ)⁻¹), winds_C _ _ (fun i=>(hp i).of_le le_top) _ ?_⟩
 intro u; let E:= Uniform.entry (A u) 0 v; have he : E=t* Uniform.entry (X u) 0 v + Uniform.entry (M u) 0 v:=by
    rw [← hiccup (X u) t v ((ht u).1.of_le le_top)]; unfold E A Uniform.entry; rw [show (fun y=>_ • _+M u y)=t • X u+ M u from rfl]; erw [iteratedFDeriv_add_apply (show ContDiffAt ℝ (2:ℕ) (t • X u) 0 from ((ht u).1.const_smul t).of_le le_top) (show ContDiffAt ℝ (2:ℕ) (M u) 0 from (hx u).1.of_le le_top)]; rfl -- tune
 change |E| ≤_; rw [he]; apply (abs_add_le ..).trans; rw [abs_mul]; exact (add_le_add (mul_le_mul_of_nonneg_left (ht u).2 (abs_nonneg _)) (hx u).2).trans_eq (by ring)
lemma hive(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(hG:G.Simple)(l:ℕ)(hn:1 ≤ l)(hl:l ≤18)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind 5) (J:ChartRatio G)(hO: LocalRatio J)(Q:ℝ):
 ∃ C:ℝ,0<C ∧∀ᶠ x in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → T.up.Bounds T.high K.top.width K.top.paths Q → sizedP G P K S T F → ∃ z, W.Service F T.high T.up z ∧ ∀ (k:S.Choices)(q:Chi)(a:ℝ)(j:Fin 2→Primary c G),
 let L(y:Mast G c):= gateY J T F x k q a l y - thermal F k T.high T.up z J (tint G _ y)
 let M:= raised G P.L ((l+52)*radiusB x)+1
 ContDiffAt ℝ 2 L 0 ∧ |Uniform.entry L 0 j| ≤ C*M*(radiusB x:ℝ)^27*temp x:=by
 obtain ⟨D,C,hD,hC,H⟩:=sieve K P p l hn hl W; obtain ⟨A,hA,H'⟩:=dale K P p l hG W; obtain ⟨N,hN,hV⟩:=wealth J hO; obtain ⟨Z,hZ⟩:=Uniform.paint_supply G 2
 let S:=K.top.width; let Y:= Q*Newt.fareX G 2 2 Z S P.L; let G':= Q* Newt.fareX G 2 2 Z (S/2) P.L
 let B:= A*Y+2*A*((A+1)*Y)+(A*G'+A*(A*G'))+(A*N+2*A*((A+1)*N)+6*C)
 have hs':0<S:=K.top.width_pos; have he:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 have hp:(∀ᶠ x in atTop, D* lamp x^3 ≤ 1/2):= by
    exact ((show Tendsto (fun x:ℝ=>D*lamp x^3) atTop (𝓝 (0:ℝ)) from by simpa using ((lamp_s.pow 3).const_mul D)).eventually (ge_mem_nhds (by norm_num : (0:ℝ)< 1/2))) -- tune meta
 refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right ..),?_⟩
 filter_upwards [H,H', Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, eventually_gt_atTop (0:ℝ), he.eventually (ge_mem_nhds zero_lt_one), Newt.smallF (n:=3) (half_pos hs') 1, hp, Hors.raises G P.L l 0 A hA.le] with x hH hY hB hx hS he hh ha c f T U F h hU hG
 obtain ⟨z,hz,hk⟩:= hH T U F h hG
 refine ⟨z,hz,fun k q b i=>?_⟩
 intro f R; let t:= temp x; let X:= lamp x; have ht:0<t:= Work.E09.temp_pos hx; let D':=A*chit G P K x l*t^(l+2); obtain ⟨hK,hV'⟩:=hk k q b
 have hR:1 ≤ R:=le_add_of_nonneg_left (by unfold raised; positivity); have hE:t^3≤ X^3:=pow_le_pow_left₀ ht.le (le_mul_of_one_le_left ht.le (one_le_pow₀ (by exact_mod_cast (show 1 ≤ radiusB x by omega)))) 3
 have hr:0 ≤ chit G P K x l:=by unfold chit raised; positivity
 have hu: D' ≤ A*R*X^3:=by
    unfold D'; apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hA.le; unfold R chit raised; dsimp only [touchH]; gcongr<;>omega -- tune
    · exact (pow_le_pow_of_le_one ht.le hS (by omega)).trans hE
    · exact pow_nonneg ht.le _
    positivity
 have hM : tollE K.top.width (Stores.till x) ≤ X^3 := (by simpa only [mul_one] using he : tollE K.top.width (Stores.till x) ≤ t^3) |>.trans hE
 have hv:D' ≤ 1:=le_trans (mul_le_mul_of_nonneg_left (pow_le_of_le_one ht.le hS (by omega)) (show 0≤ A*chit G P K x l from mul_nonneg hA.le hr)) (le_trans (le_of_eq (by ring)) ha)
 obtain ⟨hg,hP⟩:=tale (T:=U) k q b t J hU hZ (hV T F) hN.le (hY T U F h hG z hz k) hA.le (show 0≤D' from by unfold D'; positivity) hv hV' hK hh ((far_H W h hz k t ht.le hS).2.1.of_le (by norm_num)) i
 let L(y:Mast G c):= f (t•y); have heL:ContDiffAt ℝ 2 L 0:=hg; have hv:ContDiffAt ℝ 2 f 0:=by
    let U'(y:Mast G c):= t⁻¹ • y; have he :U' 0=0:=smul_zero _; apply ((he.symm ▸ heL: ContDiffAt ℝ 2 L (U' 0)).comp (f:=U') _ (contDiffAt_id.const_smul _)).congr_of_eventuallyEq; filter_upwards with i; exact (congr_arg f (smul_inv_smul₀ ht.ne' i)).symm
 have hm:0 ≤ Q:=(tsum_nonneg hU.two.1).trans hU.two.2.2; have hr:0≤Y:= by unfold Y; exact mul_nonneg hm (mul_nonneg (Uniform.atomCost_nn hZ hs' _) (Uniform.count_pos (half_pos (Uniform.width_positive hs' 2 P.L))).le)
 let M:=Newt.fareX G 2 2 Z (S/2) P.L; have heM:0 ≤ M:= mul_nonneg (Uniform.atomCost_nn hZ (half_pos hs') _) (Uniform.count_pos (half_pos (Uniform.width_positive (half_pos hs') 2 P.L))).le
 have hl: |Uniform.entry L 0 i| ≤ B*R*X^3:=by
    rw [h.got] at hP; apply hP.trans; have h: A>0:=by assumption -- tune
    have hp:tollE _ _*Q*M ≤ R*X^3*Q*M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM.trans (le_mul_of_one_le_left (by positivity) hR)) hm) heM -- tune
    let V:= X^3; let W:=A*R*V; change D'* Y+_+_+_ ≤ _
    calc
       _ ≤ (W*Y+2*W*((A+1)*Y)+(A*(R*V*Q*M)+A*(A*(R*V*Q*M))))+(W*N+2*W*((A+1)*N)+6*(C*R*V)):=by gcongr <;> assumption
       _ = _ := by unfold B W G' Y M V X; ring
 refine ⟨hv,?_⟩; unfold L at hl; rw [entry_scale f t i 0 (show ContDiffAt ℝ (2:ℕ) f (t•0) from by rw [smul_zero]; simpa using hv),smul_zero,smul_eq_mul,abs_mul,abs_of_pos (pow_pos ht _)] at hl
 apply le_of_mul_le_mul_left _ (pow_pos ht 2) -- tune
 apply hl.trans; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left B 1) (by linarith only [hR])) (by positivity)); exact le_of_eq (by unfold t X lamp; ring)
end YM.CF.Souk
