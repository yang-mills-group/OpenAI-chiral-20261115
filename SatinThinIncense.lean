import SatinThinPark
import SatinThinOver
/-! # Calibration-stage agreement of clover valuations with local permits considering both shelves -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000
set_option maxRecDepth 2400
noncomputable section
namespace YM.Regis.Head
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix Next.SectorChange Next.SectorChange.Gaussian
open Circuit Work.G06 AnalyticBridge.VerifiedReset StressFlux Brecht Push.Local Pressure Next.Rank.Spindle
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace ContDiff Classical Matrix.Norms.Frobenius
namespace Etch
variable {n c:Side}{G:Gauge} {r: Ratio c n}{H:Bed}{I:Type*}[Fintype I]{P:BudgetPoint}{q:Clip}{m:ℕ}{v η C S x k ρ β:ℝ}{Z:PathData G}{T:Support c}{S₀:Support n}{V Y: Dir G n}{U:Config G n}
local notation "Θ" => G -- variable removed
lemma river_still(B:Z.Bounds q η C S)(P:Attached H Z)(f:Cell n)(p:withinMark r T S₀ m f): river q f (tiler B P V+joinery B P r T S₀ m Y)=faceCurl f (V+Y):=by rw [← river_now q B P]; ext i; rw [map_add (tiler B P)]; unfold river cup; simp [joinery,p]
-- adaptation inside_award
private lemma fare_v (R:Rules G)(v:ℝ)(m:ℕ): 0 ≤ slotError R m v:=by unfold slotError faceCutError; have h:=R.positive; have hc:=G.colorScale_pos; positivity
lemma inside_match(A:Etch G I)(B:Z.Bounds q η C S)(L:Attached H Z)(R:Rules G) (h:A.payroll ≤ m)(s:Signed){o:Site n}(g:withinCore r T S₀ (hallBill m) o)(l:TrustLogs (V+Y) U r T v)(K:0 ≤ v)(d:v ≤ R.c)(f:0<β): |A.palette x s o U - A.chalk q (x*coupling β) s o (starFeed B L r T S₀ m Y β V)| ≤ A.priceS R x v:=by
 rw [pin, chalk]; let D(i:I):=skewSlot G (A.slot i) s; let F(i:I):= slotFace (D i) o; let E(i:I):=skewSig G (A.slot i) s
 let X(i:I):= x • E i • (D i).atSite U o; let Y'(i:I):=(x*coupling β) • E i • river q (F i) (starFeed B L r T S₀ m Y β V)
 have he: ‖X-Y'‖ ≤ |x| * slotError R A.payroll v:=by
    refine (pi_norm_le_iff_of_nonneg ?_).mpr (fun i=>?_); · exact mul_nonneg (abs_nonneg _) (fare_v ..)
    have ht:= A.payroll_paid i s; have hp: withinMark r T S₀ m (F i):=g.shift (by apply le_trans (Nat.add_le_add_right (((Work.E04.slot_separation (D i) o).trans ht).trans h) (Sequest m)); unfold hallBill Sequest; omega)
    have hY: Y' i= x • E i • faceCurl (F i) (V+Y):=by unfold Y' starFeed; rw [map_smul,river_still B L _ hp]; rw [mul_smul,smul_comm (coupling β) (E i), smul_inv_smul₀ (coupling_pos f).ne']
    rw [Pi.sub_apply,hY,show X i= x • E i • (D i).atSite U o from rfl,←smul_sub,←smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,show |E i|=1 from skewSq ..,one_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg x); exact grantSlot l K d _ (g.1.shift (y:=o) (by simp [hallBill,Sequest]; omega)) ht
 rw [←Real.norm_eq_abs]; exact ((A.steady.norm_sub_le X Y').trans (mul_le_mul_of_nonneg_left he A.favor.prop)).trans_eq (mul_assoc ..).symm
-- weighted sum of mellow probes (coeff real and independent of everything here)
variable (z:PlaqAxes→ℝ)
def amaryllis (G:Gauge)(x:ℝ)(h:0<x):= salix (G:=G) (fun i:PlaqAxes=> mellow G i x h) z
noncomputable def petalWorth (ρ:ℝ)(V:Config G n):ℝ:= ∑ i:PlaqAxes, z i * ‖ρ • petals V 0 i‖^2
/-- off-fleet adjusted **only** for a.e. terms in gauge-only inequalities, others will use real guard -/
noncomputable def garland (ρ:ℝ)(t:ℝ)(s: Signed)(o: Site n)(V: Config G n):ℝ:= masked t (halo 10 {(0:Site n)}) (petalWorth z ρ) (pull s o V)
lemma halo_plan (s:Signed)(x:Site n)(a:Site n)(m:ℕ) : (halo m {x}).image (turnSites s a)=halo m {affine s a x}:=by
 ext i; obtain ⟨i,rfl⟩:= (turnSites s a).surjective i; let U:=turnSites s a; have he:affine s a x=U x:=rfl; simp [halo_spec,(turnSites s a).injective.eq_iff, (show affine s a x=(turnSites s a) x from rfl)]
lemma garland_gauge(t:Signed)(o:Site n) : GaugeInvariant (garland z x v t o (G:=G)) :=by -- bind
 apply invariant_pull; intro k U; unfold masked; let W:=halo 10 {(0: Site n)}; have ht: Healthy v W (gauge k U) ↔ Healthy v W U:=by simp [Healthy]
 unfold Set.indicator; split <;> rename_i h
 · rw [if_pos (show U ∈ {U:Config G n|Healthy v W U} from ht.mp h)]; unfold petalWorth; simp_rw [petals_gauge,norm_smul, G.norm_adjoint] -- tune
 · rw [if_neg (show U ∉ {U:Config G n|Healthy v W U} from fun u=>h (ht.mpr u))]
private lemma costOne (F:PlaqAxes) (h: Healthy P.threshold (halo 10 {(0:Site n)}) U): ‖petals U 0 F‖ ≤ P.threshold:=by
 let V:(Tray→ G.Color):=fun i=> (atTray i.1 i.2 F).atSite U 0
 unfold petals clover stencil; rw [norm_smul,Real.norm_of_nonneg (by positivity: (0:ℝ) ≤4⁻¹)]; have hp (a b:Step)(p:a.dir < b.dir): ‖StressFlux.plate U 0 a b‖≤P.threshold:= (G.curvature_norm _).trans (Square.small a b p (Finset.disjoint_left.mpr (fun _ w=> Finset.disjoint_left.mp h (halo_subset _ _ w))))
 let A:=F.val.1; let D:=F.val.2
 have pol(i j: Step)(u:i.dir=A)(y:j.dir=D):=hp i j (by rw [u,y]; exact F.property)
 apply le_trans (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (norm_sub_le ..) (norm_sub_le ..))) (by norm_num:(0:ℝ) ≤4⁻¹)); linarith only [pol (posDir A) (negDir D) rfl rfl,pol (posDir A) (posDir D) rfl rfl,pol (negDir A) (negDir D) rfl rfl,pol (negDir A) (posDir D) rfl rfl]
abbrev meritG := ∑ i:PlaqAxes, |z i|
abbrev costG (t ρ:ℝ):ℝ:= meritG z *(ρ*t)^2
lemma costG_le(s:Signed)(o:Site n): |garland z x P.threshold s o U|≤ costG z P.threshold x:=by
 unfold garland; let X:=pull s o U; by_cases g : Healthy P.threshold (halo 10 {(0:Site n)}) X; swap; · rw [masked_ne _ _ _ _ g]; unfold costG meritG; simp; positivity
 rw [masked_eq _ _ _ _ g]; unfold petalWorth costG meritG; rw [sum_mul]; apply (abs_sum_le_sum_abs ..).trans; refine sum_le_sum (fun i _=>?_); rw [abs_mul,abs_of_nonneg (sq_nonneg ‖x • petals (pull s o U) 0 i‖)]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); change ‖_ • petals X 0 _‖^2≤_; rw [norm_smul,Real.norm_eq_abs,mul_pow |x|,mul_pow x,sq_abs]; gcongr; exact costOne i g
lemma costG_env(s:Signed)(o:Site n):RG.Envelope (garland z x P.threshold s o (G:=G)):=by
 refine ⟨?_,costG z P.threshold x,(fun i=> by rw [Real.norm_eq_abs]; exact costG_le ..)⟩; change Measurable ((RG.masked P.threshold (halo 10 {(0: Site n)}) _ )∘ (pull s o : Config G n→_)); apply Measurable.comp; · unfold petalWorth; fun_prop
 exact (prior_pull s o).measurable
lemma port (s:Signed)(o:Site n){A:Support c}(T:withinCore r A (face_anchors (misdemean P.threshold U)) (hallBill m) o)(p:12≤hallBill m) : Healthy P.threshold (halo 10 {(0:Site n)}) (pull s o U):=by
 apply (healthy_pull s o ..).mp; rw [halo_plan,affine,Signed.act_zero,zero_add]; apply disjoint_left.mpr; intro i h t; obtain ⟨x,L,k⟩:=(flags_spec ..).1 t; apply T.2 (halo_spec.mpr ⟨x.1,mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,k⟩),?_⟩); have ht:separation o i ≤10:=by simpa [halo_spec] using h
 apply (separation_triangle x.1 i o).trans; have hx:=Work.E01.sep_touched x i L; rw [separation_comm i o]; omega
/-- error coupling on scaled sketch paid station by station even for very large stencil pairs. -/
lemma garland_norm(s:Signed)(o:Site n)(vv:ℝ)(p:0<vv)(H: Healthy P.threshold (halo 10 {(0:Site n)}) (pull s o U)): |garland z x P.threshold s o U-(amaryllis z G vv p).palette x s o U| ≤ meritG z * ((x*P.threshold)^4/vv):=by
 let W:= pull s o U; have hc(i): ‖x • petals W 0 i‖^4 ≤ (x*P.threshold)^4:=by
    have he := costOne i H; rw [mul_pow,norm_smul,Real.norm_eq_abs, mul_pow]; rw [show |x|^4=x^4 from abs_pow_four x]; gcongr
 rw [show (amaryllis z G vv p).palette x s o U= (amaryllis z G vv p).here x W from ?_]; swap; · unfold here W palette; rw [pull_id]
 rw [amaryllis,salix_h]; unfold garland; rw [masked_eq _ _ _ _ H]; unfold petalWorth meritG; rw [sum_mul,←sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans; apply sum_le_sum; intro i _; rw [mellow_eval,←mul_sub, abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); let y:= ‖x • petals W 0 i‖; change |y^2-viewμ vv (y^2)|≤_; rw [abs_of_nonneg (sub_nonneg.mpr (clipμ p _ (sq_nonneg y)).2.2.1)]; refine (clipμ p _ (sq_nonneg y)).2.2.2.trans (div_le_div_of_nonneg_right ?_ p.le); rw [show (y^2)^2=y^4 from (by ring)]; exact hc _
where abs_pow_four (x:ℝ): |x|^4=x^4:=Even.pow_abs (by decide) x
lemma garland_match(B:Z.Bounds q η C S)(H':Attached H Z)(R:Rules G)(p:0<k) (h:(amaryllis z G k p).payroll ≤ m)(s:Signed){o:Site n}(g:withinCore r T (face_anchors (misdemean P.threshold U)) (hallBill m) o)(hp:12≤ hallBill m)(l:TrustLogs (V+Y) U r T v)(K:0 ≤ v)(d:v ≤ R.c)(f:0<β):let F:=amaryllis z G k p; |garland z x P.threshold s o U - F.chalk q (x*coupling β) s o (starFeed B H' r T (face_anchors (misdemean P.threshold U)) m Y β V)| ≤ meritG z*((x*P.threshold)^4/k)+ F.priceS R x v :=by intro F; exact abs_sub_le (garland _ _ _ ..) (F.palette x s o U) _|>.trans (add_le_add (garland_norm z s _ _ p (port s _ g hp)) (F.inside_match B H' R h s g l K d f)) -- tune
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.Etch.garland_match
