import YM.SU5.FiniteGaugeData.ArchiveK.Lambert
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open MeasureTheory.Measure
section grav
-- On any ℝ^n × lattice; purchase alias probabilities, volumes and orth
variable {n:Type} [Fintype n][DecidableEq n] (x:n→ℝ)(a c:ℝ) (E:EuclideanSpace ℝ n) (G:n→ℤ)
abbrev Snow(n:Type) [Fintype n]:=EuclideanSpace ℝ n
def suiteC (n:Type)[Fintype n] (a c:ℝ): Set (Snow n):= ofLp ⁻¹' (Set.univ.pi fun _=>Set.Ico a (a+c)) -- Ico. shift. tail script.
def songQ(c:ℝ)(G:n→ℤ) : Snow n:= toLp 2 fun i=> c * G i
lemma snowC : MeasurableSet (suiteC n a c):= (MeasurableSet.univ_pi (fun _=> measurableSet_Ico)).preimage ((PiLp.volume_preserving_ofLp n).measurable)
lemma in_snow(x:Snow n): x∈ suiteC n a c↔∀ i:n,x i∈Set.Ico a (a+c):= Set.mem_univ_pi -- tune
lemma snowPay(c₀:0<c) : volume (suiteC n a c)= ENNReal.ofReal (c^Fintype.card n):= by
 unfold suiteC; rw [(PiLp.volume_preserving_ofLp n).measure_preimage ((MeasurableSet.univ_pi fun _=> measurableSet_Ico).nullMeasurableSet)] -- tune measurableSet mismatch
 rw [volume_pi,Measure.pi_pi]; simp_rw [Real.volume_Ico,add_sub_cancel_left]; simp only [Finset.prod_const,Finset.card_univ, ENNReal.ofReal_pow c₀.le];
lemma snow_pay (c₀:0<c) : MeasureTheory.volume.real (suiteC n a c) = c ^ Fintype.card n:= by rw [Measure.real,snowPay a c c₀,ENNReal.toReal_ofReal]; positivity
variable {H:n→ℤ}
def tempoC(G:n→ℤ): Snow n ≃ₜ Snow n := Homeomorph.addRight (songQ c G)
lemma tempo_c : MeasurePreserving (tempoC c G) volume volume:= measurePreserving_add_right MeasureTheory.volume _
lemma tempo_map (x:Snow n) : tempoC c G x=x+songQ c G:=rfl
abbrev pacC (G:n→ℤ):= (tempoC c G) '' suiteC n a c
lemma pac_cl : MeasurableSet (pacC a c G):= (tempoC c G).measurableEmbedding.measurableSet_image.mpr (snowC a c)
lemma pac_key : E∈pacC a c G ↔ ∀ i, a ≤ E i - c*G i ∧ E i - c*G i < a+c :=by
 constructor
 · rintro ⟨x,h,rfl⟩ i; rw [in_snow] at h; simpa [tempo_map,songQ] using h i
 intro h; refine ⟨E-songQ c G, (in_snow a c _).2 (fun i=>?_ ),?_ ⟩; exact h _; exact sub_add_cancel ..
lemma pac_acco (c₀:0<c) : ∃! G:n→ℤ, E∈pacC a c G :=by
 let f(i:n):= ⌊(E i-a)/c⌋
 have he (y:n→ℤ) : E∈pacC a c y ↔ f=y:=by
    rw [pac_key,funext_iff]; apply forall_congr'; intro i; unfold f; rw [Int.floor_eq_iff,le_div_iff₀ c₀,div_lt_iff₀ c₀]; constructor <;> intro h <;> constructor <;> (obtain ⟨y,r⟩:=h; linarith only [y,r])
 exact ⟨f,(he _).2 rfl,fun v h=> ((he v).1 h).symm⟩
lemma pac_world(c₀:0<c) : ⋃ G:n→ℤ,pacC a c G=Set.univ:= Set.eq_univ_of_forall (fun x=> Set.mem_iUnion.mpr (pac_acco a c x c₀).exists)
lemma pac_disjoint(c₀:0<c) {G H:n→ℤ}(e:G≠H): Disjoint (pacC a c G) (pacC a c H):= Set.disjoint_left.mpr fun x h t=>e ((pac_acco a c x c₀).unique h t)
end grav
section l_one
variable {X J A:Type*} {_m:MeasurableSpace X} {μ:Measure X} [Countable J][NormedAddCommGroup A][NormedSpace ℝ A][CompleteSpace A]{F:J→X→ A} (p:∀ i,Integrable (F i) μ) (t:Summable (fun i=> ∫ a,‖F i a‖∂μ))
include p t
lemma weft_sum : ∑' i,eLpNorm (F i) 1 μ≠⊤:= by
 simp_rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (p _)]; rw [← ENNReal.ofReal_tsum_of_nonneg (fun i=>integral_nonneg (fun _=>norm_nonneg _)) t]; finiteness
lemma weft_conclude : ∀ᵐ x ∂μ, Summable (fun j=> ‖F j x‖):= summable_norm_of_tsum_eLpNorm_ne_top (p:=1) le_rfl (fun i=>(p i).1) (weft_sum p t)
lemma weft_paid : Integrable (fun x=> ∑' i,F i x) μ:= by
 let H(i):= MemLp.toLp (μ:=μ) (p:=1) (F i) (memLp_one_iff_integrable.mpr (p i)); let W:=∑' i,H i; have he: ⇑W=ᵐ[μ] fun x=> ∑' i,F i x:=by
    have hu: ∑' i, ‖H i‖ₑ ≠ ⊤:=by simp_rw [H,Lp.enorm_toLp]; exact weft_sum p t
    have hx:⇑W =ᵐ[μ] (fun x=>∑' i,H i x):= Lp.coeFn_tsum hu; filter_upwards [hx,(ae_all_iff (p:=fun x i=>H i x=F i x)).mpr (fun i=> MemLp.coeFn_toLp _)] with x h s; rw [h]; simp_rw [s]
 exact (memLp_one_iff_integrable.mp (Lp.memLp W)).congr he
#print axioms weft_paid
end l_one
section t
variable {n:Type} [Fintype n][DecidableEq n] {a c:ℝ}(v:0<c)
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]{F:Snow n→ X} (h:Integrable F)
local notation "S"=> suiteC n a c
local notation "Υ"=> pacC a c
local notation "Θ"=> MeasureTheory.volume.restrict (suiteC n a c)
omit v in
lemma picH (F:Snow n→X)(H:Set (Snow n))(G:n→ ℤ) : ∫ x in tempoC c G '' H,F x = ∫ x in H,F (x+songQ c G):= tempo_c c G|>.setIntegral_image_emb (tempoC c G).measurableEmbedding F H
include v h
lemma portsPa : ∑' i:n→ℤ,(∫ x in S,F (x+songQ c i))= ∫ x,F x:= by
 simp_rw [← picH]; rw [←integral_iUnion]; · rw [pac_world a c v,setIntegral_univ];
 exact fun i=> pac_cl a c i
 exact fun _ _ e=> pac_disjoint a c v e
 exact h.integrableOn -- rt
lemma portsPn : Summable (fun i:n→ℤ=> ∫ x in S, ‖F (x+songQ c i)‖):= by
 let f:=fun x=> ‖F x‖; let T:= fun i:n→ℤ=>tempoC c i '' S; have he:= hasSum_integral_iUnion (f:=f) (fun i=>pac_cl a c i) (fun _ _ e=> pac_disjoint a c v e) h.norm.integrableOn; exact he.summable.congr (fun i=> picH f S i)
omit h v
lemma paidOne(c:ℝ) (F:Snow n→X) (p:Integrable F) (i:n→ℤ): Integrable (fun x=>F (x+songQ c i)):= tempo_c c i|>.integrable_comp_of_integrable p
include h v
lemma modern_P : (∀ᵐ x ∂(MeasureTheory.volume.restrict (suiteC n a c)), Summable fun i:n→ℤ=> ‖F (x+songQ c i)‖) ∧ Integrable (fun x=> ∑' i:n→ℤ,F (x+songQ c i)) (MeasureTheory.volume.restrict (suiteC n a c)) ∧ ∫ x in S,(∑' i:n→ℤ,F (x+songQ c i))=∫ x,F x:= by
 let f:= fun (i:n→ℤ) (x:Snow n)=>F (x+songQ c i); let g(i:n→ℤ):= (show Integrable (f i) Θ from (paidOne c F h i).integrableOn); let H:=portsPn (a:=a) v h; exact ⟨weft_conclude g H, weft_paid g H , (hasSum_integral_of_summable_integral_norm g H).tsum_eq.symm.trans (portsPa (a:=a) v h)⟩
end t
-- orthonorm normalization. h period real (ω_k.T layers). tuple x in Euclidean ℝ. frequency reversed.Enabling multiple asset.Paper.
section tones
variable {n:Type}[Fintype n][DecidableEq n]{a c:ℝ}(p:0<c)(x:Snow n) (Z:n→ℤ)
local notation "S"=> suiteC n a c
local notation "ω"=> MeasureTheory.volume.restrict (suiteC n a c)
def songT (c:ℝ)(Z:n→ℤ)(x:Snow n):ℂ:=coastE (inner ℝ x (songQ (τ/c) Z))
lemma songK : songT c Z x=∏ i, coastE (x i*(τ/c)*Z i):=by
 unfold songT coastE songQ; simp only [PiLp.inner_apply,RCLike.inner_apply,WithLp.ofLp_toLp]; push_cast; -- real `mul` repr conj RR
 rw [mul_sum,Complex.exp_sum]; apply prod_congr rfl; intro i _; simp; ring -- tune
include p
lemma song_s (u:ℤ) : ∫ x:ℝ in Set.Ico a (a+c), coastE (x*(τ/c)*u) = if u=0 then (c:ℂ) else 0:=by
 split_ifs with h; · subst u; simp only [Int.cast_zero, mul_zero,coast_zero]; rw [setIntegral_const, Measure.real, Real.volume_Ico, add_sub_cancel_left, ENNReal.toReal_ofReal p.le]; rw [Complex.real_smul, mul_one] -- tune
 let V:ℂ:= Complex.I*((τ/c:ℝ):ℂ)*u; let f(x:ℝ):= Complex.exp (V*x); rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_add_of_nonneg_right p.le)]; have he: V ≠ 0:= mul_ne_zero (mul_ne_zero Complex.I_ne_zero ((show (((τ/c:ℝ):ℝ):ℂ)≠0 from by exact_mod_cast (div_ne_zero tau_pos.ne' p.ne')))) (Int.cast_ne_zero.mpr h); simp_rw [show ∀ x:ℝ, coastE (x*(τ/c)*u)=f x from (fun i=>by unfold f V coastE; push_cast; ring_nf)]; unfold f; rw [integral_exp_mul_complex he]; suffices hk: Complex.exp (V*(a+c:ℝ))=Complex.exp (V*a) by rw [hk,sub_self, zero_div]; -- parser ↑? tuning
 rw [ofReal_add,mul_add,Complex.exp_add, show Complex.exp (V*c)=1 from ?_, mul_one]; rw [show V*c=(((u:ℤ):ℂ))*(2*Real.pi*Complex.I) from ?_, Complex.exp_int_mul_two_pi_mul_I]; unfold V τ; push_cast; have h':c≠0:=p.ne'; field_simp -- tune
lemma song_a : (∫ x in (suiteC n a c),songT c Z x)= if Z=0 then ((c:ℂ)^ Fintype.card n) else 0:= by
 let f(i:n)(x:ℝ):= coastE (x*(τ/c)*Z i); let T:= MeasureTheory.volume.restrict (Set.Ico a (a+c)); let U:= MeasureTheory.volume (α:=n→ℝ); let H:=Set.univ.pi (fun _:n=> Set.Ico a (a+c)); let Y(x:n→ℝ):= ∏ i,f i (x i); have ht:∫ x in S,songT c Z x= ∫ x,Y x∂ Measure.pi (fun _=> T):=by
    simp_rw [songK]; rw [← Measure.restrict_pi_pi]; change ∫ x in (S), Y (ofLp x)=∫ x in H, Y x ∂U; exact (PiLp.volume_preserving_ofLp n).setIntegral_preimage_emb ((MeasurableEquiv.toLp 2 (n→ℝ)).symm.measurableEmbedding) Y H -- T unfold
 rw [ht]; unfold Y; rw [integral_fintype_prod_eq_prod]; unfold f T; simp_rw [song_s p]; split_ifs with h; swap; · obtain ⟨i,e⟩:= Function.ne_iff.mp h; exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg e) -- tune
 subst Z; simp
end tones
#print axioms modern_P
#print axioms song_a
end YM.CF.Window.ArchiveK
