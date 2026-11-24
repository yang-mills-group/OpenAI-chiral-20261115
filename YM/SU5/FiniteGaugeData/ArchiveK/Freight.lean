import YM.SU5.FiniteGaugeData.ArchiveK.Crimp
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open MeasureTheory.Measure
variable {p:Momentum}{E x: E4}{M:Tulip.Male}
-- normalized table tomography.
abbrev stair:= suiteC Axis (-Real.pi) τ
def μF:= MeasureTheory.volume.restrict stair
lemma stair_p : μF.real Set.univ=τ^4:= by rw [μF,Measure.real,Measure.restrict_apply_univ,snowPay (-Real.pi) τ tau_pos, Fintype.card_fin]; exact ENNReal.toReal_ofReal (pow_nonneg tau_pos.le _)
lemma μFin:IsFiniteMeasure μF:= ⟨by rw [μF,Measure.restrict_apply_univ,snowPay (-Real.pi) τ tau_pos]; finiteness⟩
attribute [local instance] μFin
lemma stair_body(h:x∈ stair): brushQ x∈baseCube:=by
 refine ⟨tmap_physical _,fun i=>?_⟩; obtain ⟨a,b⟩:= in_snow _ _ x|>.1 h i; rw [abs_le]; unfold brushQ Fir.tmap; rw [ofReal_re]; exact ⟨a,b.le.trans_eq (by unfold τ; ring)⟩
lemma stargaze : ∀ᵐ x ∂μF,(∀ i:Cover, pass (brushQ x+reciprocal i) ≠0) ∧ x≠0 ∧ brushQ x≠0 ∧ x∈ stair := by
 filter_upwards [ae_restrict_mem (snowC (-Real.pi) τ), ae_restrict_of_ae (zero_free (MeasureTheory.volume (α:=E4)))] with x h v; have hm(i:Cover): x+songQ τ i∈tempoC τ i '' stair:=Set.mem_image_of_mem (tempoC τ i) h; have he:∃ v':Axis,x v'≠0:=Function.ne_iff.mp ((WithLp.ofLp_injective 2).ne v)
 have hz:(0:E4)∈stair:= by apply (in_snow (-Real.pi) τ _).2; intro i; unfold τ; change -Real.pi ≤ 0∧ 0< -Real.pi+2*Real.pi; constructor <;> linarith [Real.pi_pos]
 obtain ⟨v',p'⟩:=he; have hk: songQ τ (0:Cover)=0:=by apply PiLp.ext; intro j; simp [songQ]
 refine ⟨fun i=> ?_ ,v, fun e=>p' (ofReal_eq_zero.mp (congr_fun e v')), h⟩
 rw [show brushQ x+reciprocal i=brushQ (x+songQ τ i) from ?_,spendQ]; apply ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr ?_)); · intro v'; have ht:= hm i; rw [v'] at ht; have hp: i=0:=(pac_acco (-Real.pi) τ 0 tau_pos).unique ht ⟨0,hz,(by rw [tempo_map,hk]; simp)⟩; rw [hp,hk,add_zero] at v'; contradiction
 funext a; unfold brushQ Fir.tmap reciprocal songQ τ; simp
lemma iron_rec(x:E4)(i:Cover): brushQ (x+songQ τ i) = brushQ x+reciprocal i:=by funext a; unfold brushQ Fir.tmap reciprocal songQ τ; simp
abbrev slurp (p:E4):Momentum:= Largo.melody (brushQ p)
abbrev rain (p:E4):Op SpinIdx:= -zen (slurp p)
lemma melody_X (p:E4)(a:Axis): Largo.melody (brushQ p) a=∑' i:Cover,ironQ (p+songQ τ i) a:=by simp_rw [ironQ,amiX,iron_rec]; rfl
lemma slurp_I(a:Axis) : Integrable (fun p:E4=> slurp p a) μF:=by simp_rw [slurp,melody_X]; exact (modern_P tau_pos (ironQ_meet a)).2.1 -- plug a
@[fun_prop] lemma song_in (a:Cover) : Continuous (fun x:E4=>mode (brushQ x) a):= by simp_rw [surfK]; fun_prop
lemma sing_in {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X][IsScalarTower ℝ ℂ X]{f:E4→X}(g:Integrable f μF)(a:Cover): Integrable (fun p:E4=> mode (brushQ p) a • f p) μF:=by
 apply g.norm.mono'; · exact (song_in a).aestronglyMeasurable.smul g.1
 exact ae_of_all _ fun i=> by simp only [norm_smul,surfK,coast_pay,one_mul, le_refl]
abbrev gain:= τ^4
def scout {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X] (f:E4→X)(a:Cover): X:= gain⁻¹ • (∫ p,mode (brushQ p) a • f p∂μF)
lemma gain_h:0<gain:=pow_pos tau_pos _
local notation "Δ"=> scout
section
variable (X:Type*)[NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X][IsScalarTower ℝ ℂ X]
#print axioms slurp_I
lemma scout_pa (a:Cover) (U:Axis): scout (fun p=>slurp p U) a=((gain⁻¹:ℝ):ℂ)*sax U (emitX a):=by
 let x:= emitX a; let F:= yotta U x; have he : sax U (emitX a)= ∫ x,(∑' i: Cover,F (x+songQ τ i))∂μF:=(modern_P tau_pos (yotta_int _ U)).2.2.symm; unfold scout; rw [Complex.real_smul,he]; apply congrArg; refine integral_congr_ae ?_; filter_upwards with p
 change mode (brushQ p) a • Largo.melody _ U= _; rw [melody_X]; unfold F yotta; unfold x; simp_rw [← surfK,iron_rec,mode_phase,mode_periodic, mul_one,tsum_mul_left,smul_eq_mul]
end
-- integrals in Banach. complex X. ∫ E. same signs.
section
variable {X Y:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X][IsScalarTower ℝ ℂ X][CompleteSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedSpace ℂ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]{f g:E4→X}
lemma pact (x:X)(a:Cover): scout (fun _:E4=>x) a=if a=0 then x else 0:=by
 have hp: (∫ p, mode (brushQ p) a∂μF) = if a=0 then (((τ:ℂ)^4)) else 0:=by
    unfold μF; simp_rw [surfK]; let z:songQ (τ/τ) a=emitX a:=(by rw [div_self tau_pos.ne']; apply PiLp.ext; intro i; simp [songQ]); simp_rw [←z]; exact song_a (n:=Axis) tau_pos _ -- tune
 unfold scout; rw [integral_smul_const,hp]; split; · rw [show (τ:ℂ)^4=(gain:ℂ) from (by unfold gain; push_cast; rfl), ← smul_assoc]; rw [Complex.real_smul,ofReal_inv]; simp [gain_h.ne'] -- tune
 simp
lemma scout_add (t:Integrable f μF)(p:Integrable g μF)(a:Cover): scout (fun x=>f x+g x) a=scout f a+scout g a:= by unfold scout; simp_rw [smul_add]; rw [integral_add (sing_in t a) (sing_in p a),smul_add]
lemma scout_sum {Z:Type*}(T:Finset Z)(F:Z→E4→X)(h:∀ i∈T,Integrable (F i) μF) (a:Cover): scout (fun x=>∑ i∈ T,F i x) a=∑ i∈ T,scout (F i) a:=by unfold scout; simp_rw [Finset.smul_sum]; rw [integral_finsetSum _ (fun i t=>sing_in (h i t) a), Finset.smul_sum]
lemma scout_we (A:X→L[ℂ] Y)(t:Integrable f μF)(a:Cover): scout (A ∘ f) a=A (scout f a):=by
 unfold scout; let F:= A.restrictScalars ℝ; have hs:= sing_in t a; let H:= (F.integral_comp_comm hs); simp_rw [Function.comp_apply,←map_smul];  exact (congrArg (fun y:Y=> gain⁻¹ • y) H).trans (map_smul F _ _).symm --  (map_smul (A.restrictScalars ℝ) _ _).symm -- note H_defeq
lemma scout_more (f:E4→X)(x a:Cover): scout (fun p=> mode (brushQ p) x • f p) a= scout f (a+x) := by unfold scout; simp_rw [smul_smul,mode_shift]
end
#print axioms scout_pa
end YM.CF.Window.ArchiveK
