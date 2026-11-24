import Gingham.Ruff.Chaparral
import Zephyr.Chern.Tile
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
/-! # Actual affirmative jet on Ruff ingredients, transferring Sprig to Rialto. -/
set_option autoImplicit false
set_option maxHeartbeats 260000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.WakeRoad
open Function Filter Topology NormedSpace Set CF Lattice
open CF.Gingham.Ruff
open _root_.Zephyr.Chern CF.Kea
private theorem c_exp_pt {J:Type*}[Fintype J](f:J→ℂ)(i:J) : exp f i = Complex.exp (f i) := by
 rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]; dsimp only; rw [tsum_apply (by rw [←expSeries_apply_eq' f]; exact expSeries_summable (𝕂:=ℂ) f)]
 simp

local notation "G"=> SU.group
private abbrev seed : SU.F→ℂ:=fun i=>Complex.I * ↑(dye.val i)
private abbrev generator : (G).Mat := Matrix.diagonal seed
private lemma spark_matrix(t:ℝ): exp (t • generator)=(G).mat (arc t):=by
 have he:(G).mat (arc t)=(moor t).2:= congrArg Prod.snd (brand_arc t)
 rw [he]; change exp (t • Matrix.diagonal seed)= Matrix.diagonal _
 rw [←Matrix.diagonal_smul, Matrix.exp_diagonal]; refine congrArg Matrix.diagonal (funext fun i=> ?_)
 rw [c_exp_pt,Pi.smul_apply,Complex.real_smul]; congr 1; ring

private def cartMint := (G).projectColor generator
lemma spark_links(t:ℝ) : (G).lieExp (t • cartMint) = arc t:=by
 apply Gauge.mat_injective
 rw [Gauge.mat_lieExp,map_smul,cartMint,Gauge.colorMat_project_self G ((Gauge.mem_lie G).mpr fun v=>⟨_,(spark_matrix v).symm⟩),spark_matrix]
open CF.Skye CF.Tulip CF.Cube
variable {N:Side}
def jetColor(N:Side)(δ:ℝ):Doub N:=(fun i=> (δ⁻¹*(stream N i)) • cartMint,0)
lemma cart_pencil (t:ℝ){δ:ℝ}(h:δ≠0): pencil δ (t • jetColor N δ)=petals (stream N) t:=by
 funext i; change (G).lieExp (δ • t • _) * (G).lieExp (δ • t • (0:(G).Color))=_
 simp only [smul_zero,show (G).lieExp 0=1 from (by simp),mul_one]
 unfold petals; rw [←spark_links]
 change (G).lieExp (δ • t • (δ⁻¹*_) • _)=_
 rw [smul_smul,smul_smul]; congr 2; field_simp

open CF.Lat CF.Gingham.Ruff.Shells
open CF.Lich
lemma jetMist(δ:ℝ)(h:0<δ):∃ C:ℝ,∀ N:Side,sprays (bouton (0:Site N)) (jetColor N δ) C:=by
 let r:=16 / δ * ‖cartMint‖
 have hr:0 ≤ r:= mul_nonneg (by positivity) (norm_nonneg _)
 refine ⟨2*r,fun n=> ⟨mul_nonneg (by norm_num) hr,fun i=>?_⟩⟩
 let H(i:Edge (Seat n)):= (stream_mild n).grow i
 have e:(separation i.1 (1:Seat n):ℝ) ≤ separation (bouton (0:Site n)) i.1 + 1:= by
   exact_mod_cast (show separation i.1 1 ≤ _+1 from (separation_triangle _ (bouton (0:Site n)) _).trans (by rw [separation_comm i.1]; gcongr; simpa [node] using bouton_clear (0:Site n)))
 rw [Prod.norm_def]; change max ‖(δ⁻¹ * stream n i) • cartMint‖ ‖(0:(G).Color)‖ ≤ _; rw [norm_zero,max_eq_left (norm_nonneg _), norm_smul]
 have hx:|stream n i|≤16*(1+(separation i.1 1:ℝ)):= H i
 simp only [Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos h]
 apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) (norm_nonneg _))
 unfold r; have h4:0≤δ⁻¹* ‖cartMint‖:= mul_nonneg (by positivity) (norm_nonneg _)
 rw [div_eq_mul_inv]; nlinarith [mul_le_mul_of_nonneg_left e h4,
  show 0≤ (separation (bouton (0:Site n)) i.1:ℝ) from Nat.cast_nonneg _]

open scoped ContDiff
lemma bloomLine {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ℂ)(h:ContDiffAt ℝ 6 f 0)(Z:fderiv ℝ f 0 = 0)(v:E) :
 Bloom (fun r:ℝ=>f (r • v)) ![f 0,0,quadraticChi f v]:=by
 have Y(t:ℝ): HasDerivAt (fun r:ℝ=> r • v) v t:= by convert ((hasDerivAt_id' t).smul_const v); simp
 have ha: ∀ᶠ (t:ℝ) in 𝓝 0, DifferentiableAt ℝ f (t • v):= by
   have s:= (h.eventually (by simp: (6:WithTop ℕ∞) ≠ ↑(⊤:ℕ∞)))
   have hf: Tendsto (fun t:ℝ=> t • v) (𝓝 0) (𝓝 0):=by simpa using ((show Continuous (fun t:ℝ=>t • v) from continuous_id.smul continuous_const)).tendsto (0:ℝ)
   exact hf.eventually (s.mono fun _ k=> k.differentiableAt (by norm_num))
 let F':E→E→L[ℝ]ℂ:= fderiv ℝ f
 have t: DifferentiableAt ℝ F' 0 := (h.fderiv_right (by norm_num: (1:WithTop ℕ∞)+1 ≤ 6)).differentiableAt (by simp)
 have y:HasFDerivAt F' (fderiv ℝ F' 0) ((0:ℝ) • v):= by rw [zero_smul]; exact t.hasFDerivAt
 let g:= fun r:ℝ=>r • v
 let X:=(ContinuousLinearMap.apply ℝ ℂ v : (E→L[ℝ]ℂ)→L[ℝ]ℂ)
 have he₀:HasFDerivAt (fun z=>F' z v) (X.comp (fderiv ℝ F' 0)) (g 0):=
    HasFDerivAt.comp (g 0) (X.hasFDerivAt (x:=F' (g 0))) y
 have he: HasDerivAt (fun r:ℝ=> F' (g r) v) (fderiv ℝ F' 0 v v) 0:=
    HasFDerivAt.comp_hasDerivAt 0 (f:=g) (F:=E) he₀ (Y 0)
 have hx(t:ℝ)(w:DifferentiableAt ℝ f (g t)) : HasDerivAt (f ∘ g) (F' (g t) v) t :=
    HasFDerivAt.comp_hasDerivAt t (f:=g) w.hasFDerivAt (Y t)
 refine Bloom.of_der (ha.mono (fun i w=> hx i w)) he ?_ ?_ ?_
 · rw [zero_smul]; rfl
 · change 0=fderiv ℝ f ((0:ℝ) • v) v
   simp [Z]
 change (2:ℝ)⁻¹ • (fderiv ℝ F' 0 v v) = _/2
 rw [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat]; ring
