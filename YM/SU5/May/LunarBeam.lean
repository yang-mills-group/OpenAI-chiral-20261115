import YM.SU5.May.LunarFirm
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical
open Window.ArchiveK Window.Largo
attribute [local instance] opCStarAlgebra
variable {T δ:ℝ}(h:0<T) (α:ℝ)(p:δ≤1)(u:δ*δ=1)(s:coastE (α*(2* Real.pi))=(δ:ℂ))
variable (P N:E4)(ht:‖N‖=1)(hm:inner ℝ N P=0)(q:P≠0)(x:ℝ)
-- $alpha left charge
local notation "V" n:max => nodeR T α n
local notation "η" => ‖P‖
local notation "Z" i:max => (P+i • N)
local notation "Y" => Real.exp (-‖P‖*T)
local notation "Χ" i:max=> ((i):ℂ)
local notation "𝕀"=> Complex.I
def saleD(P N:E4)(b x:ℝ):ℂ:= I*b*pillarF P N b x
lemma derivP (b:ℝ): HasDerivAt (pillarF P N b) (saleD P N b x) x:=by
 let Q:= P+b • N; let B:=amiX Q; unfold saleD pillarF; convert! ((((((hasDerivAt_id' x).mul_const b).ofReal_comp).const_mul I).cexp.mul_const _).mul_const _) using 1; simp only [one_mul] -- tune
 ring
include ht hm
lemma earn_square (b:ℝ): ‖P+b • N‖^2=‖P‖^2+b^2:=by rw [norm_add_sq_real, real_inner_smul_right,real_inner_comm N P,hm,norm_smul,ht,Real.norm_eq_abs]; simp
lemma sale_bound (b:ℝ): ‖saleD P N b x‖ ≤ 4*whey ‖P‖ b:=by
 unfold saleD pillarF; simp only [norm_mul,norm_I, coast_pay, one_mul,Complex.norm_real,Real.norm_of_nonneg (whey_p _),Real.norm_eq_abs]; rw [mul_comm (whey _ _),←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (whey_p _); let C:= ‖(Z b)‖
 rcases le_or_gt |b| 4 with v|v; · exact (mul_le_of_le_one_right (abs_nonneg _) (ami_le _)).trans v
 have he:|b|≤C:= (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by rw [sq_abs,show C^2=_ from earn_square P N ht hm b]; exact le_add_of_nonneg_left (sq_nonneg _)); have hg:4<C:=v.trans_le he; have hz:0<C:= (show (0:ℝ)<4 by norm_num).trans hg; have hp:= aba (Z b) (norm_pos_iff.mp hz); have ht:(4/C)^8 ≤ 4/C:= pow_le_of_le_one (by positivity) ((div_le_one hz).mpr hg.le) (by norm_num)
 exact (mul_le_mul he (hp.trans ht) (norm_nonneg _) hz.le).trans_eq (by field_simp)
local notation "Φ" => plateF T ‖P‖ δ P N
local notation "B" n:max => pillarF P N (V n)
local notation "U" => fareP T ‖P‖ δ
local notation "C" => ((δ*Real.exp (- ‖P‖*T):ℝ):ℂ)
include h p q s u
private lemma level (v:-T+20<x)(w:x< -20) : HasSum (fun n:ℤ=>saleD P N (V n) x) ((Χ U)* (Χ η) * (errata P N η x-C*errata P N (-η) x)):=by
 let g(n:ℤ):=saleD P N (V n) x; have hv:= (stableK h (norm_pos_iff.mpr q) α).mul_left 4; let t:ℂ:=errata P N η x; let t':ℂ:= errata P N (-η) x; have he(z:ℝ): HasDerivAt (errata P N z) ((z:ℂ)*errata P N z x) x:=by
    unfold errata; convert! (((((hasDerivAt_id' x).const_mul z).exp).ofReal_comp).mul_const _) using 1 <;> (push_cast; ring)
 have hp : HasDerivAt (Φ) ((Χ U)*(Χ η)*(t-C*t')) x:= by
    unfold plateF; convert! (((he η).add ((he (-η)).const_mul C)).const_mul ((fareP T ‖P‖ δ:ℝ):ℂ)) using 1; push_cast; ring -- Let
 have hm': (fun y=>∑' n:ℤ,pillarF P N (V n) y)=ᶠ[𝓝 x] (Φ):= ((lt_mem_nhds v).and (gt_mem_nhds w)).mono fun n e=> (steady h α p u s _ _ ht q n e.1 e.2).tsum_eq
 have hb:∑' n,g n= _:= (hasDerivAt_tsum (g:=fun n:ℤ=> B n) (g':=fun n=> saleD P N (V n)) hv (fun i y=>derivP P N y _) (fun i y=>sale_bound P N ht hm y _) (steady h α p u s P N ht q x v w).summable x).unique (hp.congr_of_eventuallyEq hm'); exact hb ▸ (Summable.of_norm_bounded hv (fun i:ℤ=>sale_bound P N ht hm x (V i))).hasSum -- hb defeq t
-- combine
variable (i:Axis)(r:E4)
def rays(T δ:ℝ)(P N r:E4):Momentum:= (coastE (inner ℝ P r)* ((fareP T ‖P‖ δ:ℝ):ℂ)) • (errata P N ‖P‖ (inner ℝ N r) • shaft P N ‖P‖ +(((δ*Real.exp (- ‖P‖ * T):ℝ):ℂ)*errata P N (- ‖P‖) (inner ℝ N r)) • shaft P N (- ‖P‖))
omit h s u p q
private lemma picture (b:ℝ): spectral (Z b) r i= coastE (inner ℝ P r)* (brushQ P i * pillarF P N b (inner ℝ N r) - 𝕀*brushQ N i * saleD P N b (inner ℝ N r)) :=by
 rw [spectral]; simp only [Pi.smul_apply, smul_eq_mul,inner_add_left,real_inner_smul_left,ironQ,spendQ,earn_square P N ht hm,coast_add,saleD,pillarF]; push_cast; nth_rw 1 [mul_comm b (inner ℝ N r)]; unfold brushQ Fir.tmap; push_cast; change coastE _*coastE _*(_*(2*_/_))=_; -- tune Pi smul.
 ring_nf; simp; ring
include h p s u q
lemma opportunity (l:-T+20 < inner ℝ N r) (k:inner ℝ N r< -20): HasSum (fun n:ℤ=> spectral (Z (V n)) r) (rays T δ P N r):=by
 let z:=inner ℝ N r; let Y':= coastE (inner ℝ P r); simp_rw [Pi.hasSum]; intro i; simp_rw [picture _ _ ht hm]; have hv:= (((steady h α p u s P N ht q z l k).mul_left (brushQ P i)).sub ((level h α p u s P N ht hm q z l k).mul_left (I*brushQ N i))).mul_left Y'
 rw [show rays T δ P N r i=Y'* (brushQ P i* (Φ) z-𝕀 *brushQ N i*((Χ U)*(Χ η)*(errata P N η z-C*errata P N (-η) z))) from ?_]; exact hv; unfold Y' z rays shaft plateF; simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply, smul_eq_mul,ofReal_neg]; ring
#print axioms opportunity
#print axioms derivP
end YM.CF.May.Lunar
