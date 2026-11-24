import YM.CF.Phase.Global
import YM.CF.Fock.Salary

/-! Prefactor sizes and reached state, before the local subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock NormedSpace
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def fund (m B : Side) (c : Part m B) (U : Skin m B) (x : Cue m) := (netsal (lens m B c U) (pair m B U x) : ℂ)+(accord m B c U x).im * Complex.I
def wiel (m B : Side) (c : Part m B) (U : Skin m B) := (frame matter (links U) c).H
def sheet (m B : Side) (c : Part m B) (t : ℝ) (U : Skin m B) (x : Cue m) := shot (wiel m B c U) (pair m B U x) t
def energ (m B : Side) (c : Part m B) (U : Skin m B) := (wiel m B c U * lens m B c U).trace
section
variable (c : Part m B) {e : ℝ} (b : Room B e) {U : Skin m B} (g : Guard U e) {x : Cue m} (h : ZeroF m B U x)
include b g
lemma wiel_ok : Safe (wiel m B c U) := by exact band matter _ c (plaq_lens b g)
include h
lemma kappa : Valid (m:=m) (B:=B) (lens m B c U) (pair m B U x) := bow_val c b g (show Verified _ _ margin _ _ {0} from h) (stick_in _ (Finset.mem_singleton_self 0))
lemma net_vol : ‖shrinkV (lens m B c U) (pair m B U x)-1‖≤7/9 := by
  obtain ⟨p,-,e⟩ := kappa c b g h
  exact sat_gap (lensP c b g) ⟨_,p⟩ (show ‖stage _ _-pair m B U x‖≤1/3 by rw [stage_gap (lensP c b g)]; exact e)
lemma salary : Real.exp (netsal (lens m B c U) (pair m B U x))=‖filled (lens m B c U) (pair m B U x)‖ := to_sal (lensP c b g) (kappa c b g h).2.1 (lt_of_le_of_lt (net_vol c b g h) (by norm_num))
lemma afield : filled (lens m B c U) (pair m B U x)=Complex.exp (fund m B c U x) • sound m B c U := by
  let a := accord m B c U x; let F := filled (lens m B c U) (pair m B U x); let f := netsal (lens m B c U) (pair m B U x)
  rw [sonic c b g h,sized,unscaled,norm_smul,Complex.norm_exp,←salary c b g h,←Real.exp_add,Complex.ofReal_exp]; simp only [smul_smul]
  change F=(Complex.exp (fund m B c U x)*( (Complex.exp (((-a).re+f):ℝ))⁻¹ * Complex.exp (-a))) • F
  rw [←Complex.exp_neg,←Complex.exp_add, ←Complex.exp_add]
  change F=Complex.exp ((f:ℂ)+(a.im:ℂ)*Complex.I+(-((((-a).re+f):ℝ):ℂ) + -a)) • F
  have he : ((f:ℂ)+↑a.im*Complex.I+(-((((-a).re+f):ℝ):ℂ) + -a))=0 := by apply Complex.ext <;> simp <;> ring
  rw [he,Complex.exp_zero,one_smul]
theorem produced (t : ℝ) : acts (quant (grow (wiel m B c U) t)) (pairWave (pair m B U x))=Complex.exp ((t:ℂ)*energ m B c U+fund m B c U x) • acts (exp (sheet m B c t U x)) (sound m B c U) := by
  rw [pushed (wiel_ok c b g) (kappa c b g h).2.1 (chain_unit c b g h)]
  change _ • acts (exp (sheet _ _ _ _ _ _)) (filled (lens m B c U) (pair m B U x))=_; rw [afield c b g h,Complex.exp_add,map_smul,smul_smul]; rfl
lemma covered_cash (k : Site (Domain m B)→E) : fund m B c (gauge k U) (partner m B k x)=fund m B c U x := by
  have ht := salary c b (g.cov k) ((twist_0 U x k).mpr h)
  have hb := salary c b g h
  unfold fund; rw [accord_g c b k x g h]
  rw [show netsal _ (pair _ _ (gauge k U) (partner m B k x))=netsal _ (pair m B U x) from Real.exp_injective (ht.trans (Eq.trans (by rw [pair_g,lens_g c b g,filled_twist, act_unit_norm]) hb.symm))]
end
section replay
variable (c d : Part m B) {e : ℝ} (b : Room B e) {U W : Skin m B} (g : Guard U e) (f : Guard W e) {r : Zone} {x y : Sq} (X : x∈zone r) (Y : y∈zone r) (J : UNI (Mind m B)) {s t : ArrayF m} (h : Verified m B margin U s r) (k : Verified m B margin W t r)
include b g f h k X Y
lemma swung (p : lens m B d W=twist J (1-lens m B c U)) (q : ∀ x∈zone r, bow m B W t x=congrC J (bow m B U s x)) (w : ∀ z∈zone r,(bow m B U s x).det=(bow m B U s z).det) :
    ray m B d W t x y=star (ray m B c U s x y) := by
  let F := ray m B d W t x; let L := ray m B c U s x
  have he : ContinuousOn F (zone r) := ray_contzone d b f k X
  have hl : ContinuousOn L (zone r) := ray_contzone c b g h X
  suffices H : ∀ z∈zone r, 2*F z= (2:ℂ)*star (L z) by exact mul_left_cancel₀ (by norm_num) (H y Y)
  apply carry_log (cube_path r).isPreconnected (continuousOn_const.mul he) (continuousOn_const.mul hl.star) x X
  · intro z hz
    obtain ⟨U',T,H⟩ := spot_projection _ (lensP c b g)
    let A := fun x=> bow m B U s x; let R := fun z=> (congrC (star U') (A z)).det
    have H₁ := point_log c b g h U' T H X hz
    have HE : lens m B d W=twist (J*U') (cutM Tᶜ) := by rw [p,H, Fock.twin, dim_cut T, map_sub (twist U'),map_one (twist U')]
    have H₂ := point_log d b f k _ _ HE X hz; rw [q x X,q z hz,frame_shift,frame_shift] at H₂
    have ht i (l:i∈zone r) : stratum U' Tᶜ (A i)^2=R i * star (stratum U' T (A i)^2) := by
      obtain ⟨p,g,-⟩ := bow_val c b g h l
      exact compStratum U' (⟨A i,p⟩:UNI (Mind m B)) T g
    have hn : R x=R z := by simp only [R,A,congrC,Matrix.det_mul,w z hz]
    have hk : stratum (J*U') Tᶜ (bow m B W t x) ≠ 0 := by apply strata_gap; rw [←HE]; exact bow_full d b f k X
    rw [q _ X,frame_shift] at hk
    apply mul_right_cancel₀ (pow_ne_zero 2 hk)
    change Complex.exp (2*F z) * stratum U' Tᶜ (A x)^2=Complex.exp (2*star (L z)) * stratum U' Tᶜ (A x)^2
    have ha : Complex.exp (2*F z) * stratum U' Tᶜ (A x)^2=stratum U' Tᶜ (A z)^2 := by rw [two_mul, Complex.exp_add,←pow_two,←mul_pow,show Complex.exp (F z)*_=stratum U' Tᶜ (A z) from H₂]
    rw [ha,ht x X,ht z hz, hn, mul_left_comm]; congr 1
    rw [show Complex.exp (2*star (L z))=star (Complex.exp (2*L z)) by rw [show 2*star (L z)=star (2*L z) by simp [mul_comm]]; simp [Complex.exp_eq_exp_ℂ, star_exp]]
    rw [←star_mul',two_mul,Complex.exp_add,←pow_two,←mul_pow,show Complex.exp (L z)*_=stratum U' T (A z) from H₁] -- tune
  have hA : F x=0 := by have H := ray_add d b f k X X X; change F x=F x+F x at H; exact (add_eq_left.mp H.symm)
  have hB : L x=0 := by have H := ray_add c b g h X X X; change L x=L x+L x at H; exact add_eq_left.mp H.symm
  change 2*F x=2*star (L x); rw [hA,hB,star_zero]
end replay
end YM.CF.Phase
