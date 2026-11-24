import Zephyr.Chern.Garnet
import YM.CF.Onyx.Opal
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern
namespace IndexMag
open YM YM.Lattice YM.CF.Fir YM.CF YM.CF.Jill Silk YM.Laurent Filter Topology MeasureTheory NormedSpace
open YM.Stationary
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Classical Topology _root_.Pointwise
open GaussianFourier
local notation "η"=> boundsEarth
local notation "pi!"=> Real.pi
local notation "Φ"=> exileE
variable {j:ℕ} {r:Male → Streams}(L:Looming j r)(H:1≤j)(M:Male)
local notation "Q"=> r M
lemma boundEarth {p:Gaia}(h:p∈η): Bound Real.pi (Φ p):= by
 refine pi_norm_le_iff_of_nonneg Real.pi_pos.le|>.2 (fun i=>?_); rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨((show ∀ i,(Φ p i)∈Set.Ioc (-Real.pi) Real.pi from h) i).1.le, ((show ∀ i,(Φ p i)∈Set.Ioc (-Real.pi) Real.pi from h) i).2⟩
abbrev dial (p:Gaia):Brill:= radians (Φ p)
def dimples (p:Gaia):ℝ:= (shell j M.val (tmap (exileE p))).re
abbrev reserveJ (p:Gaia):ℂ:= E (dial p) (Q 0)
lemma cast_dial : Continuous dial:=by
 apply continuous_pi; intro i; change Continuous (fun p:Gaia=> ((p i/(2*pi!) :ℝ) :UnitAddCircle)); fun_prop
local notation "ψ"=> dimples (j:=j) M
local notation "T"=> reserveJ (r:=r) M
include L
lemma signal_price {p:Gaia}(h:p∈η): reserveJ (r:=r) M p= (↑(1-2*(ψ p)):ℂ):=by
 unfold reserveJ; let w:= boundEarth h; have hx: dial p= radians (Φ p):=rfl; rw [hx,L.plays M (Φ p) w]; have he:= (signal_round j M _ w).2.1; apply Complex.ext
 · rw [Complex.ofReal_re]; change (1-2*shell j M.val (tmap (Φ p))).re= 1-2* _; simp; rfl
 rw [Complex.ofReal_im]; exact he
lemma dsmile {p:Gaia}(x:p∈η): dimples (j:=j) M p ≤ 1:=by
 let W:= T p; have hv:(-1:ℝ) ≤ W.re:=(L.round M).2 (dial p)|>.2; unfold W at hv; rw [signal_price L _ x,Complex.ofReal_re] at hv; linarith
omit L
lemma norm_ex (x:Gaia) : ‖Φ x‖≤ ‖x‖:= orbit_at _
lemma norm_pond (x:Gaia) : ‖x‖≤2*‖Φ x‖:=by
 have hx:= Onyx.moor_z (Φ x); rw [Onyx.moor,MeasurableEquiv.symm_apply_apply] at hx; exact hx
include H in
lemma lower_earth : ∃ K> (0:ℝ), ∀ (M:Male)(p: Gaia), p∈η→ K*‖p‖^2 ≤ dimples (j:=j) M p:=by
 obtain ⟨b,hb,P⟩:=Onyx.cane (A:=crop) (x:=RayH.x) (fun _=>rfl) RayH.cap RayH.M H
 refine ⟨b/4,by positivity,fun M p hp =>?_⟩; by_cases h:p=0; · subst p; unfold dimples; rw [show tmap (Φ 0)=0 from rfl,shell_origin]; simp
 let x:= Φ p; have hx:x≠0:=fun e=> h (exileE.injective e) -- 0 defeq?
 let i:RayH:= ⟨M,x,boundEarth hp,norm_pos_iff.mpr hx⟩; have hu:b*‖x‖^2 ≤ dimples (j:=j) M p:= P i
 refine le_trans ?_ hu; have ht: ‖p‖^2≤(2*‖x‖)^2:=pow_le_pow_left₀ (norm_nonneg _) (norm_pond p) 2; linarith only [mul_le_mul_of_nonneg_left ht hb.le] -- maybe le_trans
include H in
lemma dclose : ∃ K> (0:ℝ),∀ (M:Male) (p:Gaia), p∈ η→ ‖dimples (j:=j) M p-(1/4:ℝ)*‖p‖^2‖≤ K*‖p‖^3:=by
 obtain ⟨C,p,v⟩:= Onyx.up_t H; refine ⟨C,p,fun M q h=>?_⟩; let B:= (1/4:ℝ)* ‖q‖^2; let Z:= shell j M.val (tmap (Φ q)); have hv:(1/4:ℂ)*prodM (tmap (Φ q)) (tmap (Φ q))=(B:ℂ):=by rw [show ∀ p:Gaia, prodM (tmap (Φ p)) (tmap (Φ p))= _ from fun p=> Onyx.zio p]; unfold B; push_cast; rfl -- universe aberration
 let u:=(v M _ (boundEarth h)).1; change ‖Z-(1/4:ℂ)*prodM (tmap (Φ q)) (tmap (Φ q))‖ ≤ C*‖Φ q‖^3 at u; rw [hv] at u; unfold dimples; change ‖Z.re-B‖≤ _; rw [Real.norm_eq_abs,← show (Z-(B:ℂ)).re=Z.re-B from rfl]; exact (Complex.abs_re_le_norm _).trans (u.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_ex _) _) p.le))
#print axioms lower_earth
#print axioms dclose
abbrev balljac(f:Streams) (p:Gaia):ℂ:= E (dial p) (jac f)
lemma earth_globe(f:Brill→ℂ): (∫ p, f p ∂globe Axis)= (cartWeight:ℂ)*∫ p:Gaia in boundsEarth, f (dial p):=by
 let c:=2*Real.pi; have hc:0<c:=by unfold c; positivity
 let a(_ : Axis):= -(1/2:ℝ) -- bug preceding
 let S : Set (Axis→ℝ):= {x|∀ i,x i∈ Set.Ioc (a i) (a i+1)}; have he(x:Axis→ℝ): Laurent.dress Axis x = radians (c • x):=by apply congrArg (Laurent.dress Axis); funext i; change x i = (c*x i)/c; field_simp
 have hS:c • S=cradle:=by
    ext p; rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']; have he i : p i/c ∈ Set.Ioc (a i) (a i+1) ↔ p i ∈ Set.Ioc (-Real.pi) Real.pi := by rw [Set.mem_Ioc,Set.mem_Ioc, lt_div_iff₀ hc,div_le_iff₀ hc]; unfold a c; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    change (∀ i, (c⁻¹ • p) i∈ _)↔∀ i,_; simp only [Pi.smul_apply,smul_eq_mul,inv_mul_eq_div,he]
 rw [show (∫ p,f p ∂globe Axis)= ∫ p in S,f (Laurent.dress _ p) from UnitAddTorus.integral_preimage f a]; simp_rw [he]
 change (∫ x : Axis→ℝ in S, (f ∘ radians) (c • x))= _; rw [Measure.setIntegral_comp_smul_of_pos (f:= f ∘ radians) MeasureTheory.volume S hc]; rw [show Module.finrank ℝ (Axis→ℝ)=4 from Module.finrank_fin_fun ℝ,hS]
 let T':= EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis; have h:Measure.map exileE MeasureTheory.volume=MeasureTheory.volume:=T'.map_eq; rw [←h,setIntegral_map_equiv]; simp only [Complex.real_smul]; rfl
#print axioms earth_globe
end IndexMag
end Zephyr.Chern
