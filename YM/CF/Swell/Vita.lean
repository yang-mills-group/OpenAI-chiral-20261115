import YM.CF.Swell.Stroke
import YM.CF.Mew.Tube
import YM.CF.Swell.Veil
import YM.CF.Swell.Muse
import YM.CF.Swell.Bark
import YM.CF.Neon.Hick
import YM.CF.Swell.Chill
import YM.CF.Swell.Yard
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
-- exchange ordinary anchor bank to incidence over all sites.Extra fuel.PSR.
variable {N:Side}{P:BudgetPoint} {K:ℕ}{c α Θ:ℝ}
open Py
open Neon
open Larch Oath
variable {B m: Side}{h K v:ℝ}(J:RegBudget (mid m B))
variable {I:Type}[LinearOrder I][Fintype I](i: I)(X:Key I→ RegBudget (mid m B))(x:I→ Seat (mid m B))(F:I→RegBudget (mid m B))(z:Mew.Key I)(V:Orbit (mid m B))
variable (V':∀ Y:Scree.Hub (mid m B),Hush x Y.val.2 (fun z=>X z Y))(p:∀ z∈hill I,ForgeB (X z) (filmK P (P.supportExponent+1+1)) P h (fun _=>K))(q:∀ Y U,River (fun z=>X z Y U))(hp:1 ≤h)
variable (O:I→ Site (mid m B))
variable (d0:X 0=0)(hσ:x=Cube.node ∘ O)
open Module Roots
-- deconjugate boot sensor. estimates BEFORE parameters.Report both reorder weights but boot 1 input raw enlarged.Fore.P.Wrap beyond 0? restrict λ.Wstrict.
variable (s t:ℝ)(u:0<s)(hP:1≤ h)(pT:0<t)
lemma sCap(i:Ξθ): InΦ (cue_Φ s h i):=⟨mind_A.smul_mem _ (Gior i).2.1.property,mind_B.smul_mem _ (Gior i).1.property,mind_C.smul_mem _ (Gior i).2.2.property⟩ -- maybe h implicit hp.
lemma subCh (x y:ArcΦ)(h:InΦ x)(p:InΦ y): InΦ (x-y):=⟨mind_A.sub_mem h.1 p.1,mind_B.sub_mem h.2.1 p.2.1,mind_C.sub_mem h.2.2 p.2.2⟩
abbrev tθ:= ρθ Gior
lemma tt0 :0<tθ:= μp_pos ..
def ΘS_F(s:ℝ):=s/(2*tθ)
variable (Φ:Ξθ→ ArcΦ)(vX:∀ i,InΦ (cue_Φ s h i+ Φ i))(eΦ:∀ i:Ξθ, ‖(Φ i).1‖ ≤ΘS_F s ∧ ‖(Φ i).2‖*h^2 ≤ ΘS_F s)
include vX
lemma infΚ(i:Ξθ): InΦ (Φ i):=by rw [← add_sub_cancel_left (cue_Φ s h i) (Φ i)]; exact subCh _ _ (vX _) (sCap s _)
omit vX
variable(hT:∀ i:Ξθ,InΦ (Φ i))
def boostE : BadgeΦ→ₗ[ℂ] BadgeΦ:= Gior.constr ℂ fun i=> recolor (Φ i) h s (hT i)
include hP u hT eΦ
lemma χweight (i:Ξθ): ‖boostE (h:=h) s Φ hT (Gior i)‖ ≤ 1/(2*tθ):=by
 let x:=Φ i; let z:= ΘS_F s; have hz:0< h:=zero_lt_one.trans_le hP; have hv:(s:ℂ)≠0:=Complex.ofReal_ne_zero.mpr u.ne'; let V0:=x.2.1; let k:ℂ:= (s:ℂ)⁻¹*(h:ℂ)^2; set y:=1/(2*tθ); unfold boostE; rw [Basis.constr_basis]; let T:= recolor x h s (hT i); have he:{E:Type}→ [NormedAddCommGroup E]→ [NormedSpace ℂ E]→ ∀ e:E,‖e‖*h^2≤ z→ ‖k • e‖≤ y:=by
    intro E _ _ e ht; unfold k; rw [norm_smul,norm_mul,norm_inv,norm_pow,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg u.le,Real.norm_of_nonneg hz.le,mul_assoc]; exact (inv_mul_le_iff₀ u).mpr (by rw [mul_comm (h^2)]; exact ht.trans_eq (by unfold z y ΘS_F; ring))
 change ‖T‖ ≤ y; rw [Prod.norm_def, Prod.norm_def]; let A:= x.2; have ht: ‖x.2‖*h^2≤ z:= (eΦ i).2; let f:↑mind_B:=⟨_,(hT i).2.1⟩; let v:↑mind_A:=⟨_, (hT i).1⟩; let c':↑mind_C:=⟨_,(hT i).2.2⟩; refine max_le (he f ?_) (max_le ?_ (he c' ?_))
 · exact (mul_le_mul_of_nonneg_right (norm_fst_le x.2) (sq_nonneg _)).trans ht
 · change ‖(s:ℂ)⁻¹ • v‖≤_; rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg u.le,inv_mul_le_iff₀ u]; exact ((eΦ i).1).trans_eq (by unfold ΘS_F y; ring)
 exact (mul_le_mul_of_nonneg_right (norm_snd_le x.2) (sq_nonneg _)).trans ht
abbrev glowA(s:ℝ) (Φ:Ξθ→ArcΦ)(hT:∀ i:Ξθ,InΦ (Φ i)) (h:ℝ):BadgeΦ→ₗ[ℂ] BadgeΦ:= LinearMap.id+ boostE (h:=h) s Φ hT
lemma Δquo :∃ F: BadgeΦ ≃ₗ[ℂ] BadgeΦ, F.toLinearMap=glowA s Φ hT h ∧ ∀ i, ‖F.symm i‖≤ 2*‖i‖:=by
 let L:= boostE (h:=h) s Φ hT; set T:=glowA s Φ hT h; have hx(x):‖L x‖≤ (1/2:ℝ)*‖x‖:=by have ht:=tt0; apply (perk_l Gior L (1/(2*tθ)) (by positivity) (χweight s u hP Φ eΦ hT) x).trans_eq; unfold tθ at *; field_simp
 have he(x):‖x‖≤ 2*‖T x‖:=by
    have ht:= norm_sub_norm_le x (-L x); have hv:x - -(L x)=T x:=by rw [sub_neg_eq_add]; rfl
    rw [hv,norm_neg] at ht; nlinarith only [ht,hx x]
 have h0: Injective T:=by intro x y p; have hh:=he (x-y); rw [map_sub,p,sub_self,norm_zero,mul_zero] at hh; exact sub_eq_zero.mp (norm_le_zero_iff.mp hh)
 let F:=LinearEquiv.ofBijective T ⟨h0,T.surjective_of_injective h0⟩; refine ⟨F,rfl,fun i=>?_⟩; exact (he _).trans_eq (congrArg (fun y=>2*‖y‖) (F.apply_symm_apply _))
def ζFare(K:BadgeΦ≃ₗ[ℂ]BadgeΦ)(s t:ℝ)(i j:Ξθ):ℂ:= (↑(t/s):ℂ) *Gior.equivFun (K.symm (Gior j)) i
abbrev mΘ:= Fintype.card Ξθ
def hc_P := (4*tθ) * ↑mΘ * Hπ+1
omit hP u hT eΦ in
lemma hcP_ge : 0 < hc_P:=by unfold hc_P; have h:=tt0; have hp:= hPπ; positivity -- include warning
variable(K':BadgeΦ≃ₗ[ℂ]BadgeΦ) (Qκ:K'.toLinearMap=glowA s Φ hT h)(uK:∀ x, ‖K'.symm x‖ ≤2*‖x‖)(Eκ:t*hc_P=s)
include pT Qκ uK Eκ
omit eΦ
abbrev κc(s t:ℝ):=t/s*(tθ*(2*Hπ))
lemma Φfrost(i j: Ξθ):‖ζFare K' s t i j‖ ≤ κc s t:=by
 unfold ζFare; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (div_nonneg pT.le u.le)]; refine mul_le_mul_of_nonneg_left ?_ (div_nonneg pT.le u.le); change ‖Gior.repr _ _‖≤ _; exact (pagan _ _ _).trans (mul_le_mul_of_nonneg_left ((uK _).trans (mul_le_mul_of_nonneg_left (basis_D _) (by norm_num))) tt0.le)
lemma duty_L : mΘ*κc s t≤ (1/2:ℝ):=by
 unfold hc_P at Eκ; have he:0≤tθ:=tt0.le; have hx:=hPπ; apply le_of_mul_le_mul_left (a:=s) _ u
 unfold κc; rw [show s*(↑mΘ*(t/s*(tθ*(2*Hπ))))= t*(↑mΘ*(tθ*(2*Hπ))) from (by field_simp)]; rw [← Eκ]; nlinarith only [pT]
-- rescale diagonal Phi kicks. note Ξ_θ finite all, no need Lie gauge here
lemma Θport(i:Ξθ) :
 (∑ j:Ξθ, ζFare K' s t j i • (cue_Φ s h j +Φ j))=cue_Φ t h i :=by
 let F:=tune_Φ s h; let V:ℂ:=((t/s:ℝ):ℝ); let P:=K'.symm (Gior i); have ht:0<h:=zero_lt_one.trans_le hP; have h0:(s:ℂ)≠0:=Complex.ofReal_ne_zero.mpr u.ne'; have h1:(h:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ht.ne'; have he(j):cue_Φ s h j+Φ j= F (K' (Gior j)):=by
    calc _ = F (Gior j+recolor (Φ j) h s (hT j)) := by rw [map_add,show F _= Φ j from release_h _ _ _ ht u _] -- pattern ambiguity
         _ = _:=congrArg F (by change _= K'.toLinearMap (Gior j); rw [Qκ,glowA,LinearMap.add_apply,boostE,Basis.constr_basis]; exact rfl)
 simp_rw [he]; unfold ζFare; let Y:=F.comp K'.toLinearMap; have ht':F (K' P)=F (Gior i):= by rw [K'.apply_symm_apply]
 rw [show ∑ j:Ξθ,_= V • F (K' P) from ?_]; swap; · simp_rw [show F (K' P)= Y P from rfl,mul_smul,←smul_sum]; change V • ∑ i:Ξθ,Gior.repr P i • Y (Gior i)= V • Y P; nth_rw 2 [←Gior.sum_repr P]; rw [map_sum]; refine congrArg (V • ·) (sum_congr rfl fun i _=>?_); rw [map_smul]
 rw [ht']; unfold F cue_Φ; let k:=Gior i; refine Prod.ext ?_ (Prod.ext ?_ ?_) -- tune H>0 .
 · change V • ((s:ℂ) • _)= (t:ℂ) • _; rw [smul_smul]; unfold V; rw [Complex.ofReal_div,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr u.ne')]
 · change V • ((↑(s/h^2):ℂ) • _)= (↑(t/h^2):ℂ) • _; rw [smul_smul]; congr 1; unfold V; push_cast; field_simp
 change V • ((↑(s/h^2):ℂ) • _)= (↑(t/h^2):ℂ) • _; rw [smul_smul]; congr 1; unfold V; push_cast; field_simp
end YM.CF.Swell
