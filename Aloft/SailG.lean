import Aloft.Gun
import Ridgetop.Marshal
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Ridgetop
local notation "γ" s:max x:max=> P.singleState 3 (stackW s) x
local notation "Ω"=>‖Ridgetop.visible‖
local notation "Z" n:max=> scaleY (hat P.par.R.L P.par.x (stackW n))
local notation "ℵ" n:max=> P.payday (stackW n)
local notation "r" d:max=> ((girder P d):ℝ)
variable (d:ℕ)(l m:ℕ)(x:P.Spectrum0 3)(w:Cover)
noncomputable abbrev sponsor(q:ℕ):ℝ:= (Z q)^2/(ℵ q)
noncomputable abbrev gem:ℂ:= expenseR P x (stackW d) w 0 (bootH P m d)
lemma gemR_stamp:
 let u:=sponsor P d; let v:=bodyT P (stackW d) (blazeF P m d w) true; let p:= bodyT P (stackW d) (deputize P d w) false
 ((u:ℂ)^2*gem P d m x w)= (γ d x) v-star ((γ d x) p) * (γ d x) p:=by
 intro u v p; let s:=stackW d; let q:= P.chartAll (bootH P m d); let l:=wp P s w; let k:=P.chartAll 0 ∘ P.reflectTest 3; have hv: v=((u:ℂ) • (k l))*((u:ℂ) • (q l)):=by
    unfold k; rw [Function.comp_apply,show P.reflectTest 3 l=wp P s (swapW w) from reflected_h P s w,wp_visits, show q l=wp P s (shuffleT P (bootH P m d) w) from wp_visits ..]; rfl
 rw [hv]; change (u:ℂ)^2*( (γ d x) (k l*q l)-star ((γ d x) l)*_)=_
 change _=(γ d x) (((u:ℂ) • _) * ((u:ℂ) • _)) - star ((γ d x) ((u:ℂ) • l)) * (γ d x) ((u:ℂ) • l)
 exact goth _ u l (k l) (q l)
where goth {T:Type}[CommRing T][Algebra ℂ T](f:T→ₗ[ℂ]ℂ)(i:ℝ)(p a b:T): (i:ℂ)^2*(f (a*b)-star (f p)*f p)=f (((i:ℂ)•a)*((i:ℂ)•b))-star (f ((i:ℂ)•p))*f ((i:ℂ)•p):=by simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,map_smul,smul_eq_mul,star_mul',Complex.star_def,Complex.conj_ofReal]; ring
private lemma tally {x y:ℂ}{q:ℝ}{c b e t:ℝ}{L:ℕ}(hc:1≤c)(he:0<e)(hB:0≤b)(hb:b ≤ c^L)(p:‖x-(q:ℂ)‖ *c^(8*L+6) ≤1)(v:‖y‖ *c^(8*L+6) ≤1)(ht:0 ≤t)(h:t≤e*b):
 ‖x-star y*y-(q:ℂ)‖ * t^8 ≤ 2*e^8*c⁻¹:=by
 have hp:=pow_le_pow_left₀ hB hb 8; rw [← pow_mul,mul_comm L] at hp
 have hf: b^8*c ≤ c^(8*L+6):=by rw [pow_add]; exact mul_le_mul hp (by simpa only [pow_one] using (pow_le_pow_right₀ hc (show 1 ≤6 by omega))) (by linarith) (by positivity)
 have ht':t^8*c ≤ e^8*c^(8*L+6):=by have H:=pow_le_pow_left₀ ht h 8; rw [mul_pow] at H; exact (mul_le_mul_of_nonneg_right H (by linarith)).trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left hf (by positivity)))
 have hy:‖y‖≤1:= (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hc)).trans v
 have H: ‖x-star y*y-(q:ℂ)‖ ≤ ‖x-(q:ℂ)‖+‖y‖:=by rw [sub_right_comm]; refine (norm_sub_le ..).trans (add_le_add_right ?_ _); rw [norm_mul,norm_star]; exact mul_le_of_le_one_right (norm_nonneg _) hy
 have hb:0<c:=zero_lt_one.trans_le hc
 have hm(d:ℝ)(s:0≤d)(g:d*c^(8*L+6) ≤1):d*t^8 ≤ e^8*c⁻¹:=by
    rw [← div_eq_mul_inv,le_div_iff₀ hb,mul_assoc]; exact (mul_le_mul_of_nonneg_left ht' s).trans (by nlinarith only [mul_le_mul_of_nonneg_left g (show 0≤e^8 by positivity)])
 exact (mul_le_mul_of_nonneg_right H (by positivity)).trans (by nlinarith only [hm _ (norm_nonneg _) p, hm _ (norm_nonneg _) v])
noncomputable abbrev storm:= ((Fintype.card SU.group.ColorIndex):ℝ)*32+2
lemma stormCost(d:ℕ): 1 ≤ storm:=by unfold storm; have he:=color₁; linarith
variable (e:1 ≤ m)(V:Enviro P x)
include V e
/-- CP8 long-wave comparison on actual x, now at any fixed ruler.Boot factor. -/
lemma dollar :∀ᶠ d:ℕ in atTop,∀ w:Cover,Enrolled P d (stairW d) w→ Ω/256 ≤ ‖gem P d m x w‖ *(sponsor P d)^2*(led P m d w)^8 ∧ ‖gem P d m x w‖ *(sponsor P d)^2*(led P m d w)^8 ≤ storm*Ω:=by
 obtain ⟨l,h⟩:=licensed P m
 let q:=8*l+6
 let a:ℝ:= (pollN P:ℝ)*4*m+2
 have ha:0 < a:=by unfold a; positivity
 have hv:0 < Ω:=norm_pos_iff.mpr Ridgetop.visibility
 have he:Tendsto (fun d:ℕ=> 2*a^8*(Z d)⁻¹) atTop (𝓝 0):=by simpa only [Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp (stages_q P)).const_mul (2*a^(8:ℕ))
 filter_upwards [h,sides P m e l (h.mono fun i t=>t.1),V l q,he.eventually (ge_mem_nhds (show 0 < Ω/256 from (by positivity))),feeRatio P] with d h hm t hp hw w v
 let c:= sponsor P d; have hx:0 ≤ c:= div_nonneg (sq_nonneg _) hw.1.le
 obtain ⟨w₁,w₂⟩:=h.2 w v
 let p:=quoteC P m l d w
 let α:ℂ:=(c:ℂ)^2 * gem P d m x w
 let Y:=γ d x; let y:= bodyT P (stackW d) (deputize P d w) false; let z:= bodyT P (stackW d) (blazeF P m d w) true; let k:= Z d; let l':=led P m d w
 have hq: ‖Y z-(p:ℂ)‖ *k^(8*l+6) ≤1:=t (blazeF P m d w) true w₁
 have hQ:=t (deputize P d w) false w₂; change ‖Y y-(boonW P d l (8*l+6) w:ℂ)‖ * k^(8*l+6)≤1 at hQ; rw [boon_empty] at hQ; rw [Complex.ofReal_zero,sub_zero] at hQ
 have Hs : ‖α-(p:ℂ)‖ * l'^8 ≤ Ω/256:=by
    rw [show α= Y z-star (Y y)*Y y from gemR_stamp P d m x w]
    exact (tally (summitT _) ha (Nat.cast_nonneg _) h.1 hq hQ ((Nat.cast_nonneg _).trans (ledG P m d w v e)) (mandate P m d w v e|>.2)).trans hp
 have ho:=hm w v; change _ ≤ |p| *l'^8∧|p| *l'^8 ≤ _ at ho
 rw [show ‖gem P d m x w‖ *c^ (2:ℕ)=‖α‖ from (by unfold α; rw [norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg hx,mul_comm])]
 have H1:= norm_sub_norm_le (p:ℂ) α; have H2:= norm_sub_norm_le α (p:ℂ); rw [norm_sub_rev] at H1; rw [Complex.norm_real,Real.norm_eq_abs] at H1 H2; change Ω/256 ≤ ‖α‖ *l'^8 ∧ ‖α‖ * l'^8 ≤ storm*Ω
 unfold storm; constructor <;> linarith only [Hs,ho.1,ho.2,hv,mul_le_mul_of_nonneg_right H1 (show 0 ≤ l'^ (8:ℕ) by positivity),mul_le_mul_of_nonneg_right H2 (show 0 ≤ l'^ (8:ℕ) by positivity)]
#print axioms dollar
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
