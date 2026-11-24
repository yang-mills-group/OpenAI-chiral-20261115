import YM.SU5.FiniteGaugeData.Indigo.Arabic
import YM.SU5.FiniteGaugeData.LapisQ.Feon
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
open CF.Indigo
namespace SpineV
open YM.SU5.FiniteGaugeData.Lapis Lumi
open LapisS LapisS.Stadium
open Chiffon.Prato
open YM.SU5.FiniteGaugeData.Indigo Taper
open Fock
namespace Licor
namespace Lychee
open Tint Eight.Bonbon
open YM.SU5.FiniteGaugeData.LapisQ WinkQ Exterior Work.F03 Cordon
open LapisS.ArenaQ
variable (H:RadioCity.Hypothesis Λ l g Y) (h:Real.exp 1 ≤ Λ.x)
variable {I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)(ℓ:ℕ)
variable (s i k:ℕ) {p ε c:ℝ}
local notation "G"=>SU.group
local notation "Kₜ"=> tent Y h
local notation "V₁" i:max s:max=> side Y i s
local notation "Σ"=>Λ.K.top.clip
local notation "W₁"=> Charm.W (tent Y h)
local notation "c₀" i:max k:max s:max=> coolant Y s i k
local notation "β" i:max k:max s:max=> (c₀ i k s)*Real.sqrt Σ.direct
local notation "η"=> nodeC (specialM Λ.R.L)
-- Beacon & central
lemma Raw_comm (K:Calibration)(f x:W K)(h:RawG K f) : f*x=x*f:=by
 apply Subtype.ext; funext m x'; obtain ⟨z,v⟩:= h m; change f.val m x'*x.val m x'= x.val m x'*f.val m x'; rw [v, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,mul_one,one_mul]
noncomputable abbrev AverPX (s:ℕ)(x:Cover)(t:ℝ)(q:0<t):= Lum Λ.R x t q Kₜ (zoomP Λ s)
noncomputable abbrev Snear (s:ℕ)(t:ℝ)(q:0<t):= Neo Λ.R t q Kₜ (zoomP Λ s)
-- price comparator
variable (x: Cover) (t:ℝ)(q:0<t)
local notation "P★" s:max=> AverPX Y h s x t q
local notation "Sa" s:max=> Snear Y h s t q
noncomputable abbrev priceN (i k s:ℕ) (t:ℝ)(q:0<t)(T: Lumi.Duct SU.group XiCore):= wattle Y T s i k 1
-- t unused, notation.Z
lemma prep_P (T: Lumi.Duct SU.group XiCore): priceN Y i k s t q T=WinkQ.sell (cure Y s i k) Λ.V.W.reserve (coolant Y s i k*Real.sqrt Λ.K.top.clip.direct) T:=rfl
lemma psiL(K:Calibration){x x' y y' z z':ℂ}{t C:ℝ}(p:‖x-x'‖≤t)(q:‖y-y'‖ ≤ t)(u:‖z-z'‖≤ t)(c: ‖x'‖ ≤ C)(d: ‖y'‖ ≤ C): ‖(z-x*y) - (z'-x'*y')‖ ≤ (1+(t+2*C))*t:=by
 have he:0 ≤ t:=(norm_nonneg _).trans p; have hx:‖x‖≤t+C:=(norm_le_norm_sub_add x x').trans (add_le_add p c); rw [show z-x*y-(z'-x'*y')=z-z' - (x*(y-y')+(x-x')* y') from (by ring)]; apply (norm_sub_le ..).trans; refine (add_le_add u ((norm_add_le ..).trans (add_le_add ((norm_mul ..).trans_le (mul_le_mul hx q (norm_nonneg _) ((norm_nonneg _).trans hx))) ((norm_mul ..).trans_le (mul_le_mul p d (norm_nonneg _) he))))).trans_eq ?_; ring
abbrev Υ₉(X Y Z :ℂ) := Z-X*Y
include K R A H
lemma verdict(e:0<ε) : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ,Sphere Y h K R A Φ → ‖Beacon Y h (Φ s) (AverPX Y h s x t q) (Snear Y h s t q) - (↑(WinkQ.Amen (cure Y s (u i) (v k)) Λ.V.W.reserve (β (u i) (v k) s) x t q):ℂ)‖ ≤ ε:=by
 let P:= Nirv x t q; let S:= Kayak x t q; let T:= Korn x t q; let C:=t⁻¹; have hC:0<C:=inv_pos.mpr q; let y:= min 1 (ε/(2+2*C)); have h0:0 < 2+2*C:=by positivity
 have ht:0<y:=lt_min zero_lt_one (div_pos e h0); have hv: (1+(y+2*C))*y ≤ ε:= calc
    _ ≤ (2+2*C)*y:= mul_le_mul_of_nonneg_right (by linarith only [min_le_left (1:ℝ) (ε/(2+2*C))]) ht.le
    _ ≤ _:=by rw [mul_comm]; exact (le_div_iff₀ h0).mp (min_le_right ..)
 filter_upwards [Stadium.witness Y H h K R A T (η) ht, Stadium.witness Y H h K R A P (η) ht, Stadium.witness Y H h K R A S (η) ht] with s z t' k; filter_upwards [z,t',k] with i z t' k'; filter_upwards [z,t',k'] with k z t' k' Φ φ;
 let j:= u i; let m:= v k; let f:= (priceN Y j m s t q); let g(U:W₁):= Φ s U; let A':= AverPX Y h s x t q; let B:= Snear Y h s t q; have ha: beacon Y h S (η) s 1=A':=rAura Λ.R x t q Kₜ _ _; have hb: beacon Y h T (η) s 1 = B:= aAura Λ.R x t q Kₜ _ _; have hp: beacon Y h P (η) s 1=A'*B:=(show _=B*A' from pAura Λ.R x t q Kₜ _ _).trans (Raw_comm Kₜ _ _ (rareR Λ.R t q Kₜ _)) -- `(..)` inferred forall issues.T.
 let heS:= k'.2.2.2.2 Φ 1 φ; let heT:= z.2.2.2.2 Φ 1 φ; let heP:= t'.2.2.2.2 Φ 1 φ; have hs: |f S|≤ C:= Stadium.sales_bound ..; have ht: |f T| ≤ C:=Stadium.sales_bound ..
 unfold Amen; simp_rw [← prep_P Y s (u i) (v k) t q] -- tune indices defeq u i (not rw)
 change ‖(g (A'*B) - g A'*g B) - ((↑ (f P - f T*f S)):ℂ)‖ ≤ ε; push_cast; rw [mul_comm ((f T:ℝ):ℂ) _]; apply le_trans _ hv; exact psiL Kₜ (ha ▸ heS) (hb ▸ heT) (hp▸heP) (by rw [Complex.norm_real]; exact hs) (by rw [Complex.norm_real]; exact ht)
set_option maxHeartbeats 630000
private lemma fitP(s L:ℕ): ∀ᶠ i:ℕ in atTop, L≤ (More (side Y (u i) s)).val:=by
 filter_upwards [((c_grows Kₜ).comp ((momentum Y s).comp K.pick.grow_i.tendsto_atTop)).eventually_ge_atTop L] with i p; change L≤ ((tent Y h).c (momentm Y (u i) s)).val at p; rw [show side Y (u i) s= (tent Y h).c (momentm Y (u i) s) from (terrain Y h _ _).symm]; change L≤ _*2; exact p.trans (le_mul_of_one_le_right (Nat.zero_le _) (by omega))
#print axioms verdict
lemma glitter : ∃ c t₀:ℝ,0<c∧0<t₀∧∃ D:ℕ,∀ t:ℝ,∀ q:0<t,t≤ t₀→ ∀ᶠ s:ℕ in atTop,∃ x∈ marketZ D, lapse ℓ x ∧ ∀(Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ → c≤ (Beacon Y h (Φ s) (AverPX Y h s x t q) (Snear Y h s t q)).re:=by
 letI:= ArenaQ.color_funds; let Q:=Λ.K; let ρ:=Λ.V; let r:=Real.sqrt Σ.direct; have hp: 0<r:=Real.sqrt_pos.mpr Λ.K.top.clip.quadratic_pos
 obtain ⟨δ,t₀,u_,t',N,D,E⟩:= WinkQ.CuspW ℓ Λ.K.η Λ.V.W.parcel Λ.K.C (2*r) (r/2) ρ.W.reserve (half_pos hp); let y:=δ/2; have hy:0<y:=half_pos u_; refine ⟨y,t₀,hy,t',D,fun t q r' =>?_⟩; let S:=marketZ D
 filter_upwards [S.eventually_all.mpr (fun i _=> verdict Y H h K R A i t q hy), Stadium.witness Y H h K R A (Korn 0 t q) (η) hy] with s m p
 obtain ⟨i,v₀,p,a⟩:= ((S.eventually_all.mpr m).and (p.and (fitP Y H h K R A s N))).exists; obtain ⟨k,vB,p⟩:= ((S.eventually_all.mpr v₀).and p).exists
 let Q0:= Y.uv (v k) -s; let ζ:= (β (u i) (v k) s); have hγ:r/2 ≤ ζ:= le_trans (by ring_nf; exact le_of_eq (by ring) : r/2 ≤ (1/2)*r) (mul_le_mul_of_nonneg_right p.2.2.2.1 hp.le)
 have hZ:ζ≤2*r:=mul_le_mul_of_nonneg_right (le_of_abs_le p.2.2.1) hp.le
 obtain R0:= Λ.V.L.roof Q0; obtain ⟨j,w,u₁,x⟩:= E (cure Y s (u i) (v k)) (Λ.V.L.mood Q0) (Λ.V.L.tied Q0) R0.1.2.1 Λ.K.width ζ hγ hZ a; refine ⟨j,w,u₁,fun Φ p=> ?_⟩; let b:= Beacon Y h (Φ s) (AverPX Y h s j t q) (Snear Y h s t q); let A':= WinkQ.Amen (cure Y s (u i) (v k)) Λ.V.W.reserve ζ j t q; have hl:δ≤ A':= x t q r'; have he:|(b-(↑A':ℂ)).re| ≤ y:= (Complex.abs_re_le_norm _).trans (vB j w Φ p); change y≤ b.re; rw [Complex.sub_re,Complex.ofReal_re] at he; linarith only [hl,(abs_le.mp he).1,(show y+y=δ from add_halves ..)]
#print axioms glitter
end Lychee
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
