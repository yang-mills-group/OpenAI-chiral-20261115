import YM.SU5.FiniteGaugeData.Indigo.KernelI
import YM.SU5.FiniteGaugeData.Stent.Sinfonia
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
variable (R:Patch)
open CF.Indigo
namespace SpineV
open YM.SU5.FiniteGaugeData.Lapis Lumi
open LapisS LapisS.Stadium
open Chiffon.Prato
namespace Licor
-- normalize Neon at Pyramid.
variable (h:Real.exp 1≤ Λ.x)(s:ℕ)(p:Patch)(r:ℝ)
local notation "Q"=> colorG
local notation "β"=> Stadium.boon Λ
local notation "Πx"=> Λ.K.top.clip
local notation "X₀"=> Cy Λ.R
local notation "Kₜ"=> tent Y h
local notation "𝓔"=> Nylon Λ.R
local notation "η"=> nodeC (specialM Λ.R.L)
abbrev Oicu(A':Fin 4→SU.group.Color):= ‖Obl A'‖^2
lemma lac : Lariat (Fin 4) Oicu:=by
 refine ⟨?_,fun A f=>?_⟩; · unfold Oicu Obl; fun_prop
 unfold Oicu Obl; simp only [← map_add, SU.group.norm_adjoint]
abbrev zoomP (Λ:Preparation)(s:ℕ):= Stadium.boon Λ s * Real.sqrt Λ.K.top.clip.direct
noncomputable abbrev Jeanne (K:Calibration) := suede lyre (nodeC (specialM Λ.R.L)) Oicu lac K (zoomP Λ s)
abbrev levyP (Λ:Preparation)(s:ℕ) := zoomP Λ s^2/colorG
noncomputable abbrev ace(K:Calibration): W K:= ((↑(levyP Λ s)):ℂ) • (1-Neon Λ false K)
-- implicit Λ index? def mentions Λ in body (lean section param must explicit?).
open Tint Bonbon
variable {K:Calibration}{q t ε C:ℝ}
lemma rL(r:ℝ)(X:Fin 4→ SU.group.Color): Obl (r • X)=r • Obl X:=by unfold Obl; simp only [Pi.smul_apply, smul_add]
lemma foot1 (U:LinksC): (cladF lyre (η) Oicu r) U= ((↑(r^2*‖Cy Λ.R U‖^2)):ℂ):=by
 unfold cladF Oicu; apply congrArg; rw [rL,norm_smul,mul_pow, Real.norm_eq_abs,sq_abs]
-- optics width
local notation "θ"=> zoomP Λ s
local notation "λx"=> levyP Λ s
include Y
lemma priceL : 0<zoomP Λ s:= mul_pos (Real.sqrt_pos.mpr (riseY Y s)) (Real.sqrt_pos.mpr (Πx).quadratic_pos)
lemma feeL : 0< levyP Λ s:= div_pos (pow_pos (priceL Y s) _) cg0
open Next.Rank
local notation "μω"=> μX Λ s
abbrev wageL (Λ:Preparation) := Real.sqrt Λ.K.top.clip.direct/(Next.Rank.strength Λ.K.top.clip/8) -- tune
lemma Wunit : 0 < wageL Λ := div_pos (Real.sqrt_pos.mpr (Πx).quadratic_pos) (div_pos (strength_pos _) (by norm_num))
lemma bill64(t:ℝ): zoomP Λ s * μX Λ s t = wageL Λ*t:=by
 let A':= cool_ι Λ s; let B:= strength (Πx); have hB: 0<B:=strength_pos ..; have hq: 0 < Real.sqrt (hat Λ.R.L Λ.x s):= Real.sqrt_pos.mpr (riseY Y s); unfold wageL zoomP Stadium.boon μX cool_ι; field_simp -- tune need clear `strength _ ≠0`. B def mismatch
lemma glassV(t:ℝ): levyP Λ s*μω t^2= (wageL Λ*t)^2/colorG:=by rw [←bill64 Y s t, mul_pow]; unfold levyP; ring -- division
variable (N:Side)(x:Fields (K.c N))
omit Y in
lemma JeanneX : (Jeanne (Λ:=Λ) s K).val N x= ((θ^2*‖Cy Λ.R (onC (K.c N) x.1)‖^2:ℝ):ℂ) • 1:=by
 rw [Jeanne,suede_read, foot1] -- may require x? scope
omit Y in
lemma aceV : (ace (Λ:=Λ) s K).val N x= ((λx:ℂ)*(1-Nylon Λ.R (onC (K.c N) x.1))) • 1:=by
 change (λx:ℂ) • ( (1:FC _) - Nylon Λ.R (onC (K.c N) x.1) • 1)=_; rw [mul_smul, sub_smul,one_smul]
noncomputable abbrev WideLake (Λ:Preparation) : Finset Cover:= rimS lyre (nodeC (specialM Λ.R.L)) ∪ fieldQ Λ.R.L ∪ carpet (cradle Λ.R)
omit Y
include Y
lemma Jloc : Locator Kₜ (Jeanne (Λ:=Λ) s Kₜ) (WideLake Λ):= locate_sub Kₜ (sup_skin lyre (η) _ _ _ lac) (Subset.trans subset_union_left subset_union_left)
lemma Aloc : Locator Kₜ (ace (Λ:=Λ) s Kₜ) (WideLake Λ):=locate_scale Kₜ _ _ (locW_sub Y h (WideLake Λ) 1 _ (locate_one ..) (locate_sub _ (loc_shunt ..) (Subset.trans subset_union_right subset_union_left)))
lemma Jrraw : RawG Kₜ (Jeanne (Λ:=Λ) s Kₜ) := raw_skin lyre (η) _ _ _ lac
lemma Araw : RawG Kₜ (ace (Λ:=Λ) s Kₜ):= RawG.scaleG (RawG.subG (RawG.oneG _) (fun N => ⟨fun U=>𝓔 (onC _ U),(fun _=>rfl)⟩)) _ -- annotation scope
local notation "s₀" s:max=> Jeanne (Λ:=Λ) s Kₜ
local notation "a₀" s:max=> ace (Λ:=Λ) s Kₜ
local notation "P₀"=>cradle Λ.R
local notation "y₀"=> WideLake Λ
open Bonbon.Tulle
variable (N:Side)(b:Fields ((tent Y h).c N))
lemma avaW (u:¬triggerM Y h s (cradle Λ.R) r N b.1): ‖zoomP Λ s • Cy Λ.R (onC _ b.1)‖ ≤ (4*wageL Λ)*r:=by
 rw [norm_smul,Real.norm_eq_abs, abs_of_pos (priceL Y s)]; refine (mul_le_mul_of_nonneg_left (curr_B _ _ u) (priceL Y s).le).trans_eq ?_; rw [← mul_assoc _,mul_comm _ (4:ℝ),mul_assoc,bill64 Y s]; ring
lemma July : Tulle Y h s (cradle Λ.R) 2 ((4*wageL Λ)^2) (Jeanne (Λ:=Λ) s Kₜ):=by
 refine ⟨sq_nonneg _,fun j u N x p=>?_⟩; rw [JeanneX,norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]; let V:= onC _ x.1; let A':= X₀ V; change θ^2* ‖A'‖^2 ≤ _; rw [← mul_pow]; apply (pow_le_pow_left₀ (mul_nonneg (priceL Y s).le (norm_nonneg _)) _ 2).trans_eq; · exact mul_pow ..
 let Q':= avaW Y h s j N x p; simpa only [norm_smul,Real.norm_eq_abs, abs_of_pos (priceL Y s)] using Q'
lemma Atlas : ∃ C:ℝ,0<C∧∀ s:ℕ, Tulle Y h s (cradle Λ.R) 2 C (a₀ s):=by
 obtain ⟨D,v,p⟩:= care_U Λ.R; let a:=wageL Λ; refine ⟨D*a^2/colorG,div_pos (mul_pos v (pow_pos (Wunit Y) 2)) cg0,fun s=> ⟨div_nonneg (mul_nonneg v.le (sq_nonneg _)) cg0.le,fun j u N x q=>?_⟩⟩;
 let L:= levyP Λ s; let F:= Nylon Λ.R (onC _ x.1); rw [aceV,norm_smul,norm_one,mul_one, norm_mul, Complex.norm_real,Real.norm_eq_abs, abs_of_pos (feeL Y s)]; change L*‖1-F‖≤_; rw [norm_sub_rev]; apply (mul_le_mul_of_nonneg_left (p _ _ q) (feeL Y s).le).trans_eq; rw [mul_left_comm,show L*(μX Λ s j)^2=_ from glassV Y s j]; unfold a; ring -- $implicit
open scoped Classical
lemma ASAP (e:0<ε)(q:ℕ)(q':0<q):∀ᶠ s:ℕ in atTop, Width Kₜ (insideM Y h s (cradle Λ.R) q ( (a₀ s) - (s₀ s))) ε:=by
 let a:=wageL Λ; have hA:0<a:= Wunit Y; let t:= (a*q)^2; have hQ:0<t:=by unfold t; positivity
 let D:= ε*colorG/t; obtain ⟨T,hT,b⟩:= hood_B Λ.R (show 0<D from div_pos (mul_pos e cg0) hQ); have ht:Tendsto (cool_ι Λ) atTop atTop:= Tendsto.const_mul_atTop (div_pos (strength_pos _) (by norm_num)) (Real.tendsto_sqrt_atTop.comp (Steam.horizons Λ.x (V:=Λ.V))) -- spell
 have hu:Tendsto (fun s :ℕ=>μX Λ s q) atTop (𝓝 0):= tendsto_const_nhds.div_atTop ht
 filter_upwards [hu.eventually (ge_mem_nhds hT)] with s p N x; let H:= ace (Λ:=Λ) s Kₜ; let F:= Jeanne (Λ:=Λ) s Kₜ; let S':= swatch Y h s (cradle Λ.R) q; let R':=levyP Λ s; let V:=onC _ x.1; let α:=colorG*‖Cy Λ.R V‖^2; have hx:= (feeL Y s); change ‖ ( (1:FC _)-S'.val _ _)*(H-F).val N x‖ ≤ _
 rw [show S'.val N x=_ from Bonbon.stroke Y h s _ q N x]; split_ifs with f; · rw [sub_self,zero_mul,norm_zero]; exact e.le
 rw [sub_zero,one_mul]; change ‖H.val N x-F.val N x‖ ≤_; unfold H F; rw [aceV,JeanneX]; let c:= Nylon Λ.R V; let y:= (c-1)+(α:ℂ); have hy: ‖y‖ ≤ D*(μX Λ s q)^2:= b V _ (div_nonneg (Nat.cast_nonneg _) (boostP Y s).le) p f
 have he:R'*α= zoomP Λ s^2*‖Cy Λ.R V‖^2:= by unfold α R' levyP; rw [←_root_.mul_assoc,div_mul_cancel₀ _ cg0.ne']
 rw [← sub_smul]; change ‖ ( (R':ℂ)*(1-c)- ( (zoomP Λ s^2*‖Cy Λ.R V‖^2:ℝ):ℂ)) • (1:FC _)‖≤_; rw [← he, Complex.ofReal_mul, show (R':ℂ)*(1-c)-(R':ℂ)*(α:ℂ)= -((R':ℂ)*y) from (by unfold y; ring), norm_smul,norm_one,mul_one,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]; refine (mul_le_mul_of_nonneg_left hy hx.le).trans_eq ?_; rw [mul_left_comm,show R'*(μX Λ s q)^2=t/colorG from glassV Y s _]; unfold D; have h:=cg0;  rw [show ε*colorG/t*(t/colorG)=(ε* (colorG/colorG))*(t/t) by ring, div_self h.ne', div_self hQ.ne',mul_one,mul_one]
#print axioms ASAP
#print axioms July
#print axioms Atlas
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
