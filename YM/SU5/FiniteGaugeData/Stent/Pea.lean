import YM.SU5.FiniteGaugeData.Stent.Vellum
import YM.SU5.FiniteGaugeData.Stent.Taffy
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
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
open Succulent
section
-- avoid factorization on test language using dense masks. Not assuming Φ is positive on gauge-only.
local notation "η"=> fieldQ Λ.R.L
noncomputable def marble (n:ℕ):ℝ:= 1/((n:ℝ)+1)
noncomputable def rollPlus (n:ℕ)(z:ℂ):ℝ:=marble n+‖z‖^2
noncomputable def caput (n:ℕ)(c z:ℂ):ℂ:= star (z-c)/(rollPlus n (z-c):ℂ)
lemma warmer(n:ℕ):0 < marble n:=by unfold marble; positivity
lemma rollPos (i:ℕ)(z:ℂ):0<rollPlus i z:= (warmer i).trans_le (le_add_of_nonneg_right (sq_nonneg _))
lemma cap_cont (n:ℕ)(c:ℂ): Continuous (caput n c):=by unfold caput rollPlus; apply Continuous.div₀ <;> (first | fun_prop | exact fun x=>Complex.ofReal_ne_zero.mpr ((rollPos n (x-c)).ne'))
-- residual functions with honest sup bounds Π & convergence. apply *shunt_more*.
noncomputable def regnant (n:ℕ)(c:ℂ)(z:ℂ):ℂ:= 1-caput n c z*(z-c)
lemma reg.cont(n:ℕ)(c:ℂ):Continuous (regnant n c):= continuous_const.sub ((cap_cont n c).mul (continuous_id.sub continuous_const))
variable (v:ℂ)
lemma reg.chance(n:ℕ)(z:ℂ) : regnant n v z= ((marble n/rollPlus n (z-v):ℝ):ℂ):=by
 let x:=z-v; let t:= rollPlus n x; have he: ((t:ℝ):ℂ)≠0:= Complex.ofReal_ne_zero.mpr ((rollPos ..).ne'); unfold regnant caput; let U:= marble n; let V:ℝ:= ‖x‖^2; change 1-star x/(t:ℂ)*x= ((U/t:ℝ):ℂ); rw [Complex.ofReal_div]; rw [div_mul_eq_mul_div,sub_div' he, one_mul, div_left_inj' he, mul_comm (star x)]; rw [Complex.star_def,Complex.mul_conj,←Complex.sq_norm,←Complex.ofReal_sub]; unfold t rollPlus; rw [add_sub_cancel_right] -- div spelling
lemma reg.weight(i:ℕ)(z:ℂ):‖regnant i v z‖≤1:=by
 rw [reg.chance]; have h:0<rollPlus i (z-v):= rollPos ..; have hz:= warmer i; rw [Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤ marble i/rollPlus i (z-v))]; exact (div_le_one h).mpr (le_add_of_nonneg_right (sq_nonneg _))
lemma reg.limit (z:ℂ)(h:z≠v):Tendsto (fun i=> regnant i v z) atTop (𝓝 0):=by
 let x:ℝ:= ‖z-v‖^2; have h:x≠0:= pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)); have hp:Tendsto marble atTop (𝓝 0):= tendsto_one_div_add_atTop_nhds_zero_nat; simp_rw [reg.chance]; let u:= Complex.ofRealCLM; refine u.map_zero ▸ u.continuous.continuousAt.tendsto.comp (?_ ); exact zero_div (a:=x) ▸ (hp.div (zero_add x ▸ hp.add_const x) h) -- tune CLM & zero.Div
#print axioms reg.limit
end
section
open Tint Next.Rank
variable (h':Real.exp 1≤Λ.x)
local notation "Kₜ"=> (tent Y h')
variable (s i:ℕ)(z:ℂ)
local notation "N"=> side Y i s
local notation "η"=> fieldQ Λ.R.L
local notation "Nₛ"=> Neon Λ false Kₜ
noncomputable def rackW (Λ:Preparation)(K:Calibration)(b:ℂ)(n:ℕ) := shunt K false (caput n b ∘ Nylon Λ.R) (Anorak.paint (Nylon Λ.R) (locketA Λ.R Λ.V.tallX) _ (cap_cont n b)) -- Qpainting
noncomputable def ebony (Λ:Preparation)(K:Calibration)(b:ℂ)(n:ℕ) := shunt K false (regnant n b∘ Nylon Λ.R) (Anorak.paint (Nylon Λ.R) (locketA Λ.R Λ.V.tallX) _ (reg.cont n b))
local notation "τ" n:max=> ebony Λ Kₜ z n
lemma Eboracum (n:ℕ): ebony Λ Kₜ z n=1-(rackW Λ Kₜ z n)*(Neon Λ false Kₜ-z • 1):=by
 apply Subtype.ext; funext i x; let r:= (tent Y h').c i; let y:= onC r x.1; let t:= Nylon Λ.R y; let u:= caput n z t; change (1-u*(t-z)) • (1:FC (Single r))=1-u • (1:FC _) * (t • 1-z • 1); rw [← _root_.sub_smul,Algebra.smul_mul_assoc, one_mul, smul_smul, _root_.sub_smul,one_smul] -- order `u • (…) * ...` smul RHS parsed correct?
lemma E_loc(n:ℕ): Locator Kₜ (ebony Λ Kₜ z n) (fieldQ Λ.R.L):= loc_shunt ..
lemma E_price(n:ℕ): ‖ reading Kₜ η (ebony Λ Kₜ z n) (E_loc Y h' z n)‖≤1:=by
 obtain ⟨i,h⟩:= (roomy_sides (fieldQ Λ.R.L) (tent Y h')).exists; apply offered_bound _ _ _ (roomy_hosp _ h); intro v; rw [reading_p]; let t:= Nylon Λ.R (onC _ v.1); change ‖(regnant n z t) • (1: FC _)‖≤_; rw [norm_smul,norm_one,mul_one]; exact reg.weight ..
lemma symbolic {X' Y':ℕ→ W Kₜ}{S:Finset Cover} {p:∀ n, Locator (tent Y h') (X' n) S} (t:η ⊆ S)(e:∀ i (v:Orbit (side Y i s)),Tendsto (fun n=> shapeA Y h' s i v (Y' n)) atTop (𝓝 (shapeA Y h' s i v (Y' 0)))) (g:∀ n:ℕ,X' n=ebony Λ Kₜ z n*Y' n): Stratus.SupplyP Y h' S s (fun i=> reading Kₜ S (X' i) (p i)):=by -- enough only constant Y for now
 intro i h; simp_rw [reading_p]; let P:MeasurePreserving Prod.fst (city (side Y i s)) (Wilson.prior SU.group (More (side Y i s))):= measurePreserving_fst
 let W(U:Pane (side Y i s)):= Nylon Λ.R (onC (side Y i s) U)
 have hΞ:∀ᵐ v∂city (side Y i s), W v.1 ≠ z:= P.quasiMeasurePreserving.ae (p:=fun U:Pane (side Y i s)=> W U≠z) (editorial Λ.R Λ.V.tallX ⟨h.seat_.mono t⟩ z)
 filter_upwards [hΞ] with V p; let L:= shapeA Y h' s i V; change Tendsto (fun n=>shapeA Y h' s i V (X' n)) _ _; let b:FC (Single (side Y i s)):= L (Y' 0); let Q:= (1:FC (Single (side Y i s))); simp_rw [g,do_times,ebony,do_stamp]; change Tendsto (fun i=> (regnant i z (W V.1) • Q) * L (Y' i)) _ _; exact (zero_mul b ▸ zero_smul ℂ Q ▸ (Tendsto.mul ((reg.limit z (W V.1) p).smul_const Q) (e i V))) -- Eq tune
#print axioms symbolic
variable {P:Call Λ l}{J:Wicket Λ l}{I:ℕ→Family (tent Y h')→ℕ→ℂ}{E:ℕ→Family (tent Y h')→ℂ}
variable (K:Universal Y h' u v I E)(R:Rolled Y h' u v J P)(A:∀ i:Axis,Repertory Y h' K R i)
variable (t:ℝ)
local notation "ω"=> Natural Λ t Kₜ
-- limit shrink at ANY locale. require X given before thresholds (automatic supports).
lemma Vert (T:W Kₜ) (k:ℝ)(p:0<k):∀ᶠ n:ℕ in atTop,∀ (Φ:ℕ→ W Kₜ →ₗ[ℂ]ℂ), Sphere Y h' K R A Φ → ‖Φ s (ebony Λ Kₜ z n*T)‖≤ k:=by
 obtain ⟨F,b⟩:= testimony Kₜ T; let S:= fieldQ Λ.R.L ∪ F; let X'(n:ℕ):=τ n*T; have he(n:ℕ): Locator Kₜ (X' n) S:= locate_join _ S (locate_sub _ (E_loc Y h' z n) subset_union_left) (locate_sub _ b subset_union_right)
 let Q:=‖reading Kₜ F T b‖; let C:= duration η *duration F*Q; have hp:0<C+1:=by unfold C Q; have hx:= duration_pos (fieldQ Λ.R.L); have hy:= duration_pos F; positivity -- duration pos use
 apply Stratus.flex Y h' K R A S s X' he (C+1) (symbolic Y h' s z subset_union_left (Y':=fun _=>T) (fun i v=> tendsto_const_nhds) (fun _=>rfl)) _ hp p; intro i; let L:=(reading Kₜ S (X' i) (he i)); let W:= reading Kₜ F T b; let Z:=reading Kₜ η (τ i) (E_loc Y h' z i)
 have hx:L=timesL Kₜ subset_union_left subset_union_right Z W:= compose_inj _ _ (by rw [show composeQ _ S L=(X' i).val from reading_p ..,show composeQ _ S (timesL _ _ _ Z W)=_ from paired_id Kₜ (D:=S) (v:=subset_union_right) subset_union_left Z W, show composeQ _ (fieldQ Λ.R.L) Z= _ from reading_p _ _ (τ i) (E_loc Y h' z i), show composeQ _ F W=T.val from reading_p .., (show ∀ i,(X' i).val=(τ i).val*T.val from fun _=>rfl)])
 change ‖L‖≤_; rw [hx]; have he:‖Z‖ ≤ 1:= E_price ..; refine (norm_timesL Kₜ _ _ Z W).trans ?_; change _*‖Z‖*Q ≤ _; exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (mul_nonneg (duration_pos _).le (duration_pos _).le) he) (norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one) -- placeholder
#print axioms Eboracum
#print axioms Vert
end
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
