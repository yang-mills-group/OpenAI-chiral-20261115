import YM.SU5.FiniteGaugeData.Indigo.Refugio
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
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
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "U"=> W (tent Y h)
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
variable {a:Axis}{d w n m:ℕ}{x f:W (tent Y h)}{vD:Axis→ℕ}(L:Master Y s i)(lP:Club Y g s)

namespace Bonbon
/- The tail camera: several of the purchases below adapted from WP8 Eight/{Likeness,Senate,Melt} etc. β sector pace. -/
open Steam.Indigo
include K R A
private lemma dayBook (p:∀ i,∃ b:ℤ,film b (vD i) S i)(c:0≤C)(z:0<D)(q:0≤θ)(x:0≤α)(w:α*Real.exp (θ*capR Kₜ vD) ≤ 1)(e:D<C₀): ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (V:Literature (side Y (u i) s))(f:W (tent Y h))(u_:Locator (tent Y h) f S), (∀ j,‖sold Y h s (u i) f.val j‖ ≤ C) → Tax Y h s (u i) (V:=V) m 0 C S f→ LedgerT Y s (u i) (v k) V m (D⁻¹*C) α θ→∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖ ≤ C₀:=by
 let n:=(D⁻¹:ℝ); have ht: 0<n:=inv_pos.mpr z; let ε:=(C₀-D)*n; have hε:0<ε:=mul_pos (sub_pos.mpr e) ht; let b:ℂ:=↑n
 filter_upwards [express Y h K R A S s (m:=m) 3 p (c:=(show 0≤n*C from mul_nonneg ht.le c)) x hε q w] with i E; filter_upwards [E] with k p' V f u' c' t O Φ H
 have he:sold Y h s (u i) (b • f).val=b • sold Y h s (u i) f.val:=map_smul (sold Y h s (u i)) _ _
 have hb:‖b‖=n:=by unfold b; rw [Complex.norm_real,Real.norm_of_nonneg ht.le]
 have hv := Hull.scale t b; rw [hb] at hv
 have hk:= p' V (b • f) (locate_scale _ _ _ u') (fun z=>by rw [he,Pi.smul_apply, norm_smul,hb]; exact mul_le_mul_of_nonneg_left (c' z) ht.le) (by unfold Tax; rw [he]; exact hv) O Φ H; rw [map_smul,norm_smul,hb] at hk; refine le_of_mul_le_mul_left (hk.trans (show 1+ε ≤ n*C₀ from ?_)) ht; unfold ε n; rw [_root_.sub_mul]; have hx:D*D⁻¹=1:=mul_inv_cancel₀ z.ne'; linarith
variable (Z:Finset (Face ℤ)) {r:ℝ} (r₀:0≤r)
local notation "vV"=> μX Λ s r
local notation "Qₜ"=>carpet Z∪S
include lP r₀
omit K R A lP r₀
include Λ in
lemma sloW(g:ℝ)(e:0≤g) : 0 ≤ slopeZ Λ.W g:=by unfold slopeZ slopeF accrual; positivity
include K R A r₀ lP
lemma tempoPrice (p:∀ i,∃ b:ℤ,film b (vD i) S i)(q:0≤g)(c:0≤C)(e:C*Real.exp (-r)*Real.exp (slopeZ Λ.W g * capR Kₜ vD)<θ):∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (f:W (tent Y h))(xV:Locator (tent Y h) f S),(∀ z,‖sold Y h s (u i) f.val z‖≤ C)→Glints 1 (region S (side Y (u i) s)) vV (sold Y h s (u i) f.val) →∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖ ≤ θ:=by
 let x:=slopeZ Λ.W g; have hv:0 ≤ x:=by unfold x slopeZ slopeF accrual; positivity
 obtain ⟨b,t,pT⟩:= exists_between e; have hz:0<b:=lt_of_le_of_lt (mul_nonneg (mul_nonneg c (Real.exp_pos _).le) (Real.exp_pos _).le) t; let F:= b⁻¹*C*Real.exp (-r); have hw:0≤ b⁻¹*C:=by positivity
 have h₀:F*Real.exp (x*capR Kₜ vD) ≤ 1:= ((mul_le_mul_of_nonneg_left t.le (inv_pos.mpr hz|>.le)).trans ((inv_mul_cancel₀ hz.ne').le)).trans' (show F*Real.exp (x*capR Kₜ vD)≤ b⁻¹* _ from le_of_eq (by unfold x F; ring))
 filter_upwards [dayBook Y h K R A S s (m:=1) p c hz hv (mul_nonneg hw (Real.exp_pos _).le) h₀ pT] with i t; filter_upwards [t,K.pick.pass Y h s (u i)] with k p' t f u' v g Φ H; exact p' _ f u' v (Hull.trig (V:=fairy vV _) g (sold_affair Y h S s (u i) u') v) (ledger Y s _ _ lP r t.enters t.depth hw r₀) Φ H -- natural glints by defin
omit K R A r₀ lP
private lemma proofsT' (Ko:Calibration)(f:W Ko)(r:ℝ)(c:Width Ko f C)(m':Side): let x:=seesT Ko Z r*f; let T:=carpet Z∪ S; let m:=Ko.c m'; RealWidth Ko x m' C ∧ Glints 1 (region T m) r (x.val m'):=by
 intro x T m; let Q:=seesT Ko Z r
 constructor; · intro z; change ‖(troubles Ko Z r m' z)*f.val m' z‖ ≤ C; exact (norm_mul_le ..).trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (hovers Ko Z r z)) (c m' z))
 change Glints 1 _ _ ((troubles Ko Z r m')*(f.val m')); exact Glints.shrink r (tripped Ko Z r m') (Finset.image_subset_image (show carpet Z⊆ T from subset_union_left))
private lemma proofsT (f:W (tent Y h))(r:ℝ)(c:Width Kₜ f C) : let x:=seesT Kₜ Z r*f; let y:= sold Y h s i x.val
 (∀ z,‖y z‖ ≤ C) ∧ Glints 1 (region (carpet Z∪S) N) r y:=by
 intro x y; let T:=carpet Z∪ S; let Q:=seesT Kₜ Z r
 let V:= proofsT' S Z Kₜ f r c (momentm Y i s); let hV:= terrain Y h (Y.ir i) s; change (∀ z,‖ship hV (x.val (momentm Y i s)) z‖≤ C)∧ Glints 1 _ r (ship hV _)
 exact castQ (terrain Y h (Y.ir i) s) (x.val (momentm Y i s)) T (t:=r) V.1 V.2
where castQ {n m:Side}(h:n=m)(x:Mark n)(T:Finset Cover){t:ℝ}(c: ∀ z, ‖x z‖≤ C)(hp:Glints 1 (region T n) t x): (∀ z, ‖ship h x z‖≤ C)∧Glints 1 (region T m) t (ship h x):=by subst n; exact ⟨c,hp⟩
variable (Φ:ℕ→Charm.W (tent Y h)→ₗ[ℂ]ℂ)
include K R A lP r₀
lemma cardax (p:∀ i,∃ b:ℤ,film b (vD i) (carpet Z∪S) i)(c:0≤C)(g':0≤g)(u_:Sphere Y h K R A Φ)(f:W (tent Y h))(q: Locator Kₜ f S)(e: Width Kₜ f C) : ‖Model Y h Φ s (troubles Kₜ Z vV*f.val)‖ ≤ C*Real.exp (-r)*Real.exp (slopeZ Λ.W g * capR Kₜ vD):=by
 let T:= carpet Z∪ S; let Q:=seesT Kₜ Z vV; let x:=Q*f
 rw [show troubles Kₜ Z vV*f.val = x.val from rfl,Modell]; apply le_of_forall_gt_imp_ge_of_dense; intro w hv; obtain ⟨i,p'⟩:= (tempoPrice Y h K R A T s lP r₀ p g' c hv).exists; obtain ⟨k,h₀⟩:= p'.exists
 have Ua:= proofsT Y h S s (u i) Z f vV e
 exact h₀ x (locate_join Kₜ _ (locate_sub Kₜ (undone Kₜ Z vV: Locator Kₜ Q _) subset_union_left) (locate_sub Kₜ q subset_union_right)) Ua.1 Ua.2 Φ u_
omit K R A lP r₀
lemma studyFilm (S:Finset Cover):∃ D:Axis→ℕ, ∀ i,∃ b:ℤ,film b (D i) S i:=by
 let Z':= S.sup fun s=>univ.sup fun a:Axis=>(s a).natAbs; refine ⟨fun _=>2*Z',fun a=> ⟨-(Z':ℤ),fun i t=>?_⟩⟩; have he:(i a).natAbs ≤ Z':= (le_sup (f:=fun a:Axis=>(i a).natAbs) (mem_univ _)).trans (le_sup (f:=fun i=>univ.sup fun a:Axis=>(i a).natAbs) t); change -(Z':ℤ)≤ i a ∧ i a≤ -(Z':ℤ)+(↑(2*Z':ℕ):ℤ); omega
abbrev vKit := (studyFilm S).choose
noncomputable def wageZ (Λ:Preparation)(h:Real.exp 1≤Λ.x)(Y:Course Λ (VolumeCape.Dream.Nimbus l))(S:Finset Cover) (g:ℝ): ℝ:= Real.exp (slopeZ Λ.W g* capR (tent Y h) (vKit S))
include K R A lP
lemma costZ(t: carpet Z ⊆ S)(r:ℝ)(p:0≤r)(c:0≤C)(g':0≤g)(V: Sphere Y h K R A Φ) (f: W (tent Y h))(u:Locator Kₜ f S)(e:Width Kₜ f C):
 ‖Φ s (seesT Kₜ Z (μX Λ s r) *f)‖ ≤ C*Real.exp (-r)*wageZ Λ h Y S g:=by
 let z:=cardax Y h K R A S s lP Z p Φ (vD:=vKit S) (by rw [union_eq_right.mpr t]; exact (studyFilm S).choose_spec) c g' V f u e; rw [←Modell]; exact z
private lemma normalL (f:Literature (side Y i s))(c:0≤C)(p:s≤Y.uv k)(u:(Y.voyage i).kick ≤ k)(v:0≤g): LedgerT Y s i k f 0 C C (slopeZ Λ.W g):=by
 intro T q n x e b h₀ h₁; let G:=(Y.voyage i).CapeT s; let F':= x ∘ drawn G
 let z:= Club.toll lP F' (pow_nonneg c n) u p (Steam.Toll.supplies (lP.full _ _ p) (p:=fun i=>h₁ _)); apply z.trans; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (pow_nonneg c n); apply mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans (sites_pos _)); unfold slopeZ accrual; apply le_add_of_nonneg_right; positivity
lemma income (c:0≤C)(v':0≤g)(Z: Sphere Y h K R A Φ) (f: W (tent Y h))(u':Locator Kₜ f S)(p:Width Kₜ f C): ‖Φ s f‖ ≤ C*wageZ Λ h Y S g:=by
 apply le_of_forall_gt_imp_ge_of_dense; intro ε v__; obtain ⟨D,hD,t⟩:= exists_between v__; have he:0≤wageZ Λ h Y S g:=(Real.exp_pos _).le; have hp:0<D:=lt_of_le_of_lt (mul_nonneg c he) hD; let b:=D⁻¹*C; have hv:0≤b:=by unfold b; positivity
 obtain ⟨i,v⟩:=(dayBook Y h K R A S s (m:=0) (studyFilm S).choose_spec c hp (sloW g v' : 0 ≤ slopeZ Λ.W g) hv (show b*wageZ Λ h Y S g≤1 from ((mul_le_mul_of_nonneg_left hD.le (inv_pos.mpr hp).le).trans_eq (inv_mul_cancel₀ hp.ne')).trans' (by unfold b; rw [mul_assoc])) t).exists
 obtain ⟨k,v,Pw⟩:= (v.and (K.pick.pass Y h s (u i))).exists; let M':= fairy 0 (side Y (u i) s); let w:=castP (terrain Y h (Y.ir (u i)) s) (p (momentm Y (u i) s)); -- let expr type
 exact v M' f u' w (Hull.trig (V:=M') (n:=0) (m:=0) (fun x y=>Nat.zero_le _) (sold_affair Y h S s (u i) u') w) (normalL Y h K R A s (u i) _ lP M' hv Pw.enters Pw.depth v') Φ Z
 where castP {N' M: Side}{f:Mark N'}(e:N'=M)(z:∀ i, ‖f i‖≤ C) :∀ i, ‖ship e f i‖≤ C:=by subst N'; exact z
#print axioms income
#print axioms cardax
#print axioms costZ
end Bonbon
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
