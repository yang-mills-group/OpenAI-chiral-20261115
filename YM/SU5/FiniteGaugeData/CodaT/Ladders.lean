import YM.SU5.FiniteGaugeData.CodaT.Chell
import YM.SU5.FiniteGaugeData.CodaT.Aria
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
open Hills
variable (h:Real.exp 1≤Λ.x) (s i k:ℕ) {S:Finset Cover}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ} (K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
local notation "Kₜ"=> tent Y h
variable (D:Desire (tent Y h) S)
local notation "Ψ" s:max i:max => side Y i s   -- swapped!
local notation "Φx" s:max i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram s
local notation "Θx"=> tickA (Ψ s i)
local notation "Φψ" s:max i:max k:max=> D.slope (tent Y h) Λ.K.j (Ψ s i) (((Y.voyage i).X (Y.uv k)).gram s).J.M
local notation "ΦH"=> 45 * Real.sqrt (MajorH Λ)
local notation "N"=> Ψ s i
variable {n m d:ℕ}{p C Y0 r t b u' e E':ℝ}{U:Op (Single (side Y i s))}
variable (S':RadioCity.Hypothesis Λ l g Y)
set_option maxHeartbeats 730000
section
private lemma cup_fee (ζ:ℂ)(t:‖ζ‖≤r)(hC:0≤C)(hU:Fable U (tickA (side Y i s)))(q:pointM (Single (side Y i s)) Θx U C) : |D.bend U Θx ζ| ≤ r*calibrationH S C* D.owed:=by
 refine (Complex.abs_re_le_norm _).trans ((norm_mul ..).trans_le (le_trans ?_ (le_of_eq (mul_assoc ..).symm))) -- specify
 exact mul_le_mul t (D.pay hU q hC 1) (norm_nonneg _) ((norm_nonneg _).trans t)
local notation "c0"=> calibrationH S ΦH
abbrev pushH(S:Finset Cover)(K:Calibration):ℝ:= capR K (fun _=> spreadN S)
abbrev strictH (y b:ℝ):ℝ:=4+3*b^2*y
private lemma phi_pos(Λ:Preparation):0≤ MajorH Λ:= Presidio.sponsor_v _ (editions Λ) -- tune namespace
private lemma stern(Λ:Preparation)(b:ℝ):0 < strictH (MajorH Λ) b:=by unfold strictH; linarith only [mul_nonneg (sq_nonneg b) (phi_pos Λ)]
private lemma cap_pos (S:Finset Cover)(K:Calibration):0≤pushH S K:= Nat.cast_nonneg _ -- Nat casts `capR`
local notation "Ω"=> strictH (MajorH Λ) D.owed
-- flare fee in assembly
private lemma width_sale {C r:ℝ} (ζ:ℂ)(Z:∀ (ζ:ℂ),‖ζ‖≤r→∀ (x:Side)(V:Fields ((Kₜ).c x)), ‖(Aria.tail n D.paid ζ).val x V‖≤ C)(t:‖ζ‖≤r)(u:ℝ): ∀ z:Fields (Ψ s i), ‖sold Y h s i ((((Real.exp u):ℂ) • Aria.tail n D.paid ζ : W Kₜ)).val z‖≤ Real.exp u*C:=by
 rw [Subalgebra.coe_smul, map_smul]; intro z; rw [Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply castS (terrain Y h (Y.ir i) s) ((Aria.tail n D.paid ζ).val (momentm Y i s)) _ (Z ζ t _)
where castS {n m:Side}(t:n=m)(f:Mark n)(z:Fields m)(H:∀ y, ‖f y‖≤C): ‖ship t f z‖≤ C:=by subst m; exact H _
variable (H₁:D.paid^n=0)(t':∃ x:ℝ,0<x)
local notation "U₀"=> pushH S Kₜ * Ω + c0
include H₁ K R A S'
private lemma frank (p:0<r) (q:4*(r*D.owed)^2≤1)(e:0< E') : ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop,∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ → ∀ ζ:ℂ, ‖ζ‖≤ r→‖noteT n D.paid (Φ s) ζ‖ ≤ Real.exp ((ζ* (Φψ s (u i) (v k))).re) * (Real.exp ((pushH S Kₜ * Ω + c0)*r^2)*(1+E')):=by
 obtain ⟨t,u0,hx⟩:=D.melt r p; obtain ⟨c,w,Z⟩:= Aria.flare n D.paid D.at_site r p.le; let C':= D.owed; let μ:=4*(r*C')^2; let δ:=r^2; have he:0<r*C':=mul_pos p D.hv; let T:= Ω * δ; let H':= MajorH Λ; let a:= c0; have ha:0 ≤ ΦH:=by positivity
 have hv:0 ≤ a:=calib_pos S ha; let G:=2*r*a*C'; have ht:0<δ:=pow_pos p 2; have hz:0< G+1:= lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (show 0 ≤ G from mul_nonneg (mul_nonneg (mul_nonneg zero_le_two p.le) hv) D.hv.le)); -- tune argument.lt
 let F:= pushH S Kₜ; let X:=a*δ; let Gt:= -(T*F); have hL:0≤T:= mul_nonneg (stern Λ C').le ht.le
 let M:=r*a*C'; let Y' := Real.exp M*c; have hMu:0<μ:= mul_pos (by norm_num) (pow_pos he _)
 have hp:4*δ+factorC μ (r*C') (MajorH Λ) ≤ T:=by unfold T μ δ strictH factorC; change _ ≤ (4+3*C'^2* MajorH Λ)*_; nlinarith only [mul_nonneg (sq_nonneg (r*C')) (phi_pos Λ)]
 filter_upwards [candles (j:=spreadN S) Y h K R A S S' (fun i=> ⟨_,spread_film i⟩) (show 0≤Y' from mul_nonneg (Real.exp_pos _).le w) e (show 0≤G from mul_nonneg (mul_nonneg (mul_nonneg zero_le_two p.le) hv) D.hv.le) u0 ht hp hMu q (show (r*C')^2≤μ/2 from by unfold μ; nlinarith only [sq_nonneg (r*C')]) he hL (show Gt+T*F ≤0 from (neg_add_cancel _).le)] with s V
 filter_upwards [V] with i Yb; filter_upwards [Yb] with k tH Φ H z h0
 let m':=Ψ s (u i);
 let T':= (((Y.voyage (u i)).X (Y.uv (v k))).gram s).J.M; let N':=spar Λ.K.j T' (1:Pane m'); let Q:=tickA m'; let L₀:= D.slope Kₜ Λ.K.j m' T'; let ξ:= D.bend N' Q z; have hz':(z*L₀).re=ξ:=rfl
 obtain ⟨q1,pT,o⟩:=tH; let U:=D.icicle q1 pT ha p (hx m') h0; let x:= Aria.tail n D.paid z; let α:=Gt - ξ - X; let ℓ:ℂ:= Real.exp α; let f:=ℓ • x
 have v':0≤X:=mul_nonneg hv ht.le; have hα:α+ξ+X ≤ Gt:=by unfold α; linarith
 have hW : α ≤ M:=by
    have hη := (abs_le.mp (cup_fee (s:=s) (i:=u i) Y h D z h0 ha q1 pT)).1; change -M ≤ ξ at hη; unfold α Gt -- danger unfold sth
    linarith only [hη,v', mul_nonneg hL (show 0≤F from cap_pos ..)]
 have ht:∀ t,‖sold Y h s (u i) f.val t‖ ≤ Y':=fun y=> (width_sale (n:=n) Y h s (u i) D z Z h0 α y).trans (mul_le_mul_of_nonneg_right (Real.exp_monotone hW) w)
 have hK: Rent Y h s (u i) N' Q (spreadN S) t (r*C') X ξ G α 1 S f:=by unfold Rent f; rw [Subalgebra.coe_smul,map_smul,show sold Y h s (u i) x.val=_ from soldGerm n z Y h s (u i) D H₁]; exact Post.piece U -- tune namespace icicle opaque. type t metavariable
 have hζ:= o ξ X α v' hα f (locate_scale Kₜ _ ℓ (tailSite n D.paid z D.at_site)) ht hK Φ H; change ‖(Φ s) (ℓ • x)‖ ≤ _ at hζ; rw [map_smul,norm_smul, show ‖ℓ‖=Real.exp α from (by unfold ℓ; rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le])] at hζ
 change ‖Φ s x‖≤ Real.exp ξ * _; rw [← mul_assoc,←Real.exp_add]; apply le_of_mul_le_mul_left (hζ.trans ?_) (Real.exp_pos α); rw [←mul_assoc, ←Real.exp_add,show α+(ξ+(U₀)*r^2)=0 from ?_, Real.exp_zero,one_mul]; unfold α X Gt T a F δ -- notation Ω unfolds?
 ring
end
include S'
private lemma canvasW(b C:ℝ)(p:0≤C)(d:0<e):∃ r:ℝ, 0<r ∧ 4*(r*b)^2≤1 ∧ 4*(Real.exp (C*r^2)*(1+r^2)-1)/r≤e :=by
 let f(s:ℝ):= Real.exp (C*s^2)*(1+s^2); let F(s:ℝ):=4*(s*b)^2
 have he:F 0=0:=by unfold F; ring
 have ht: Tendsto F (𝓝[>] 0) (𝓝 0):=by nth_rw 3 [←he]; exact (show Continuous F by unfold F; fun_prop).continuousAt (x:=0)|>.tendsto|>.mono_left nhdsWithin_le_nhds -- tune parentheses
 have hh:HasDerivAt f 0 0:=by let A:=(hasDerivAt_id' (0:ℝ)).pow 2; simpa [f] using! (A.const_mul C |>.exp).mul (A.const_add 1)
 obtain ⟨r,x,y,Z⟩:= ((ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1))).and ((hh.tendsto_slope_zero_right.eventually (ge_mem_nhds (by positivity: 0<e/4))).and self_mem_nhdsWithin)).exists
 have h:0<r:=Z; refine ⟨r,h,x,?_⟩; change r⁻¹ * (f (0+r)-f 0)≤ _ at y; rw [zero_add, show f 0=1 by simp [f]] at y; change 4*(f r-1)/r≤_; field_simp at y ⊢; linarith -- tune
-- without knowing convergence of the free comparator yet, we can evaluate & bound spacing; genuine moving tangent read.A.Power.
def yak (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ):ℂ:=Φ s D.paid
abbrev Pslope:= Φψ s i k
include K R A
lemma affirmD (p:0<e): ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop,∀ Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ, Sphere Y h K R A Φ → ‖Φ s D.paid-Pslope Y h s (u i) (v k) D‖ ≤ e:=by
 let F:= pushH S Kₜ; let C:=F*(strictH (MajorH Λ) D.owed)+calibrationH S (ΦH); let b:= D.owed; have hc: 0≤C:=add_nonneg (mul_nonneg (cap_pos ..) (stern Λ b).le) (calib_pos S (by positivity))
 obtain ⟨r,z,x,hr⟩:=canvasW (e:=e) Y S' b C hc p -- likely extra
 let t:= Real.exp (C*r^2)*(1+r^2)-1; have ht:0 < t:= sub_pos.mpr (lt_of_lt_of_le (lt_add_of_pos_right _ (pow_pos z 2)) (le_mul_of_one_le_left (by positivity) (Real.one_le_exp (mul_nonneg hc (sq_nonneg _)))))
 obtain ⟨i,u0⟩:=D.off; let n:=i+2; have hp:D.paid^n=0:= pow_eq_zero_of_le (by omega) u0; have he':0<r^2:=pow_pos z 2; have hh:=t+1
 filter_upwards [frank Y h K R A D S' hp z x he'] with s o; filter_upwards [o] with i g; filter_upwards [g] with k f Φ Q
 exact (Aria.come (at_two n _ _ (Q.living s) (by omega)) ((poem n _ _).differentiableOn) (lyric n D.paid (Φ s) (Q.living s) (by omega)) ht z (fun ζ e=> le_trans (f Φ Q ζ (mem_ball_zero_iff.mp e).le) (le_of_eq (by change _*(Real.exp (C*r^2)*(1+r^2))=_*(1+t); unfold t; ring)))).trans hr -- le placement e scope incorrect
#print axioms affirmD
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
