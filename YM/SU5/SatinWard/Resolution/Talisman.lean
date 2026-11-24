import YM.SU5.SatinWard.Resolution.Captain
import YM.SU5.SatinWard.Resolution.TunicW
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
variable {s:ℕ}(a b' c d:ℝ)
open BProof Pressure
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
local notation "K'"=> P.calibration
local notation "τ" s:max=> Pressure.temp (hat P.par.R.L P.par.x s)
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open Quire LampsQ LitCurrent Surplus Next.Rank Next.Rank.Spindle PSE
local notation "Δ★"=> P.run
local notation "H★"=> P.large
local notation "Lp"=> lapQ P.run
local notation "U'S" => WCash Δ★ s
lemma rootVolume (P: Spine)(Q μ:ℝ)(hq:0≤ Q) (n:ℕ) (A:ℕ) : ∀ᶠ s:ℕ in atTop,∀(x y:Cover)(d:Gaia)(R:ℝ), R≤ polishQ P s ^ n → ∀z:Addressing x y d μ R Q, gradeLight z (polishQ P s) (P.thresholdF s) → WidthBudget (pavilion x (A+P.thresholdF s)∪pavilion y (A+P.thresholdF s)) (budgetWidth (hat P.par.R.L P.par.x s) (n+1)):=by
 filter_upwards [(polish_late P).eventually_ge_atTop (Q+2*A+6),(polish_late P).eventually_ge_atTop 1] with s h h' x y d R e y0 g0
 let u:=polishQ P s; let N:=pavilion y A; let F:=patchF (x-y) R; let g:= ‖F‖; let K:=(Q+1)*R; have w:= y0.pLease; have hd:0<K:=by unfold K; positivity
 let T := Nat.ceil K; have hv: g ≤ Q+1:=by have hx:μ/R≤ 1:= (div_le_one (by positivity)).2 (by linarith only [y0.lap]); exact (norm_le_norm_sub_add F d).trans ((add_le_add (y0.meters.trans hx) y0.sizes).trans_eq (add_comm ..))
 apply widenWidth (Finset.Subset.refl _) _ (footprintA (k:=T) ?_)
 all_goals rotate_left 0 -- order
 · apply (Nat.cast_le (α:=ℝ)).mp; apply le_trans _ (Nat.le_ceil (R:=ℝ) _); push_cast; rw [pow_succ]; let Y:=(P.thresholdF s:ℝ); change 2*((A:ℝ)+Y)+ ↑T≤ u^n*u; have hx:(T:ℝ)<K+1:=Nat.ceil_lt_add_one hd.le;
   have ht:2*Y ≤ R:=calc
      2*Y ≤ (μ+2*Y+4)*u:=le_trans (_root_.le_mul_of_one_le_right (by unfold Y; positivity) g0.1) (by have b:0≤μ:=y0.r₀; exact mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans g0.1))
      _ ≤R:=g0.2.2.2
   unfold K at hx; nlinarith only [mul_le_mul_of_nonneg_left e (show 0≤Q+1 by positivity), e, hx,ht, mul_le_mul_of_nonneg_left (show Q+2*A+6≤u from h) (pow_nonneg (zero_le_one.trans g0.1) n), show 1≤u^n from one_le_pow₀ h', mul_le_mul_of_nonneg_right (show 1≤u^n from one_le_pow₀ h') (Nat.cast_nonneg (α:=ℝ) A)] -- tune
 intro i; apply (Nat.cast_le (α:=ℝ)).mp; apply le_trans _ (Nat.le_ceil K); let Vc:=x-y; have hμ:‖scape Vc‖=R*g:=by rw [show scape Vc=R • F from (smul_inv_smul₀ (show R ≠ 0 from (zero_lt_one.trans_le w).ne') _).symm,norm_smul,Real.norm_of_nonneg (zero_le_one.trans w)]
 have hc: |((x i-y i:ℤ):ℝ)| ≤ _ := show |(shaftX Vc) i| ≤ ‖scape Vc‖ from le_trans (norm_le_pi_norm (shaftX Vc) i) (YM.Stationary.orbit_at ..); rw [hμ] at hc; apply le_trans _ ((hc.trans (mul_le_mul_of_nonneg_left hv (zero_le_one.trans w))).trans_eq (mul_comm ..)); apply le_of_eq; rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
lemma morphQ {G A B C D E:ℂ} {p q K R w:ℝ}(V:ℝ)(hv:0<V)(hk:V≤R)(h:1≤R) (u:‖A-B‖≤w)(v:‖D-E‖≤w)(y:‖G-C‖≤w)(t₁:R^9*w≤1)(t₂:w≤1)(a:‖B‖≤p) (b:‖E‖≤q){k:ℂ}(e:Disp V K ((R:ℂ)^8*(C-B*E)) k): Disp V (K+(p+q+2)) ((R:ℂ)^8*(G-A*D)) k:=by
 let Z:=(R:ℂ)^8; let f':=Z*((G-C)-(A*D-B*E)); let l:=Z*(C-B*E); have hp:0<R:=by linarith
 have d:0≤ w:= (norm_nonneg _).trans u
 have H:‖A*D-B*E‖≤ (p+q+1)*w:=by
    rw [show A*D-B*E=(A-B)*E + A*(D-E) from by ring]; refine (norm_add_le ..).trans ?_
    rw [norm_mul,norm_mul]; have hu:‖A‖ ≤ p+1:= (norm_le_norm_sub_add A B).trans ((add_le_add (u.trans t₂) a).trans_eq (add_comm ..)); exact (add_le_add (mul_le_mul u b (norm_nonneg _) d) (mul_le_mul hu v (norm_nonneg _) ((norm_nonneg _).trans hu))).trans_eq (by ring)
 have g:0≤p+q+2:=by linarith [norm_nonneg B,norm_nonneg E]
 have a':Disp V (p+q+2) f' 0:= ⟨g,(norm_zero).trans_le g,by
    rw [sub_zero]; unfold f'; rw [norm_mul]; have hz:‖Z‖=R^8:=by unfold Z; rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    rw [hz]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add y H)) (by positivity)); rw [le_div_iff₀ hv]; nlinarith only [mul_le_mul_of_nonneg_left t₁ g, mul_le_mul_of_nonneg_left hk (show 0≤R^8*(w+(p+q+1)*w) from by rw [show w+(p+q+1)*w=(p+q+2)*w from by ring]; positivity)]⟩ -- check closure semicolon
 rw [show (R:ℂ)^8*(G-A*D)= l+f' from (by unfold l f' Z; ring),← show k+(0:ℂ)=k from add_zero _]; exact e.plus a'
abbrev influ (χ:Chamber.Division)(j:ℕ):ℂ:= (5/2:ℂ)*(bmass j * IndexMag.medalD χ)
abbrev equator:ℝ:= 3 * Fintype.card Sage * (4*Maxwell.normal*((1:ℝ)^2)⁻¹^2)^2
lemma equator_nn : 0≤ equator:=by unfold equator; positivity
lemma le_equator (d:Gaia)(h:1≤ ‖d‖): ‖optic d‖ ≤ equator:=by
 have ht:0< ‖d‖:= zero_lt_one.trans_le h
 rw [optic_formula _ (norm_pos_iff.mp ht), Complex.norm_real,Real.norm_of_nonneg (optic_pos _ (norm_pos_iff.mp ht)).le]; unfold posix equator; have e:=Maxwell.normal_pos; gcongr
variable (E':ℝ)
include T H
lemma raster {s:ℕ}(F:WCash P.run s)(x:Cover)(h:(∑ i,∑ j, ‖F i j‖) ≤ E'):
    ‖(Quire.grain P.run F x).issues (β s) (W s) (Real.sqrt (β s))‖ ≤ E'*escrowCoin P:=by
 let T':= Quire.grain P.run F x; unfold Quire.grain Tab.issues fareCoin; rw [sum_product]; simp_rw [archeryQ (P.run.meter.a s).B (W s) (wise T H s).1 (wise T H s).2]
 have hz:0≤ escrowCoin P:= sq_nonneg _
 refine (norm_sum_le ..).trans ((sum_le_sum (fun i (_:i∈univ)=>(norm_sum_le ..).trans (sum_le_sum (g:=fun j=> ‖F i j‖*escrowCoin P) (fun j _=>?_)))).trans ?_) -- goal metavars need annotation
 case refine_1 => simp only [norm_mul,Complex.norm_I,mul_one]; exact mul_le_mul_of_nonneg_left (response_fare T ..) (norm_nonneg _)
 simp_rw [←sum_mul]; exact mul_le_mul_of_nonneg_right h hz
omit T H
lemma slipPose {q:ℕ}{D m:ℂ}{χ:Chamber.Division}{X d:ℝ}{P₀:Gaia}(u:‖m- (bmass q*IndexMag.medalD χ)‖ ≤ d/X) (h:1≤ X) (w:1≤ ‖P₀‖) {E:ℝ}(p: Disp X E D ((5/2:ℂ)*m*optic P₀)): Disp X (E+ ‖influ χ q‖ * equator+ ‖(5/2:ℂ)‖* |d| * equator) D (influ χ q *optic P₀):=by
 have hv:0≤ ‖(5/2:ℂ)‖* |d| * equator:= mul_nonneg (by positivity) equator_nn; have hf:0≤ ‖influ χ q‖*equator:= mul_nonneg (norm_nonneg _) equator_nn; have hE:=p.nn
 refine ⟨by linarith,by rw [norm_mul]; exact le_trans (mul_le_mul_of_nonneg_left (le_equator _ w) (norm_nonneg _)) (by linarith),?_⟩
 apply (norm_sub_le_norm_sub_add_norm_sub D ((5/2:ℂ)*m*optic P₀) _).trans; rw [add_div,add_div]; refine (add_le_add (p.amount.trans (le_add_of_nonneg_right (show 0≤ ‖influ χ q‖ * equator / X from div_nonneg hf (zero_le_one.trans h)))) ?_)
 unfold influ; rw [← _root_.sub_mul,← _root_.mul_sub,norm_mul,norm_mul]; exact (mul_le_mul (mul_le_mul_of_nonneg_left (u.trans (div_le_div_of_nonneg_right (le_abs_self _) (zero_le_one.trans h))) (norm_nonneg _)) (le_equator _ w) (norm_nonneg _) (by positivity)).trans_eq (by ring)
include H T
variable (H' A φ:ℝ) (g:P.NightCop)(x:Cover)(j f0:ℕ)(η:Type)[Fintype η]
local notation "S✔" i:max s:max z:max => P.singleState i s z
noncomputable def moniker (U V:P.Test) (i:Axis) (s:ℕ) (z:P.Spectrum0 i) :ℂ:= (S✔ i s z) (U*V)-(S✔ i s z) U * (S✔ i s z) V
include g
lemma tabulate (Q μ:ℝ)(p:0<a)(r:ℕ)(χ:Chamber.Division) (e:0≤Q){h:ℝ}: ∃ E:ℝ,0≤ E ∧∀ᶠ s:ℕ in atTop, payable P s 2 ∧∀ (z:payable P s 2) (U:P.Test), 0< lapQ P.run s→bornPub a h H' A φ j f0 χ η s x σ U → ∀ R:ℝ, R ≤ (polishQ P s)^r→∀ (y:Cover)(d:Gaia)(A:Addressing (nodeC x) y d μ R Q), gradeLight A (polishQ P s) (P.thresholdF s)→ ∀ (i:Axis)(z₁:P.Spectrum0 i), Disp (polishQ P s) E ((R:ℂ)^8 * moniker (dear β U s) (aptLabel P β 1 1 s y z) i s z₁) (influ χ j * optic d):=by
 let d₀:=inkCoins 1 1; obtain ⟨B,hB,hP,h'⟩:= fortress T a d₀ H' A φ g x j f0 η p (r+1) χ (h:=h)
 obtain ⟨E,hE,u⟩:= winLight H Q B; let X:= gaugeNote P 1 1; let S:= B * escrowCoin P; let A₂:=E+(S+X+2); let F':ℝ:= bmass j+1; have hV:0≤X:= (norm_nonneg _).trans (payload T H 1 1 0 0 0); have hx:0≤ S:= mul_nonneg hP.le (sq_nonneg _); refine ⟨A₂+‖influ χ j‖*equator+‖(5/2:ℂ)‖*|F'| *equator,by have e:=equator_nn; unfold A₂; positivity,?_⟩
 filter_upwards [h', phaseRent P r, attest T H 1 1 1 1 g r Q μ e,rootVolume P Q μ e r petalD] with s t y z u'
 refine ⟨z.1,fun p U v e R h₂ w d C ξ i jstar=>?_⟩
 obtain ⟨W',m,hM,h⟩:= t _ v e
 let A:=(P.thresholdF s); let T':= Quire.grain P.run W' (nodeC x); let V:=aptLabel P β 1 1 s w p; let V':= sampleP 1 1 (τ s) w -- edit
 let S':= pareQ A (nodeC x) ∪ pareQ A w; let ess:= h S' subset_union_left (by unfold S' pareQ; rw [Nat.add_comm A]; exact u' _ _ _ _ h₂ C ξ) i jstar; let Tρ:ticket S' 1 (Ω s) 2 V':= fun i h=> improve (sample_ticket 1 1 (Ω s) (τ s) w rfl p i h) (Finset.Subset.trans (inclPav _ _ (A+petalD) (by omega)) subset_union_right) le_rfl
 have hp: V'.terms ≤ B:= (sample_terms ..).trans_le hB; let y₀:= Real.sqrt (β s); let χs:= ess.2 V' Tρ (sample_says 1 1 _ _ _ _) hp; let τ1:= (z.2 p _ _ R d h₂ C).2 i jstar; let V₀:= fun G:Tab ledgerDeck=> G.issues (β s) (W s) y₀; let hμ: d ≠ 0:= norm_pos_iff.mp (lt_of_lt_of_le (by norm_num:(0:ℝ)<2) C.area); -- remove
 let Θ:= u C ξ s W' hM.budget; apply slipPose (q:=j) hM.buoy ξ.1 (le_trans (by norm_num:(1:ℝ)≤2) C.area)
 unfold moniker; refine morphQ _ (zero_lt_one.trans_le ξ.1) ξ.2.1 C.pLease ess.1 τ1.2.1 χs (y.2.2 R C.pLease h₂) y.2.1 (raster T H B W' _ hM.budget) (payload T H 1 1 _ _ _) ?_
 change Disp _ E ((R:ℂ)^8 * issuesBond T' V' (W s) (β s) y₀) _; rw [show issuesBond T' V' _ _ _= _ from aeroBond _ _ (W s) (wise T H s).1 (wise T H s).2, optic_formula d hμ,← conc_earns hμ W' hM.style]; exact Θ
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
