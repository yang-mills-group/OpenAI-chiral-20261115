import YM.SU5.FiniteGaugeData.CodaT.AdagioX
import YM.CF.Onyx.Quod
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
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
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
-- matching natural currencies for any wired bilinear (WP18). Does not need aligning at planar origins. We construct explicitly so basis signs checked on tiny wrapped endpoints, to read moving slope for this family stencil. Here `Spin10`/`δ5` each paid, upper/lower. Common law on gauge. -/
namespace Niagara
variable {x y a b:Cover}{u v:SpinIdx}
open Largo Mirage -- placeholder
open Dial -- tickA
open Cascade Ember Stationary MeasureTheory
open Onyx Flare -- Mate
-- physical free-momentum scaling. mastery. Keep all angles along ANY Chisel sequence. uniform in Reader world (call after).
namespace PolarF
variable (A:Chisel){X:ℕ→Chisel}{u d:SpinIdx}
local notation "mκ" P:max M:max=> Chisel.μWallet A M P
open Chisel
private lemma fixedLift (N:Side)(i:Site N)(M:Tulip.Male): dip 4 M (mel i)= -(minA*Fir.zen (mixL 4 M.val (mel i))):=by
 let p:= mel i; have ht:=base_subset_realCube zone_pos (mel_h i); have hz:shell 4 M.val p≠0:= by rw [shell_inv 4 M.val ht (mel_away i)]; exact inv_ne_zero (graphs_ne (phys_mix 4 M.val M.property _ ht.1))
 rw [Onyx.dip,skin_mix _ _ ht,lash_s,inv_smul_smul₀ hz]; rfl
private lemma pen_h (M:Tulip.Male)(i:Site N): ‖dip 4 M (mel i)‖ ≤ ‖zen (mixL 4 M.val (mel i))‖:=by rw [fixedLift,norm_neg]; exact Fock.Reduction.Drama.needy Flare.minA_p _
private lemma contour : ∃ C:ℝ,0<C∧∀ (M:Tulip.Male)(N:Side)(i:Site N), ‖dip 4 M (mel i)‖≤ C/Ember.pinch N := by
 -- duplicate chill computation
 obtain ⟨C,h,t⟩:= Cascade.chillY 4 (by norm_num); refine ⟨Real.sqrt C,Real.sqrt_pos.mpr h,fun M N i=>?_⟩
 let P:= mixL 4 M.val (mel i); let H:= shell 4 M.val (mel i); let y:=zen P; let u:ℝ:=∑ i,(P i).re^2; have hp:= mel_h i; let q:=bark i; have hq:0<‖q‖:=lt_of_lt_of_le (pinch_pos _) (Ember.torch _)
 have hu:physical P:=phys_mix _ _ M.property _ hp.1; have he : ‖y‖^2=u:=by
    rw [sq, ← CStarRing.norm_star_mul_self,show star y= -y from zenStar P hu, neg_mul,show y*y= _ from zenSq P, ← neg_smul,neg_neg,norm_smul,norm_one,mul_one,prodM_self _ hu,Complex.norm_real,Real.norm_of_nonneg (sum_nonneg fun i _=> sq_nonneg _)]
 have hw:‖H⁻¹‖=1+u:=by unfold H; rw [shell_inv _ _ (base_subset_realCube zone_pos (mel_h i)) (mel_away _),inv_inv, prodM_self _ hu]; change ‖(1:ℂ)+(u:ℂ)‖=_; rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (add_nonneg zero_le_one (sum_nonneg fun _ _=> sq_nonneg _))]
 have ht:= t M N i; change ‖H⁻¹‖≤_ at ht; rw [hw] at ht;
 apply (pen_h M i).trans; apply le_trans (b:=Real.sqrt C/‖q‖); swap; · exact div_le_div_of_nonneg_left (by positivity) (pinch_pos _) (Ember.torch i)
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp; rw [he,div_pow,Real.sq_sqrt h.le, div_eq_mul_inv]; linarith
def cashOffset (N:Side): Jill.Offset N:=⟨0, norm_zero.trans_le (Ember.pinch_pos N).le⟩
private lemma lambdaT (n:Side)(i:Site n): mel i=tmap (glen (cashOffset n) i):=by unfold Onyx.glen cashOffset; dsimp only; rw [add_zero]; rfl
def ledger (N:Side)(M:Tulip.Male): Site N→Peb:= fun i=> dip 4 M (mel i)
private lemma fits_w : ∃ c:ℝ,0<c ∧∀ (N:Side)(M:Tulip.Male), FormU (cashOffset N) 4 M 1 c (ledger N M):=by
 obtain ⟨c,p,w⟩:= contour; refine ⟨c,p,fun N M=>⟨fun i _=>?_,fun i _=> w M N i⟩⟩; unfold ledger; rw [lambdaT]
abbrev spanD (A:Chisel):=A.landing-A.launch
lemma stage_i (N:Side)(M:Tulip.Male)(R:ℝ): let X:= bore (cashOffset N) R (spanD A) (ledger N M); (R:ℂ)^3 * (Chisel.stage A N M) = X A.d A.u := by -- notation `.spanD` ns adjust
 intro X; have hp(i:Site N): ledger N M i A.d A.u= (-Fir.zen (mixL 4 M.val (mel i))) A.d A.u:=by
    unfold ledger; rw [fixedLift]; simp only [Matrix.neg_apply]; congr 1
    let P:=Fir.zen (mixL 4 M.val (mel i)); have he:minA=cutM plusHalfᶜ:=by unfold minA; rw [Adef, ←raising,dim_cut] -- linear instance spin yes
    rw [he,Largo.compass,if_pos (mem_compl.mpr A.dn)]
 unfold X bore liv Chisel.stage; rw [Matrix.smul_apply, Matrix.sum_apply]; simp_rw [Matrix.smul_apply,hp,smul_eq_mul,charK, ←lambdaT]; simp_rw [μWallet,Chisel.angleK]; -- unfold helpers
 let Z:= (∑ i:Site N, mode (mel i) (spanD A)*(-zen (mixL 4 M.val (mel i))) A.d A.u); change _= _ • Z; rw [Complex.real_smul]; change (R:ℂ)^3*(Z/_) =_*_; push_cast; ring
variable {N_:ℕ→Side}{M_:ℕ→ Tulip.Male}{R:ℕ→ℝ}(p:Yard N_ R)(Y:Gaia)(hp:Y≠0) (τz:Tendsto (fun i=>riseX (R i) (spanD (X i))) atTop (𝓝 Y))(e:∀ i:ℕ,(X i).u=u)(vD:∀ i:ℕ,(X i).d=d)
include p hp τz e vD
private lemma curtain : Tendsto (fun i=>(R i:ℂ)^3*(X i).stage (N_ i) (M_ i)) atTop (𝓝 ((pencil Y) d u)):=by
 let A(i:ℕ):=bore (cashOffset (N_ i)) (R i) (spanD (X i)) (ledger (N_ i) (M_ i)); have he(i:ℕ):(R i:ℂ)^3*(X i).stage (N_ i) (M_ i) = A i d u:=(by rw [←vD i, ← e i]; exact stage_i ..) -- tune
 simp_rw [he]; obtain ⟨c,hc,h⟩:= fits_w; exact ((show Continuous fun x: Peb=> x d u from (continuous_apply u).comp (continuous_apply d)).continuousAt.tendsto.comp (p.struck (M:=M_) (S:=N_) (r:=1) (j:=4) (A:=fun i=> ledger (N_ i) (M_ i)) (Eventually.of_forall fun i=> h (N_ i) (M_ i)) (by omega) hp τz (by norm_num) hc)) -- argument order tune syntax
-- arbitrarily late N & masses matching after tuning by test.
omit p hp τz e vD in
private lemma hires(N:ℕ): ∃ z:ℕ→Side,(∀ i,Even (z i).val) ∧ Tendsto (fun i=>(z i).val) atTop atTop:=by
 let F(i:ℕ):Side:=⟨2*i+2,by omega⟩; refine ⟨F,fun i=>⟨i+1,by change 2*i+2=i+1+(i+1); omega⟩,(strictMono_nat_of_lt_succ (show ∀ i:ℕ,(F i).val <(F (i+1)).val from fun i=>by change 2*i+2< 2*(i+1)+2; omega)).tendsto_atTop⟩
-- Curtain comparison from H sphere to ground.GK scales assigned AFTER forest to cover spin schedule data. We can prove finalIncome limit by diagonal through comparison with arbitrary AP (not elections); dependencies reason r>0 only
omit p
omit hp τz e vD in
private lemma hires_p(X:ℕ→Chisel)(R:ℕ→ℝ)(p:∀ i:ℕ,0<R i)(h:Tendsto R atTop atTop): ∃ (N:ℕ→Side)(M:ℕ→Male), Yard N R ∧∀ i:ℕ, dist ((R i:ℂ)^3*(X i).finalIncome) ((R i:ℂ)^3*(X i).stage (N i) (M i)) ≤ 1/R i :=by
 classical
 obtain ⟨y,a,g⟩:= hires 0; let m(j:ℕ):Male:= ⟨⟨2*j+1,by omega⟩,j,(by change 2*j+1=_ ; omega)⟩; -- Odd number target 2*j+1? Odd definition mul.or. 
 have ht:Tendsto (fun i=>(m i).val.val) atTop atTop:=StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (by intro i; unfold m; change 2*i+1< 2*(i+1)+1; omega));
 have hh(i): ∃ k, dist ((R i:ℂ)^3*(X i).finalIncome) ((R i:ℂ)^3*(X i).stage (y k) (m k)) ≤ 1/R i ∧ R i*Ember.pinch (y k) ≤ 1/R i :=by
    let F:ℝ:=1/R i; have hp:0<F:= one_div_pos.mpr (p i); have he:= ((X i).authorized (M_:=m) ht g a).2.const_mul ((R i:ℂ)^3); have hx:= Metric.tendsto_nhds.mp he F hp; let V(k):=Ember.pinch (y k)
    have hv: Tendsto V atTop (𝓝 0):= Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop.comp g) _; have hw:Tendsto (fun k=> R i*V k) atTop (𝓝 0):= (mul_zero (R i)) ▸ hv.const_mul (R i)
    refine (hx.and (hw.eventually (ge_mem_nhds hp))).frequently.exists.imp ?_; intro i j; refine ⟨dist_comm .. |>.trans_le j.1.le, j.2⟩ -- tune
 choose k hp hk using hh; refine ⟨fun i=>y (k i), fun i=>m (k i), ⟨p,h,?_,fun i=> a (k i)⟩,hp⟩; exact squeeze_zero (fun i=> mul_nonneg (p i).le (pinch_pos _).le) hk (Tendsto.const_div_atTop h 1)
lemma accolade (H:Tendsto R atTop atTop)(P:∀ i:ℕ,0<R i): Tendsto (fun i=>(R i:ℂ)^3*(X i).finalIncome) atTop (𝓝 ((pencil Y) d u)) :=by
 obtain ⟨N,M,p,Q⟩:= hires_p X R P H; have hp:= curtain (N_:=N) (M_:=M) p Y hp τz e vD
 refine hp.congr_dist (squeeze_zero (fun _=>dist_nonneg) (fun i=>?_) (Tendsto.const_div_atTop H 1)); exact (dist_comm ..).le.trans (Q _)
end PolarF
end Niagara
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
