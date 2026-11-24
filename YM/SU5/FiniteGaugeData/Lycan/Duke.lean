import YM.SU5.FiniteGaugeData.Lycan.Yawl
/-! # WP24b: joint P20 estimate and centered covariance. Paths at certain late but then fixed versions. -/
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
open Stationary Mir Royal
-- wires normal at x with i-apex; all species.Matter site support. real normalization.
variable (σ:Window.Family)(x y:Cover)(i n:ℕ)
-- color combin formulas (incl reused for onsite). interpret δ-read f.
section
variable {I D:Type*}(d:I→ Finset D){Q:Finset D} [DecidableEq D]
abbrev violet (c:I→I→ℂ)(i j:I×D):ℂ:= if i.2=j.2 then c i.1 j.1 else 0
local notation "Ν"=> I×D
lemma solos (x y:Ν) (C':Ν→Ν→ℂ): Album C' [(x,y)]= C' x y := by rw [spindle,slid]; change _*1-0=_; ring
lemma twos (x y p q:Ν) (C':Ν→Ν→ℂ): Album C' [(x,y),(p,q)]= C' x y * C' p q - C' x q * C' p y:=by rw [spindle,slid,slid,add_zero,solos,solos]; rfl
lemma cost_1(c:I→I→ℂ)(a:I)(h:d a=Q):Conv d (violet c) [a]=(Q.card:ℂ)*c a a:=by unfold Conv; rw [Silk]; simp_rw [Silk, solos, violet]; simp only [h,if_true,sum_const,nsmul_eq_mul]
lemma cost_2(c:I→I→ℂ)(a b:I)(h:d a=Q)(t:d b=Q): Conv d (violet c) [a,b]=(Q.card:ℂ)^2*c a a*c b b-Q.card*c a b*c b a:=by
 unfold Conv; rw [Silk]; simp_rw [Silk,twos,violet]; -- projection simp maybe invalid
 let M:= Q.card; simp only [if_true, sum_sub_distrib,h,t];
 have he (i:D)(p:i∈Q): (∑ j∈Q,(if i=j then c a b else 0)*(if j=i then c b a else 0))= c a b*c b a:=by
    rw [sum_eq_single i]; · simp
    · intro v h g; rw [if_neg g,mul_zero]
    exact fun v=> (v p).elim
 rw [sum_congr rfl he,sum_const,sum_const,sum_const]; simp only [nsmul_eq_mul]; ring -- tune nested rw sum_const dependent
end
local notation "Ω"=> absoluteP (fun _:Bool=>σ) (fun _=>0) (fun _=>2) aSpan
local notation "YH" n:max=> earthV (Royal.fuao n)
local notation "d'"=> (dimf σ:ℂ)
def leadRead(b a:Bool): ℂ:= Window.kernel (dayb b a)
private lemma formatC : specter (fun _=>0) (fun _=>2) aSpan= violet leadRead:=by funext i j; unfold specter violet aSpan leadRead; congr 1; rw [show (0:SpinIdx)= upSpin 0 from rfl,show (2:SpinIdx)=dnSpin 0 from rfl,pencil_time,if_pos rfl] -- maybe syntax partial in congr
private lemma self_c(a:Bool): leadRead a a=P20:=by cases a <;> rw [P20_value]<;> norm_num [leadRead,dayb,morphK,Window.kernel,one_div] -- tune
private lemma treble: leadRead false true=P20/64 ∧ leadRead true false= -P20/8:=by rw [P20_value]; norm_num [leadRead,dayb,morphK,Window.kernel,one_div]; constructor<;> ring
private lemma waltz(b:Bool): (Ω) [b]= d' * P20:=by unfold absoluteP; rw [formatC,cost_1 _ leadRead b (Q:=Window.colors σ) rfl,colors_card,self_c]
def dimR(σ:Window.Family):ℝ:= dimf σ
lemma dimH:0<dimR σ:= Nat.cast_pos.mpr (dimf_pos _)
-- normalize externally dim expensive maybe choose mean d'. state normalized aesthetically.S/thermal.
abbrev Restamp(σ:Window.Family):ℝ:= (1/Real.pi^2)^2/ (512*dimR σ)
lemma onR:0< Restamp σ:=by unfold Restamp; have hp:=dimH σ; have he:=Real.pi_pos; positivity
lemma cashRest: (Restamp σ:ℂ)= P20^2/(512*d'):=by unfold Restamp; rw [P20_value]; unfold dimR; push_cast; rfl
abbrev rV(σ:Window.Family):ℂ:=P20^2+(Restamp σ:ℂ)
private lemma proudV:(Ω) [false,true]= d'^2*(P20^2+Restamp σ):=by unfold absoluteP; rw [formatC,cost_2 _ leadRead false true (Q:=Window.colors σ) rfl rfl,colors_card,self_c,self_c,treble.1,treble.2,cashRest]; have hp:0<dimf σ:= dimf_pos σ; have he:d'≠0:= Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp); field_simp; ring
abbrev chartC (K:Calibration)(n:ℕ)(x:Cover): W K:= ((earthV (Royal.fuao n)) / (dimf σ:ℂ)) • bookFee K (oculus σ x n)
-- variance top and loc
abbrev citadel(x:Cover)(n:ℕ):Finset Cover:= (oculus σ x n).town
lemma hallV(K:Calibration): Locator K (chartC σ K n x) (citadel σ x n):= locate_scale K _ _ (ProbeCode.Country K _).place
section
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ) {Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ}(H:Sphere Y h K R A Φ){ε:ℝ}
local notation "Kₜ"=> tent Y h
local notation "ΛF"=> W Kₜ
local notation "W°" σ:max x:max n:max=> chartC σ Kₜ n x
include K R A S' P'
private lemma spectV (X:List Bool) (e:0<ε): ∀ᶠ i:ℕ in atTop, ∀ᶠ s:ℕ in atTop, ∀ Φ:ℕ→ΛF→ₗ[ℂ]ℂ,Sphere Y h K R A Φ→ ‖earthV (fuao i)^X.length * Φ s ((X.map (localFee σ Kₜ x y i)).prod) - (Ω) X‖ ≤ ε:=by
 let L(i N Y):= lips (ferris σ x y i) Y N 1; have he(i N X): ((X.map (localPaint σ x y i)).prod N 1)=L i N X:=by induction X with | nil=>rfl | cons z l ih=> change localPaint σ x y i z N 1 * ((l.map (localPaint σ x y i)).prod N 1) = _; rw [ih,scent0]; rfl
 let P:= egg Y (X:=X) (Sesame.cantor σ x y) h K R A S' P' (fun i=> jungle (localSkin σ x y i Kₜ) (show ({(0:Cover)}:Finset Cover).Nonempty from singleton_nonempty _) X) (fun i N=> he i N X) e; exact P.mono fun i t=> t.mono fun z v=>v.2
lemma waltz_c(e:0<ε):∀ᶠ i:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ Φ:ℕ→ΛF→ₗ[ℂ]ℂ,Sphere Y h K R A Φ→ ‖Φ s (chartC σ Kₜ i x) -P20‖≤ε:=by
 have hp:0< dimf σ:=dimf_pos _; have hx:d'≠0:= Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp); have he:= norm_pos_iff.mpr hx; filter_upwards [spectV Y σ x x h K R A S' P' [true] (show 0< ‖d'‖*ε by positivity)] with i s₁; filter_upwards [s₁] with s v Φ H; have hv:=v Φ H; rw [waltz] at hv; let w := bookFee Kₜ (oculus σ x i); change ‖YH i^1*Φ s (w*1)-_‖≤_ at hv
 rw [mul_one,pow_one] at hv; refine le_of_mul_le_mul_left ?_ he; rw [← norm_mul, _root_.mul_sub, chartC,map_smul,smul_eq_mul, ← mul_assoc, show d' * ((YH i)/d')=(YH i) by field_simp]; exact hv
lemma doubleR(e:0<ε): ∀ᶠ i:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ Φ:ℕ→ΛF→ₗ[ℂ]ℂ,Sphere Y h K R A Φ→ ‖Φ s (helve Kₜ 3 (chartC σ Kₜ i x) (chartC σ Kₜ i y)) - (rV σ)‖ ≤ ε:=by
 have hp:0< dimf σ:=dimf_pos _; have hx:d'≠0:= Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp); let C:= d'^2; have he:= norm_pos_iff.mpr (show C≠0 from pow_ne_zero _ hx); filter_upwards [spectV Y σ x y h K R A S' P' [false,true] (show 0< ‖C‖*ε by positivity)] with i s₁; filter_upwards [s₁] with s v Φ H; have hv:=v Φ H; rw [proudV] at hv; let w := bookFee Kₜ (oculus σ x i); let W:= bookFee Kₜ (oculus σ y i); let K':=(YH i)/d'; change ‖(YH i)^2*Φ s (fire Kₜ 3 0 w*(W*1))- C*_‖≤_ at hv; rw [mul_one W] at hv; refine le_of_mul_le_mul_left ?_ he; rw [←norm_mul, _root_.mul_sub]; unfold helve; change ‖C*Φ s (fire Kₜ 3 0 (K' • w)*(K' • W))- C*rV σ‖ ≤_; rw [ice_paid,show star K'=K' by unfold K' earthV; simp,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,map_smul,smul_eq_mul,←mul_assoc,show C*(K'*K')=(YH i)^2 by unfold K' C; field_simp]; exact hv -- `K':` lex
end
#print axioms proudV
#print axioms doubleR
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
