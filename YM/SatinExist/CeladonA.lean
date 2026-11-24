import YM.SatinExist.Pepper
import YM.SatinExist.Verd
-- truly attain op budget on front conductor, WITHOUT supplying new coupling
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 340000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste Sonnet Lungo
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
variable (P:Spine)(R : P.Register)(j:Axis)(C A:ℝ)(Y:Supplier)(T:uniform P R Y C A)(D:P.NightCop)
local notation "W"=>P.calibration
local notation "Λ"=>P.par
local notation "Ψ"=>P.run
local notation "H"=>P.large
local notation "ℓ"=>P.calibration.ℓ
local notation "θ"=> P.tuneK
variable {w N a b':ℕ} {F:Weaver}{S:Finset Cover}(v: Lamour.Bridge.Celeste.Voice F S) (h:Clarity F P.par.K.j (1/4))
-- more-or-less any grid fixed lender. choose t large after request.
local notation "κ"=> P.calibration
open Aria
lemma mount_card (s:ℕ)(q:Between κ j (-(ruler P.par.block * w)) (ruler P.par.block*w) S): ∃ f:P.Card j s (w+w), P.voxTest j s f.val = P.shifts j w (P.tuneK v):=by
 let A:= θ v; let V:=P.shifts j w (A); let L:=plow κ j w S
 have hb:A∈bay κ S true:=(Tapestry.locates ..).2 ((v.1.narrow _).widen)
 have hd:= q.relocate κ j (w:ℤ); rw [show ruler (κ).B = ruler P.par.block from rfl, add_neg_cancel,←mul_add,← Nat.cast_add] at hd; let u:= P.shifts_support j (w:ℤ) S hb
 refine ⟨(⟨P.positiveVox j s L V u (fun p t=> (hd p t).1),L,u,hd⟩:P.Card j s (w+w)),rfl⟩
lemma card_slack (S:Finset Cover): ∀ᶠ w:ℕ in atTop, Between P.calibration j (-ruler P.par.block*w) (ruler P.par.block*w) S:=by
 let r:=ruler P.par.block
 refine S.eventually_all.mpr (fun p h=>?_)
 filter_upwards [eventually_ge_atTop ((p j).natAbs+ℓ)] with n e; have hp: (n:ℤ) ≤ r*n:= le_mul_of_one_le_left (by positivity) (ruler_gene _); rw [neg_mul]; unfold r at *; omega
open CF.Velvet Casting
include h T D
lemma controlsUV :∀ᶠ s:ℕ in atTop,∀ x:P.Spectrum0 j, ‖P.singleState j s x (P.tuneK v)‖ ≤ Real.sqrt (RedD+3):=by
 obtain ⟨a,q⟩:=eventually_atTop.1 (P.card_slack j S); obtain ⟨w,g,f⟩:=P.pay_arena R j C A Y T D v h a; have hp:0<w+w:=by omega
 filter_upwards [f] with s t x; obtain ⟨L,k⟩:= mount_card P j v s (by rw [←neg_mul]; exact q w g.le) -- change neg
 let X:=P.voxTest j s L.val; let U:=P.colorSpace j x; have hu:X∈enclave κ:=by rw [show X= _ from k]; exact P.shifts_keep _ _ (P.celebrity v)
 let Ω:=P.colorZero j x; let J:= P.door j s (w+w) hp L hu; let F':=(U J)
 have hy: ‖F'‖ ≤ Real.sqrt (RedD+3):= (NonUnitalStarAlgHom.norm_apply_le U J).trans (t L k)
 have hx:‖Ω‖=1:=P.norms_color j x; rw [← P.slide_single j x s w (θ v),← k,←P.view_scalar j x s (P.admitted_view j s L hu),←P.attended]; exact (norm_inner_le_norm ..).trans ((by rw [hx,one_mul]; exact (F'.le_opNorm Ω).trans (by rw [hx,mul_one]; exact hy)))
-- docs mention ≠registration etc.
omit h
local notation "J"=>P.par.K.j
lemma richC {F:Weaver}{S:Finset Cover}{e:ℝ}(p:0<e)(v: Lamour.Bridge.Celeste.Voice F S)(c:ℂ) (a:ℝ)(f:0<a)(q:Clarity (meanF F c) P.par.K.j ((1/4)/a)) (t:Real.sqrt (RedD+3) < a*e):∀ᶠ s:ℕ in atTop, ∀ x:P.Spectrum0 j, ‖P.singleState j s x (P.tuneK v) - c‖ < e:=by
 let G:= meanF F c; have h:Clarity ((a:ℂ) • G) J (1/4):=by
    filter_upwards [q] with N h y M x z; have hu:=h y M x z; rw [Pi.smul_apply,Pi.smul_apply,map_smul,norm_smul,Complex.norm_real, Real.norm_eq_abs,abs_of_pos f,mul_comm]; exact (le_div_iff₀ f).1 hu
 let b:=v.sub ((Voice.one S).hushed c); let K:=b.hushed (a:ℂ); filter_upwards [controlsUV P R j C A Y T D (v:=K) h] with s k x
 have hk: θ K= (a:ℂ) • (θ v -c • (1:P.Test)):=rfl; have hs:= (k x).trans_lt t; rw [hk,map_smul,map_sub,map_smul,show (P.singleState j s x) 1=1 from (by rw [P.single_state,P.reading_unit,map_one]),show c • (1:ℂ)= c from mul_one _,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos f] at hs; exact lt_of_mul_lt_mul_left hs f.le
private abbrev giftUV (v:Lamour.Bridge.Celeste.Voice F S) (x:P.Spectrum0 j)(s:ℕ):=P.singleState j s x (P.tuneK v)
open Ballad Chalice
open YM.Stationary (Gaia)
variable {I:Type}(Z:I→ Stone)(O:ℕ→ I → Cover)(L:List I)(E:I→ Gaia) (y:P.Spectrum0 j)(e:ℝ)
local notation "x'"=> P.giftUV
-- exact consumption for these appointments. ALL character sync. cutoff first lift cost.
open Emu Onyx Flare
lemma matterU (n:ℕ→ℕ)(p:Tendsto n atTop atTop) (b:∀ i,Tendsto (fun s:ℕ=>riseX (n s:ℝ) (O s i)) atTop (𝓝 (E i))) (v:∀ i j,E i=E j→ ∀ᶠ t in atTop,O t i=O t j)(g:0<e) : ∀ᶠ R₀ in atTop, ∀ᶠ s:ℕ in atTop, ∀ x:P.Spectrum0 j, dist (P.singleState j s x (P.tuneK (pressC Z (O R₀) L (R:=n R₀)))) (depictionC Z L E)< e:=by -- Core taste
 let d:=Real.sqrt (RedD+3); let w:=d/e+1; have hp:0<w:=lt_add_of_le_of_pos (div_nonneg (Real.sqrt_nonneg _) g.le) zero_lt_one
 have hb:d<w*e:= lt_add_of_le_of_pos (le_refl _) g |>.trans_le (le_of_eq (by unfold w; rw [add_mul, one_mul,div_mul_cancel₀ _ g.ne'])) -- syntax redo
 filter_upwards [fanC Z O L E J n p b v ((1/4)/w) (by positivity) (by rw [P.par.kJ]; decide)] with k h; let F':= depictionC Z L E; have ht:=P.richC R j C A Y T D g (pressC Z (O k) L (R:=n k)) F' w hp h hb
 filter_upwards [ht] with s p x using (dist_eq_norm ..).trans_lt (p x)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
