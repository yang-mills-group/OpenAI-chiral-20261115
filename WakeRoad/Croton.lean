import WakeRoad.Tenax
import WakeRoad.Tallow
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
open CF.Onyx
open CF.Gingham.Ruff Spine.Gingham.VoyageB
open UVNext.FreeStress
variable (P:Spine)(r:ℕ→ℕ)
local notation "iₛ" i:max=>P.period (P.projection.rows (r i))
local notation "kₛ" i:max=>P.cutoff (P.projection.columns (r i))
local notation "nDoc" s:max i:max=>side P.run (iₛ i) s
local notation "Mₛ" s:max i:max=>P.par.V.L.H ((P.run).uv (kₛ i)-s)
local notation "R*" s:max=> ((↑(2*ArborJet.moment P s:ℕ):ℂ))
local notation "ff"=> (4* Maxwell.normal)
variable {m:ℕ}
variable (s n:ℕ)
local notation "K"=>RootBook P.run (iₛ n) (kₛ n) s
local notation "ι"=>Postcard ((K).p.B/10)
variable {a c μ:ℝ}{l:ℕ}{δ C:ℝ}(B:Scene P a c μ l s (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))))(X:Rialto 6 P.par.d δ C)
local notation "A*" b:max=> grove P s (iₛ n) (kₛ n) b
local notation "w*"=> cocoa P s (iₛ n) (kₛ n) B X
local notation "G*" b:max=>combo P s (iₛ n) (kₛ n) B X b
-- scaledAtlas floors at C floors group
private lemma subsidy (ρ R:ℝ)(bucket:ℝ)(p:0<bucket)(hU:1≤4*ρ^4)(H W I:ℂ) (l:bucket ≤ I.re)
   (z:‖W-I‖≤bucket/2) (e:(R:ℂ)^8*H=(ρ:ℂ)^4*W):
 bucket / 8 ≤ ((R:ℂ)^8*H).re := by
 rw [e]; have hb:= Complex.re_le_norm (I-W); rw [Complex.sub_re,norm_sub_rev] at hb
 rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero]
 have hp:0≤ρ^4:=by positivity
 have hg:=mul_le_mul_of_nonneg_left (show bucket/2≤W.re from by linarith) hp; nlinarith
open Spine.Gingham
variable {r' f:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ l r' F)(w:StrictMono f) (pA:Anthem P a c μ l δ C X)(hd:0<δ)
include β w pA hd
-- r = r'∘f, scheme. pooling β real commands.
lemma mortgage {κ:ℕ→ℝ}(HM:Pooling P.run (P.period∘P.projection.rows) (P.cutoff∘P.projection.columns) (r'∘f) κ) :
 ∃ q'> (0:ℝ),∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,
   let i:=Diary.irr P ((r'∘f) n); let k:=Diary.uvv P ((r'∘f) n);
   Nonempty (Scene P a c μ l s i k) ∧ ∀ B:Scene P a c μ l s i k, let R:=κFix κ s; let r:=(r'∘f);
     q' ≤ (((((↑(2*ArborJet.moment P s:ℕ)):ℂ)^8)*(visage P r s n B X R - atlas P r s n B X R true * atlas P r s n B X R false))).re:=by
 let r:= r'∘f
 obtain ⟨D,d,h,L⟩:=chargeMirror P a c μ l X hd β.aP pA (ν:=r) HM.up.tendsto_atTop
 let q₀:= fun z:oxygen=> clair δ z.1 z.2
 obtain ⟨η,v,g⟩:=glitter q₀ d h
 let Y := (ff)^2*(2*η^2)
 have hY: 0<Y:=by unfold Y; have h:= Maxwell.normal_pos; positivity -- Y captures namespace Yoke^
 let a':= |D|+1
 have h':0<a':=by unfold a'; positivity
 refine ⟨Y/8,by positivity,?_⟩
 filter_upwards [L, income_delta P r HM.up a' h' (Y/2) (half_pos hY), β.clearFor 1 zero_le_one 2 le_rfl] with j t x y
 let θ := κFix κ j; have M : ∀ᶠ n:ℕ in atTop,9/10 < reachCost P.run j (Diary.irr P (r n)) (Diary.uvv P (r n)) θ:= (Gathering P.run HM j).eventually (lt_mem_nhds (by norm_num)) -- wrong lt implies greater? gt_mem_nhds upper. need ρ≥√(1/2)=.707 instead use 9/10
 filter_upwards [t,x,w.tendsto_atTop.eventually y.1,M] with n t x p tM
 let i:=Diary.irr P (r n); let k:=Diary.uvv P (r n); let q:=RootBook P.run i k j
 dsimp only; refine ⟨⟨p⟩,fun B=>?_⟩
 obtain ⟨ht,u,z⟩:=t B
 let T':=cocoa P j i k B X
 specialize x B.gears.boot.B T' (ht.trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)))
 let K':=affinity braid_st (portrait true T') (portrait false T')
 have hv:δ>0:=hd
 have hh:d ≤ ‖WakeRoad.Score (WakeRoad.compact takeIn T') q₀‖:=by
   rw [←compass_score]; exact u.le.trans (Complex.re_le_norm _)
 have H:Y ≤ K'.re:=by
    rw [show K'= _ from affinity_charge (U:=T') (fun i j=>(revision ..)),Complex.real_smul];
    rw [← Complex.ofReal_ofNat, ←Complex.ofReal_mul, ←Complex.ofReal_mul, Complex.ofReal_re]; unfold Y; gcongr; exact (g _ hh).le
 let W := affinity (salute P r j n) (portrait true T') (portrait false T')
 have hq:1 ≤4*(reachCost P.run j i k θ)^4:=by
    have hh: (9/10:ℝ)^4≤ (reachCost P.run j i k θ)^4:=by gcongr
    exact le_trans (by norm_num: (1:ℝ)≤4*(9/10:ℝ)^4) (mul_le_mul_of_nonneg_left hh (by norm_num))
 have he:= scaledAtlas P r j n B X θ B.ok.le
 exact (subsidy _ (↑(2*ArborJet.moment P j):ℕ) Y hY hq _ W K' H x (by push_cast at he ⊢; exact he))
#print axioms mortgage
