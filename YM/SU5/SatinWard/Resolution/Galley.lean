import YM.SU5.SatinWard.Resolution.Stoop
import YM.SU5.SatinWard.Resolution.Gips
import YM.SU5.SatinWard.Resolution.SandGlass
import YM.SU5.SatinWard.Resolution.TunicW
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
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
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal
open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
local notation "Y"=> P.run
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} {Z:Visit→ Cover → Family P.calibration} {χ:Division}{d:PitchZ}
variable (E:Ceremo P η v P.jump128 f0 a b φ H A χ D Z d)(q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)
local notation "Ξ" u:max=> cloakF P M p (E.earnedZ P η u) v
local notation "Δ"=> cloakF P M p (logStarCore P η E) v
local notation "X" v:max=> hat P.par.R.L P.par.x v
local notation "Yw" v:max=> (hueW P.par.R.L (X v))
local notation "h★" v:max=> (↑(Yw v):ℂ)
local notation "h△" v:max=>(↑(qHull P.par.R.L (X v)):ℂ)
local notation "h❖" v:max=>(↑(jHull P.par.R.L (X v)):ℂ)
local notation "TΔ" i:max=> Ξ (some i)
noncomputable abbrev incMove(i:Axis)(b:Bool):Cover:= if b then step i else -(step i)
local notation "δt" => incMove -- okay
local notation "VH" i:max b:max=> (P.chartAll (δt i b) (TΔ i).F)
local notation "KZ"=> (h★ v/h△ v)
local notation "KW"=> (h★ v/h❖ v)
lemma income_tape : (Δ).F = (h★ v/h△ v) • (Ξ none).F +(h★ v/h❖ v) • ∑ i:Axis,(VH i true - VH i false):=by
 let w:= tauprint P M p; let g(i:Axis)(b:Bool):= VH i b; have he(i b): g i b= chapterFoot P (E.earnedZ P η (some i)) (w+pmZ ζ i b):=by
    change P.chartAll _ (chapterFoot P (E.earnedZ P η (some i)) w)=_; rw [calendar_moves,show ζ • (incMove i b)= pmZ ζ i b from ?_]; unfold incMove pmZ; cases b<;>simp
 apply Subtype.ext; change fullStar P.par v P.jump128 Z w=_; unfold fullStar; dsimp only; simp only [←Complex.coe_smul,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,Pi.sub_apply]
 change ((↑(_/_ :ℝ):ℂ)) • _ + (↑(_/_ :ℝ):ℂ) • _= _ + KW • (((∑ i:Axis, (g i true-g i false)):P.Test):Family P.calibration) -- tune lhs.Bew
 simp_rw [Complex.ofReal_div]; apply congrArg; rw [show (((∑ i:Axis,(g i true-g i false)):P.Test):Family P.calibration)= ∑ i:Axis,((g i true).val-(g i false).val) from ?_]; simp_rw [he]; rfl
variable {s:ℕ} -- remove F shadow
-- data relative at lag Rent is *uncompressed* at x, not a.ℋ across v yet. Useful Motion.Set
variable (i:Axis)(x:P.Spectrum0 i){f:ℕ}(hp:f ≤ v){l r:ℝ}
local notation "tₖ" i:max u:max => P.tock v ((u:Cover) i)
local notation "Q₀"=> home P q v i
local notation "𝔤"=> P.Grips i x v (-(l-Q₀)) (r+Q₀)
local notation "ℛ"=>P.charter i x
noncomputable def galley (v:ℕ)(k:Cover)(D:P.RawLag i x)(l r:ℝ): (P.ColorHil i x).Op:=ℛ (P.vtile v k) (D (l+P.tock v (k i)) (r-P.tock v (k i))) -- pi tolerance
private noncomputable def hereP(q:Cover)(u:Cover)(Xp:P.Apron)(v:ℕ)(l r:ℝ):= galley P i x v u (fun l r=> P.rawBase i x Xp (l-home P q v i) (r+home P q v i)) l r
lemma gripsH (q:Cover)(B:P.Apron)(u:Cover)(h:B.s=v)(u₀:B.realWidth P i≤l+tₖ i u-home P q v i)(v₀:B.realWidth P i≤ r-tₖ i u +home P q v i): P.Grips i x v (-(l-home P q v i)) (r+home P q v i) (P.chartAll u B.F) (hereP P i x q u B v l r):=by -- q binder collision α Q₀ section include? hereP binder also q hygiene; use shift.D. compile.
 let y:=home P q v i; let o:=tₖ i u; unfold hereP galley; dsimp only
 subst v; rw [show r-(P.tock B.s (u i))+ y=r+y-P.tock B.s (u i) from by abel, show l+ P.tock B.s (u i)-y=P.tock B.s (u i)- -(l-y) from by abel]; apply P.grasp_place i x B u <;> linarith only [u₀,v₀] 
variable (yu:|home P q v i| ≤ P.macroStep v)
lemma inc_wallet (j:Axis)(b:Bool): |tₖ i (δt j b)| ≤ P.macroStep v:=by
 have ht(i:ℤ): |P.tock v i|= |(i:ℝ)| *σ v:=by rw [tock_price, abs_mul,abs_of_pos (P.macroStep_pos ..)]
 rw [ht]; apply le_trans ?_ (Eq.le (one_mul (σ v))); apply mul_le_mul_of_nonneg_right _ (P.macroStep_pos _).le; unfold incMove; by_cases e:i=j<;> cases b <;> simp [e,Ne.symm] -- tune
variable (k₁:16*(deltaWing P (rentWidth P P.jump128 v):ℝ)*P.macroStep v≤ moonClock P s)
variable (t:3*P.macroStep v≤ moonClock P s)(hl:2*moonClock P s ≤ l)(hr:2*moonClock P s≤ r)
local notation "y★" A:max=> P.rawBase i x A (l-Q₀) (r+Q₀)
local notation "P₂" j:max b:max=> hereP P i x q (δt j b) (TΔ j) v l r
local notation "V₂" j:max b:max=> VH j b
local notation "o₁"=> (Δ).F
local notation "o₀"=> (Ξ none).F
include t hl hr k₁
lemma anchor_balance : y★ Δ= KZ • y★ (Ξ none) + KW • ∑ j:Axis,(P₂ j true-P₂ j false):=by
 let u:=σ v; let δ:=moonClock P s; have ht:=abs_le.mp (home_room P p v i)
 have H0(W:ℕ)(f:W≤ rentWidth P ζ v): (deltaWing P W:ℝ)*σ v ≤ δ:=by -- edit
    let g:=Nat.cast_le (α:=ℝ)|>.mpr (show deltaWing P W ≤ deltaWing P (rentWidth P ζ v) from (by unfold deltaWing; omega)); let v:=mul_le_mul_of_nonneg_right g (P.macroStep_pos v).le; linarith only [v,k₁,clockP P s] -- k₁ mulassoc? linarith non-linear constant; ring
 have h₁ (F:P.Apron)(h:F.s=v)(w:F.realWidth P i≤ δ): 𝔤 F.F (y★ F):=by
    have he:= P.grasp_fixed i x F (a:=l-Q₀) (by linarith only [t,hl,ht.2,w,P.macroStep_pos v]) (b:=r+Q₀) (by linarith only [t,hr,w,ht.1,P.macroStep_pos v])
    rw [h] at he; exact he
 let o' := o₀; let F := y★ Δ
 have hx:𝔤 o₁ F:=h₁ Δ rfl (by rw [real_cloak]; exact H0 _ (starPad (j:=ζ) ..))
 apply hx.unique; rw [income_tape P η E q p M]; apply Grips.add; · exact (h₁ (Ξ none) rfl (by rw [real_cloak]; exact H0 _ (widthPaid ..))).smul _
 apply Grips.smul; apply Grips.sum; intro j _
 have hq: (Ξ (some j)).realWidth P i≤δ:=by rw [real_cloak]; exact H0 _ (widthPaid ..)
 let u' b:= gripsH (v:=v) P i x (l:=l) (r:=r) q (TΔ j) (δt j b) rfl (by have e:= (abs_le.mp (inc_wallet P (v:=v) i j b)).1; linarith only [t,hq,hl,e,ht.2,P.macroStep_pos v]) (by have e:=(abs_le.mp (inc_wallet P (v:=v) i j b)).2; linarith only [t,hq,hr,e,ht.1,P.macroStep_pos v])
 rw [sub_eq_add_neg (V₂ j true), sub_eq_add_neg (P₂ j true),← neg_one_smul ℂ (V₂ j false), ←neg_one_smul ℂ (P₂ j false)]; exact (u' true).add ((u' false).smul _)
omit t hl hr k₁
noncomputable def evdiv (D: Axis → P.RawLag i x)(v:ℕ)(l r:ℝ):= ∑ j:Axis,(galley P i x v (δt j true) (D j) l r-galley P i x v (δt j false) (D j) l r)
local notation "𝒥" j:max=> lined P M i x f q hp (Ξ (some j))
local notation "ℰ₀"=> lined P M i x f q hp Δ
local notation "ℰ₁"=> lined P M i x f q hp (Ξ none)
include t hl hr k₁
lemma clockLine : (ℰ₀ l r)= KZ • (ℰ₁ l r) + KW • evdiv P i x (fun j=> 𝒥 j) v l r:=by
 change ℛ (chair P M q hp) (y★ Δ)= _; rw [anchor_balance P η E q p M i x k₁ t hl hr]; -- arguments!
 unfold evdiv; rw [P.charter_add,P.charter_smul,P.charter_smul,P.charter_list]; refine congrArg₂ (·+·) rfl ?_; apply congrArg; apply sum_congr rfl; intro j _; rw [P.charter_sub]
 have he(b:Bool): ℛ (chair P M q hp) (P₂ j b)=galley P i x v (δt j b) (lined P M i x f q hp (TΔ j)) l r:=by
    unfold hereP galley lined; simp only; rw [P.charter_sum,P.charter_sum,add_comm (chair P M q hp)]; rfl
 exact congrArg₂ (·-·) (he true) (he false)
#print axioms clockLine
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
