import YM.SU5.SatinWard.Resolution.OrielR
import YM.SU5.SatinWard.Resolution.Timpani
import YM.SU5.SatinWard.Resolution.BroochA
import YM.SU5.SatinWard.Resolution.Carnation
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Synod
import YM.SU5.SatinWard.Resolution.Achilles
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
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
open CF.Fir _root_.YM.Regis.Circuit.SpringDay.Spring
variable {s:ℕ}
local notation "ζ"=> CF.Papyrus.Franc.SatinForce.Flash
local notation "K₁"=> principalKid
local notation "K₀"=> Op SU.Slot
-- economy grouping spin then family.Q equals trace pairing
open MeasureTheory
namespace Orchid
open Mezzo SoulField
abbrev GKey:= Coords Wage3
abbrev ZKey:= Wage3 → ℂ
-- complex extension for rank; no Wick or Fock payments from complex assumption Herm; spin tests combine actual paid real glyphs.
noncomputable abbrev convey (x:Wage3): Op SU.Slot:=dynamicSpin (ShapeLab.leg x)
noncomputable def rangeHue (z:ZKey) : Op SU.Slot:= ∑ x:Wage3,z x • convey x
noncomputable def silenceE (z:GKey):ZKey:= fun i=> z i
noncomputable def whisperR (z:ZKey):GKey:= fun i=> Complex.re (z i)
noncomputable def whisperI (z:ZKey):GKey:= fun i=> Complex.im (z i)
lemma giveH (p:GKey):dynamicSpin p=∑ x:Wage3,p x • convey x:=by
 let F:= (chiralModule.subtype).comp Θc.equivFun.symm.toLinearMap; have h:= (ShapeLab.columns_map F); exact (DFunLike.congr_fun h p).symm -- give.Hue
lemma giveY (z:GKey): dynamicSpin z= rangeHue (silenceE z):=by unfold rangeHue silenceE; rw [giveH]; exact sum_congr rfl fun x _=>(Complex.coe_smul ..).symm
lemma softT (z:ZKey): rangeHue z= dynamicSpin (whisperR z)+Complex.I • dynamicSpin (whisperI z):=by
 rw [giveY,giveY]; unfold rangeHue silenceE whisperR whisperI; rw [smul_sum,←sum_add_distrib]; refine sum_congr rfl (fun x _=>?_); rw [smul_smul,←add_smul, mul_comm Complex.I _,Complex.re_add_im]
lemma form_currency (q:GKey): ChiralX 0 (dynamicSpin q):=(Θc.equivFun.symm _).property
private lemma star_goal {A B: Herm SU.Slot} (t:A.val+Complex.I • B.val=0): A=0∧ B=0:=by -- use injectivity inkFinite+hermInk inaccessible private; add public wrapper there or repeat
 have h:= congrArg star t; rw [star_add,star_zero,star_smul,star_quiet,star_quiet, Complex.star_def,Complex.conj_I,neg_smul] at h; have e:Complex.I • B.val=0:=by
    have ht:=eq_neg_of_add_eq_zero_left t; rw [ht] at h; refine (smul_eq_zero.mp (?_:(2:ℝ) • (Complex.I • B.val)=0)).resolve_left (two_ne_zero (α:=ℝ)); rw [two_smul ℝ]; rw [←neg_add_rev,neg_eq_zero] at h; exact h
 rw [e,add_zero] at t; exact ⟨Subtype.ext t,Subtype.ext ((smul_eq_zero.mp e).resolve_left Complex.I_ne_zero)⟩
lemma awakeH (z:ZKey)(q:rangeHue z=0): z=0:=by
 rw [softT] at q; let Q(p:GKey): ↥(Herm SU.Slot):=⟨dynamicSpin p,(form_currency p).2⟩; obtain ⟨q,t⟩:= star_goal (A:=Q (whisperR z)) (B:=Q (whisperI z)) q
 have hz(p:GKey)(f:Q p=0):p=0:=Θc.equivFun.symm.injective (by rw [map_zero]; exact Subtype.ext (congrArg (fun g:↥(Herm SU.Slot)=>g.val) f)); let g(i):=(congrFun (hz _ q) i); let v(i):=(congrFun (hz _ t) i); funext i; exact Complex.ext (g i) (v i)
noncomputable def rateM : ZKey →ₗ[ℂ] Op SU.Slot where
 toFun:= rangeHue
 map_add' x y:= by simp only [rangeHue,Pi.add_apply,add_smul,sum_add_distrib]
 map_smul' x y:= by simp only [rangeHue,Pi.smul_apply,smul_sum,RingHom.id_apply,mul_smul,smul_eq_mul]
noncomputable def quireM (z:ZKey):ℝ:= ∑ i:slotPair,‖rangeHue z i.1 i.2‖^2
noncomputable def starKey (z:ZKey): ZKey:= star z
lemma hueCC (z:ZKey): rangeHue (starKey z)=star (rangeHue z):=by simp only [rangeHue, star_sum, star_smul,starKey, Pi.star_apply]; exact sum_congr rfl fun i _=> congr_arg ((star (z i)) • ·) ((form_currency _).2.symm)
lemma clear_quadratic (z:ZKey)(q:z ≠ 0):0 < quireM z:=by
 have hea:= mt (awakeH z) q; let A:=rangeHue z; change A≠0 at hea; have he:∃ i j:SU.Slot, A i j ≠0:=by contrapose! hea; ext i j; exact hea i j -- unicode e problem
 obtain ⟨i,j,t⟩:= he; exact sum_pos' (fun _ _=> sq_nonneg _) ⟨(i,j),mem_univ _,sq_pos_of_pos (norm_pos_iff.mpr t)⟩
lemma quireSale(z:ZKey): puBand (rangeHue (starKey z)) (rangeHue z)= (quireM z:ℂ):=by
 rw [hueCC]; unfold puBand quireM; rw [Complex.ofReal_sum,←Equiv.sum_comp (Equiv.prodComm SU.Slot SU.Slot) (fun i:slotPair=> ((‖rangeHue z i.1 i.2‖^2:ℝ):ℂ))]; refine sum_congr rfl (fun i _=>?_); let a:= rangeHue z i.2 i.1; change star a * a=_; rw [mul_comm,Complex.star_def,Complex.mul_conj, Complex.normSq_eq_norm_sq]; rfl
#print axioms quireSale
-- Gram matrix continuous, min bound.E cost before θ rank.L
private lemma hInput (i:slotPair):Continuous (fun A: Op SU.Slot=> A i.1 i.2):= (show (Op SU.Slot) →ₗ[ℂ] ℂ from { toFun A:= A i.1 i.2,map_add' z w:=rfl,map_smul' z w:=rfl}).continuous_of_finiteDimensional
lemma quire_cont : Continuous quireM:=continuous_finsetSum _ (fun i _=>(((hInput i).comp rateM.continuous_of_finiteDimensional).norm).pow _)
lemma quire_pay :∃ e:ℝ,0 < e ∧ ∀ x:ZKey, ‖x‖=1→ e ≤ quireM x:=by
 let u: ZKey:= fun _=>1; have he:‖u‖ =1:=by change ‖(fun _ : Wage3=>(1:ℂ))‖=1; rw [pi_norm_const]; exact norm_one
 let S:= Metric.sphere (0:ZKey) 1; obtain ⟨x,v,a⟩:= (isCompact_sphere .. :IsCompact S).exists_isMinOn (show S.Nonempty from ⟨u,(mem_sphere_zero_iff_norm.mpr he)⟩) quire_cont.continuousOn
 rw [Metric.mem_sphere,dist_zero_right] at v; exact ⟨quireM x,clear_quadratic _ (by rw [← norm_ne_zero_iff,v]; exact one_ne_zero),fun x p=>a (Metric.mem_sphere.mpr (by rwa [dist_zero_right]))⟩
-- laminate rank test under ∑ glyphs.
local notation "Mζ"=> Op SU.Slot
lemma contour (x y:ZKey):puBand (rangeHue x) (rangeHue y)= ∑ i:Wage3, ∑ j:Wage3, x i*y j*puBand (convey i) (convey j):=by
 let f(A B:Mζ)(i:slotPair):= A i.1 i.2 * B i.2 i.1; have hV {I:Type}(X:I→ Mζ)(t:I→ℂ)(B:Mζ)(S:Finset I) : puBand (∑i∈S,t i • X i) B=∑ i∈S,t i*puBand (X i) B :=by
    unfold puBand; simp_rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,sum_mul, mul_sum,mul_assoc]; rw [sum_comm]
 have ht(A B:Mζ):puBand A B=puBand B A:= by
    unfold puBand; rw [←Equiv.sum_comp (Equiv.prodComm SU.Slot SU.Slot) (fun i:slotPair=> B i.1 i.2 * A i.2 i.1)]; exact sum_congr rfl (fun i _=> mul_comm ..)
 unfold rangeHue; rw [hV]; refine sum_congr rfl (fun i _=> ?_); rw [ht,hV,mul_sum]; exact sum_congr rfl fun j _=>by rw [ht (convey j), mul_assoc]
#print axioms quire_pay
end Orchid
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
