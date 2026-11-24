import GaugeFieldConstruction.CaliphR
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.

local notation "ΤΓ"=> P.run
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (x:P.VMark)(R:Signed × Bool)(u:BandS)
local notation "Ξu"=> Fin (θ u)
local notation "η"=> FrameK (Fin (θ u))
variable (pu:Adept_T θ B0 M G)
-- Flexible anchor representation. stores assertion on arbitrary Movement Words.May align proofs of R3 via composition. KeyScope.S.
variable (L:finsJ)
local notation "Υs"=> ScaleμJ P.par u.val
-- CASH in force p P through procurement. preservation under Delayed (single.U)
local notation "ΚΡ"=> CalendarJ p B0 M
variable (A: CalendarJ p B0 M)
-- price limits of approximants.Any other heights at same point even with multiple gaps.N.Helper loan.
variable (T:LampHouseJ (θ:=θ) u) (D:P.Heritor)(V:LampΤJ p B0 M x R u A T D.path)
local notation "Zγ"=> FrameK (Fin (θ u))
local notation "ι" i:max=> D.path.subSeq i
local notation "gp" i:max=> P.gatePeriod (D.path.subSeq i)
local notation "gq" i:max=> P.gateCut (D.path.subSeq i)
local notation "βζ"=> FlavorRateJ P u
local notation "Κg"=> ΦWallet p
variable {f s l:ℕ}(g:f0≤ f)(s0:f0 ≤ s)
-- Portrait in all Habitat pads at Slabs.Location.Mar.K.Kernel.
local notation "νP" => RankQJ P.par
local notation "Kρ"=> p.price
local notation "gR" => RStepJ P.par
local notation "βρ" => stepRateJ P.par u.val
variable (σ τ:PermWallJ P) (i:Axis)(v:FrameK (Fin (θ u)))
open BoonsθJ Gleam BProof BProof.PricePort Gleam.Guide Gleam.clocks
open Fock.Flux
variable {d m:ℕ}
abbrev WrappR (D:P.Heritor)(m f d:ℕ)(o:Genre):ℂ:= let s:= SportR P m f; (Richm_R P m f:ℂ)^d * P.FireValue o s (D.β s) / RankQJ P.par s
-- ΦBasis: from ungraded.FrameK here at Lamph u. restore $Z bin.
def CartoonR (D:P.Heritor)(V:LampΤJ p B0 M x R u A T D.path)(g:f0≤ f)(m d:ℕ)(Z:Genre) : FrameK (Fin (θ u))→ₗ[ℂ] ScreensJ P:= (ΦCentered p B0 M x R u pu A T D V (g.trans (SportR.hop P m f))).comp (WrappR D m f d Z • (BrJ u (T.sun L (SportR P m f)).1))
local notation "Πκ"=> Panmart p B0 M x R u pu A T D V f0 le_rfl
-- center operator with full E. analogue sealed.
def CenterBudgetR (P:Spine) (s:ℕ)(F:P.Test):P.Test:= F-(P.publicBill s F) • 1
abbrev incomeVertR (F:P.Slabs i):= VirtueJ (P.publicH) i F
local notation "Ηβ"=> HeatTaxJ P i
abbrev centerP_R (P:Spine)(j:Axis)(A B:PermWallJ P)(F:P.Slabs j):= F-incomeVertR j F • CandΛJ P j A B
lemma budget_R(F:P.Slabs i) : ‖centerP_R P i σ τ F‖ ≤2*‖F‖:=by
 let s:=incomeVertR i F; exact (norm_sub_le _ (s • _)).trans (add_le_add_right (show ‖s • CandΛJ P i σ τ‖ ≤ ‖F‖ from (norm_smul _ _).le.trans ((mul_le_of_le_one_right (norm_nonneg _) (P.heat_norm i _)).trans (Vbudget i P.publicH _))) _|>.trans_eq (by ring)) -- tune
lemma virt_PlusR (X Y:P.Slabs i) : incomeVertR i (X+Y)= incomeVertR i X+incomeVertR i Y:= by simpa only [one_mul, one_smul] using Vfoot i P.publicH 1 X Y
lemma virt_ZR : incomeVertR (P:=P) i 0=0:=by unfold incomeVertR VirtueJ; rw[map_zero]; simp
lemma virt_SMPR (F:P.Slabs i)(z:ℂ): incomeVertR i (z•F)= z*incomeVertR i F:=by simpa only[add_zero, show VirtueJ P.publicH i 0=0 from virt_ZR _] using Vfoot i P.publicH z F (0:_)
private def linρR (P:Spine)(j:Axis): P.Slabs j→ₗ[ℂ] ℂ where
 toFun:= incomeVertR j
 map_add':=virt_PlusR j
 map_smul' i q:=virt_SMPR j q i
private def linΦR (σ τ:PermWallJ P)(i:Axis): P.Slabs i→ₗ[ℂ] P.Slabs i := LinearMap.id - (linρR P i).smulRight (CandΛJ P i σ τ)
lemma payC_R {w:P.Test}{F:P.Slabs i}(h:CallBoxJ x σ τ i w F l) : CallBoxJ x σ τ i (CenterBudgetR P l w) (centerP_R P i σ τ F) l :=by -- implicit binders
 unfold centerP_R incomeVertR; rw [CallΨJ P.publicH (MeanBylawsJ P) h]; exact h.minus ((UnitWallJ x σ τ i l).scale _)
local notation "q_f"=>RankQJ P.par
variable (Vt:Genre)
include g pu
lemma HeatCartoonR (a:f ≤ s)(Y:ℝ)(e:LoomK v ≤ Y)(z:BelowWallJ P σ τ f) : ‖ΦCentered p B0 M x R u pu A T D V (g.trans a) (BrJ u (T.sun L s).1 v) i σ τ‖≤ 2*(ΦWallet p*((2*Y)* RankQJ P.par s)):=by
 let S:=BrJ u (T.sun L s).1 v; let Q:= MeshΦ p B0 M x R u pu A T D V (g.trans a) S
 change ‖Q i σ τ- Heapψ P Q • _‖ ≤ _
 rw[show Heapψ P Q=incomeVertR i (Q i σ τ) from (ΦSkyJ p B0 M x R u pu A T D V (g.trans a) σ τ i S _ (MeanBylawsJ _)).symm]
 let h:= (HeatMarkJ p B0 M x R u pu A T D V g (g.trans a) σ τ i S z); unfold FarePQ at h; rw[if_pos a] at h; refine (budget_R σ τ i (Q i σ τ)).trans (mul_le_mul_of_nonneg_left (h.trans ?_) (by norm_num)); have hw:=p.price f g u s
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((weighΘ p B0 M x R u L A T D V (g.trans a) v).trans (mul_le_mul_of_nonneg_left e (by norm_num))) (hw.hot a le_rfl).le) (WalletB p).le
variable {w:ℝ}
omit pu
include p
lemma wrapR_fee : ‖WrappR D m f d Vt‖= TallyInR D m f d Vt:=by
 unfold WrappR TallyInR; dsimp only; rw [norm_div,norm_mul, norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Richm_good ..).le];
 let A:=RankQJ P.par (SportR P m f); congr 1; rw [show ‖(A:ℂ)‖=‖A‖ from Complex.norm_real _, Real.norm_eq_abs,abs_of_nonneg (p.tempo _ (g.trans (SportR.hop ..))).1.le] -- tune
abbrev CutVertR (D:P.Heritor)(m f d:ℕ)(x:Cover)(Z:Genre)(w:Waves):P.Test:= let s:= SportR P m f; (Richm_R P m f:ℂ)^d • D.stx s (x,Z,w)
abbrev SportRockR (D:P.Heritor)(m f d:ℕ)(x:Cover)(Z:Genre)(w:Waves):P.Test:= CenterBudgetR P (SportR P m f) (CutVertR D m f d x Z w)
include g
lemma WrappShip (Vt:Genre)(d:ℕ)(m:ℕ)(F:Waves) (S:LiPaJ B0 R u v=F):let s:= SportR P m f
 WrappR D m f d Vt • PaletteEJ B0 x R u D s v= CutVertR D m f d (P.adventJ x s) Vt F:=by
 intro s; subst F; rw [PaletteQ,map_smul]; unfold CutVertR Heritor.stx; rw [smul_smul,smul_smul]; congr 1; apply div_mul_cancel₀; exact_mod_cast (p.tempo s (g.trans (SportR.hop ..))).1.ne'
-- #80 analogue, also arbitrary X.R.V.Calendar evidence.
include pu V
lemma LightΘR (Vt:Genre)(d m:ℕ) (Y:ℝ)(F: Waves)(e:LoomK v ≤ Y)(S:LiPaJ B0 R u v=F)(z:BelowWallJ P σ τ f): let s:=SportR P m f
 ∃ X:P.Slabs i, CallBoxJ x σ τ i (SportRockR D m f d (P.adventJ x s) Vt F) X s ∧ ‖X-CartoonR p B0 M x R u pu L A T D V g m d Vt v i σ τ‖ ≤ 2*ΦWallet p*(TallyInR D m f d Vt * FlavorRateJ P u f s s (2*Y)):=by
 intro s
 let Q':=SportR.hop P m f; let w:=BrJ u (T.sun L s).1 v; obtain ⟨U,h,vU⟩:=LawΦsJ p B0 M x R u pu L A T D V g σ τ i v (g.trans Q') Q' z
 let M':= MeshΦ p B0 M x R u pu A T D V (g.trans Q') w; let A':= (T.sun L s).2 v; let H:=CandΛJ P i σ τ; let K:= M' i σ τ; let a':= WrappR D m f d Vt
 refine ⟨_,payC_R x σ τ i (show CallBoxJ x σ τ i (CutVertR D m f d (P.adventJ x s) Vt F) (a' • U) s from by rw [← WrappShip p B0 x R u D g v Vt d m F S]; exact h.scale a'),?_⟩ -- tune reorder
 let b:=linΦR σ τ i; have ht(F:P.Slabs i):b F=centerP_R P i σ τ F:=rfl
 have hΩ:b H=0:=by rw[ht]; unfold centerP_R; rw[show incomeVertR i H=1 from Virtue1J σ τ i P.publicH]; simp only[one_smul]; exact sub_self _
 let j:=g.trans (SportR.hop P m f); let Q:=ΦCentered p B0 M x R u pu A T D V j
 change ‖b (a' • U)- Q (a' • w) i σ τ‖≤ _; rw [Q.map_smul]; change ‖b (a' • U) - a' • (K-Heapψ P M' • H)‖≤ _; rw [show Heapψ P M'=incomeVertR i K from (ΦSkyJ p B0 M x R u pu A T D V (g.trans Q') σ τ i w _ (MeanBylawsJ _)).symm]
 change ‖b (a' • U) - a' • b K‖ ≤ _; let X:=U-(K+A' • H)
 have hp:=p.price f g u s
 rw [map_smul,←smul_sub,show b U-b K=b X from (by unfold X; rw [map_sub,b.map_add,map_smul,hΩ,smul_zero,add_zero]),norm_smul,show ‖a'‖=TallyInR D m f d Vt from wrapR_fee p D g Vt]
 have he:0 ≤ TallyInR D m f d Vt:= (show _ from (norm_nonneg a')).trans_eq (wrapR_fee p D g Vt)
 have h:FlavorRateJ P u f s s (2*LoomK v) ≤ FlavorRateJ P u f s s (2*Y):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e (by norm_num)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp.small _)) (hp.hot le_rfl Q').le) (pow_nonneg (zero_le_one.trans hp.bound) _))
 exact (mul_le_mul_of_nonneg_left ((budget_R σ τ i X).trans (mul_le_mul_of_nonneg_left (vU.trans (mul_le_mul_of_nonneg_left h (WalletB p).le)) (by norm_num))) he).trans_eq (by ring)
#print axioms LightΘR
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
