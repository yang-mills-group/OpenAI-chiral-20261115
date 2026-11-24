import YM.SU5.SatinWard.Resolution.Veering
import Velour.Crepe.GapSet
import YM.SU5.Reconstruction.Oblique.TiltAxis
import YM.SU5.Reconstruction.Oblique.Consulting
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A:ℝ)
open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
open Hove Yoke Buffered Afterglow Journey ShapeLab.ResolutionFrame
namespace Tabletop

open ResolutionFrame Vow.TreasuryFog Swell
open ResolutionFrame Rue Advance Tapestry
variable {I:Type}[Fintype I][LinearOrder I]{v z:ℕ}
attribute [-instance] instDecidableEqLex
local notation "WK"=> Booth I η
local notation "Θ"=> P.Ctor (Y.ir i) (s+1)
local notation "εμ"=> Primary ι η
local notation "Φ"=> F.colors (P.Ctor (Y.ir i) s)
local notation "Xp"=> RootBook Y i k s
local notation "Xf"=> RootBook Y i k (s+1)
local notation "G★"=> Vale.apt (Y.ir i) P.block P.R.L s
-- lean abbrev turnover step receipts. ensure proof printed. preserve all Step assumptions to reuse for grafts later.
variable [DecidableEq η](D:ArmorK)
set_option maxHeartbeats 240000
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Pressure.Worth Worth.Pays Graph
-- all annual payments. `Invoices` even in integrating on that partition, with q^{-1} radius when earned. Normed.Check.
open Again Tapestry Tower.SlabMark Tower.Tilted VelourBoard
open StressFlux AnalyticBridge.VerifiedReset Ione.Clock
-- general `Banner` reads: (i independent charge= p revenue) ANY skate. support&regularity qualified when constructed later. these are exact Marks even off boot widths.
namespace Shrine
variable {N:Side}(p:BudgetPoint)(D:Skate)
variable (i₀:Site (More N)) (V:Pane N)(j:Axis)(L:ℤ)(x y:ℝ)
abbrev bookValue {N:Side}(P:BudgetPoint)(A:Skate)(t:Site (More N))(V:Pane N):ℂ:=({v| pingS P.threshold (Lattice.halo 10 {t}) v}).indicator (kerP t P A) V
noncomputable def temple {N:Side}(P:BudgetPoint)(x:Site (More N)): Skate →ₗ[ℝ] Mark N where
 toFun A := fun v=> bookValue P A x v.1 • 1
 map_smul' r V:=by
    funext i'; unfold bookValue; by_cases h:pingS P.threshold (Lattice.halo 10 {x}) i'.1; · simp only [Set.indicator_apply, Set.mem_setOf_eq,h,Pi.smul_apply,if_true,RingHom.id_apply]; erw [point_scale]; change _= r • (kerP x P V i'.1 • (1:Fock.FC (Single N))); rw [smul_assoc]
    simp only [Set.indicator_apply, Set.mem_setOf_eq,h,if_false,RingHom.id_apply,zero_smul,Pi.smul_apply,smul_zero] -- fix indentation
 map_add' A B:=by
    have hb(t:Pane N): kerP x P (A+B) t= kerP x P A t+ kerP x P B t:=by simp only [ker_suit,kCar,Pi.add_apply,smul_add,sum_add_distrib]
    funext i; by_cases h:pingS P.threshold (Lattice.halo 10 {x}) i.1 <;> simp only [bookValue,Set.indicator_apply,Set.mem_setOf_eq,h, ↓reduceIte,hb,Pi.add_apply,zero_smul,add_zero,add_smul]

lemma point_book (E:Side)(i:Site (mid N E)): temple p (node i) D= pointK i D 10 p:=rfl
-- orientation move. need commute notF.X. odd det only. Ker-space arbitrary.
lemma purse (s:Signed)(b:Site (More N)) : Pec.pays s (bookValue p D i₀ (pull s b V))= bookValue p (localFace s D) (affine s b i₀) V:=by
 let M:=More N; let h:=ping_commutes (halo 10 {i₀}) p.threshold s b V; rw [YM.Regis.Head.Etch.halo_plan] at h; let X:= affine s b i₀
 unfold bookValue; by_cases q:pingS p.threshold (halo 10 {affine s b i₀}) V; swap; · have w:=mt h.mp q; simp only [Set.indicator_apply, Set.mem_setOf_eq,q,w, ↓reduceIte,map_zero] -- X def
 simp only [Set.indicator_apply,Set.mem_setOf_eq,q,h.mpr q,if_true]
 rw [ker_suit,ker_suit]; unfold kCar; rw [map_smul,map_sum (Pec.pays s)]; congr 1
 let E:=PlaqAxes.transform s; symm; rw [←Equiv.sum_comp E]; refine sum_congr rfl fun k _=>?_ ; rw [map_sum (Pec.pays s),←Equiv.sum_comp E]; refine sum_congr rfl fun j _=>?_
 rw [petals_moves, frame_levy,frame_levy,real_inner_smul_left,real_inner_smul_right,map_smul]; rw [show localFace _ _ (E k) (E j)= _ from face_p s D k j,smul_smul]; apply congrArg₂ _ _ rfl; unfold E; ring
lemma temple_mirror : reflMark j L (temple p i₀ D) = temple p ((plane j L).anon _ i₀) (localFace (Signed.mirror j) D):=by
 let s:=Signed.mirror j; let S:=plane j L; funext V; change Fock.theta _ (bookValue p D i₀ (fling j L N V.1) • 1)= bookValue p _ _ _ • _
 rw [theta_smul,theta_one,fling_eq]; apply congrArg (fun z:ℂ=> z • (1:Fock.FC (Single N))); exact Eq.trans (b:=Pec.pays s _) (by unfold Pec.pays s; rw [if_pos (det_t j)]; rfl) (purse ..)
lemma temple_tilt (s:Ramp) : s.bill (temple p i₀ D)=temple p (s.plan.anon _ i₀) (localFace s.s D):=by
 funext V; change Fock.theta _ (bookValue p D i₀ (s.turnLink N V.1) • 1) = bookValue p _ _ _ • _
 rw [theta_smul,theta_one,s.turn_pull]; apply congrArg (fun z:ℂ=> z • (1:Fock.FC (Single N))); have h:=s.proper_pin
 rw [show s.plan.anon N i₀= affine s.s 0 i₀ from ?_]; swap; · change affine s.s (wrap (More N) (2 • (0:Cover))) i₀= _; rw [smul_zero,map_zero]
 exact Eq.trans (b:=Pec.pays s.s _) (by unfold Pec.pays; rw [if_pos h]; rfl) (purse ..)

-- rotas. any j axis orientation gives same even though calling swaps not authorized for v-shape.
def ac0:Ramp:=⟨0,2,by decide⟩
def ac1:Ramp:=⟨1,2,by decide⟩
private lemma lowLow_0 : Ione.Clock.move ac0.s lowLow= rimC:=by decide
private lemma lowLow_u0 : Ione.Clock.levy ac0.s lowLow = 1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis)<1 then 1 else -1)=_; norm_num [Axis]; decide
private lemma rimA_0 : Ione.Clock.move ac0.s rimA= rimA:=by decide
private lemma rimA_u0 : Ione.Clock.levy ac0.s rimA = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if true=true then (-1:ℝ) else 1)*(if (2:Axis)<0 then 1 else -1)=_; norm_num [Axis]
private lemma rimB_0 : Ione.Clock.move ac0.s rimB= highHigh:=by decide
private lemma rimB_u0 : Ione.Clock.levy ac0.s rimB = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis)<3 then 1 else -1)=_; norm_num [Axis]; decide
private lemma rimC_0 : Ione.Clock.move ac0.s rimC= lowLow:=by decide
private lemma rimC_u0 : Ione.Clock.levy ac0.s rimC = 1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if true=true then (-1:ℝ) else 1)*(if (1:Axis)<0 then 1 else -1)=_; norm_num [Axis]
private lemma rimD_0 : Ione.Clock.move ac0.s rimD= rimD:=by decide
private lemma rimD_u0 : Ione.Clock.levy ac0.s rimD = 1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis)<3 then 1 else -1)=_; norm_num [Axis]; decide
private lemma highHigh_0 : Ione.Clock.move ac0.s highHigh= rimB:=by decide
private lemma highHigh_u0 : Ione.Clock.levy ac0.s highHigh = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis)<3 then 1 else -1)=_; norm_num [Axis]; decide
private lemma lowLow_1 : Ione.Clock.move ac1.s lowLow= rimA:=by decide
private lemma lowLow_u1 : Ione.Clock.levy ac1.s lowLow = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if true=true then (-1:ℝ) else 1)*(if (0:Axis)<2 then 1 else -1)=_; norm_num [Axis]; decide
private lemma rimA_1 : Ione.Clock.move ac1.s rimA= lowLow:=by decide
private lemma rimA_u1 : Ione.Clock.levy ac1.s rimA = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if true=true then (-1:ℝ) else 1)*(if (0:Axis)<1 then 1 else -1)=_; norm_num [Axis]
private lemma rimB_1 : Ione.Clock.move ac1.s rimB= rimB:=by decide
private lemma rimB_u1 : Ione.Clock.levy ac1.s rimB = 1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis)<3 then 1 else -1)=_; norm_num [Axis]; decide
private lemma rimC_1 : Ione.Clock.move ac1.s rimC= rimC:=by decide
private lemma rimC_u1 : Ione.Clock.levy ac1.s rimC = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if true=true then (-1:ℝ) else 1)*(if (2:Axis)<1 then 1 else -1)=_; norm_num [Axis]; decide
private lemma rimD_1 : Ione.Clock.move ac1.s rimD= highHigh:=by decide
private lemma rimD_u1 : Ione.Clock.levy ac1.s rimD = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis)<3 then 1 else -1)=_; norm_num [Axis]; decide
private lemma highHigh_1 : Ione.Clock.move ac1.s highHigh= rimD:=by decide
private lemma highHigh_u1 : Ione.Clock.levy ac1.s highHigh = -1 := by
 unfold Ione.Clock.levy StressFlux.sign; change (if true=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis)<3 then 1 else -1)=_; norm_num [Axis]; decide
lemma shrineRotations : localFace ac0.s Ω₁= coupleW rimB rimC Complex.I ∧ localFace ac1.s Ω₁= -(coupleW rimA rimD Complex.I) ∧ localFace ac0.s (Ω₁+Ω₂)=Ω₁+Ω₂ ∧ localFace ac1.s (Ω₁+Ω₂)=Ω₁+Ω₂:=by
 simp only [Ω₁, Ω₂, local_plus, locale_sub, couple_move,lowLow_0,lowLow_1,lowLow_u0,lowLow_u1,rimA_0,rimA_1,rimA_u0,rimA_u1,rimB_0,rimB_1,rimB_u0,rimB_u1,rimC_0,rimC_1,rimC_u0,rimC_u1,rimD_0,rimD_1,rimD_u0,rimD_u1,highHigh_0,highHigh_1,highHigh_u0,highHigh_u1]; simp [Pec.pays,couple_swap,couple_neg,ac0.proper_pin,ac1.proper_pin]; constructorm* _ ∧ _ <;> abel
lemma templeGlazed (j:Axis)(x y:ℝ): localFace (Signed.mirror j) (cloverKey x y)=cloverKey x y:=by rw [cloverKey,local_plus,locale_smul,locale_smul,FF_even.1 _ (mirror_l _),FF_even.2 _ (mirror_l _)]
lemma rotate_m (x y:ℝ): cloverKey x y + localFace ac0.s (cloverKey x y)+ localFace ac1.s (cloverKey x y)= (x+2*y) • cloverKey 1 1:=by
 obtain ⟨h,H,v,u⟩:=shrineRotations; rw [local_plus,h] at v; rw [local_plus,H] at u;
 unfold cloverKey; rw [local_plus,local_plus,locale_smul,locale_smul,locale_smul,locale_smul,h,H]; simp only [one_smul]; rw [show localFace ac0.s Ω₂=Ω₁+Ω₂-coupleW rimB rimC Complex.I from by rw [←v]; abel, show localFace ac1.s Ω₂=Ω₁+Ω₂+coupleW rimA rimD Complex.I from by rw [←u]; abel]; unfold Ω₂; simp only [smul_add,smul_neg,add_smul,two_mul,smul_sub]; abel
#print axioms temple_tilt
#print axioms rotate_m
end Shrine
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
