import YM.SU5.SatinWard.Resolution.Spirea
import YM.SU5.SatinWard.Resolution.Lampro
import YM.SU5.Reconstruction.Oblique.TiltAxis
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
variable (uZ:BladeQ P.R Z W V K)(proofW:∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s<Y.uv k → stockedTap Y Pay kc Γ Tξ nmc m Z V K W s i k)(flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A u:ℝ)


open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
set_option linter.flexible false
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Bα"=> RootBook Y i k s
local notation "pβ" => (Bα).p
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "V₀"=> (Y.voyage i).CapeT s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
local notation "ARE"=>stockRate (Bα).p
local notation "L★"=> P.R.L

open Hove
variable (p:GardenPlan Y s i k a b ψ f c (stencilReserve P.R.L)) (pB:0 ≤ b)(pH:0<c)(vΩ: CartRoom P.U ((Y.voyage i).CapeT s) (RootBook Y i k s) P.R.L.val Γ P.h)
variable (Hw:0<lapQ Y s)(w:s< Y.uv k)

open ShapeLab
open SweepSign
namespace Tabletop
open LitCurrent LitCurrent.Chamber
-- All > t prospects. Same electronic masks
variable {j:ℕ}{v:ℝ}(P₀:MaskPoint Y j s i k a b)(E:eraτ Y s i k j a v)
local notation "Cz"=>Θgain
local notation "Bv"=> (((RootBook Y i k s).p.B)/10)
-- normalized operands actual certified masks as literal formulas.
open StressFlux LitCurrent.Chamber Buffered.Afterglow.Tower Tilted Advance
-- arbitrary carriers field-density.Call.Rosters.T.A.
structure Poisson (N:Side)(S:Site N→ Mark N):Prop where
 rise (s:Sweep N)(p:s.charge=false)(x y:Site N)(h:Earlier s x y): flyMark s (S x)= S y
structure Dirfield (N:Side)(S:Axis→ Site N→ Mark N):Prop where
 rise (s:Sweep N)(p:s.charge=false)(x y:Site N)(h:Earlier s x y)(i:Axis): flyMark s (S (s.s.perm i) x)= (StressFlux.sign s.s i) • S i y
lemma Dirfield.plus{N:Side} {S T:Axis→Site N→Mark N}(s:Dirfield N S)(t:Dirfield N T): Dirfield N (S+T):=by refine ⟨fun i p x y h j=>?_⟩; simp only [Pi.add_apply]; rw [show flyMark i (S (i.s.perm j) x+T (i.s.perm j) x) = flyMark i (S (i.s.perm j) x)+flyMark i (T (i.s.perm j) x) from funext fun k=> map_add (Hive.teen i) (S (i.s.perm j) x _) (T (i.s.perm j) x _),s.rise i p x y h j,t.rise i p x y h j,smul_add] -- map_add returns teen terms not flyMark.Add
lemma Dirfield.minus{N:Side} {S:Axis→Site N→Mark N}(s:Dirfield N S)(a:ℝ):Dirfield N (a • S):=⟨fun i p x y h j=>by simp only [Pi.smul_apply,fly_scale]; rw [s.rise i p x y h j,smul_comm a]⟩
lemma Dirfield.heat{N:Side}: Dirfield N 0:=by refine ⟨fun i t x y h j=>?_⟩; simp only [Pi.zero_apply,smul_zero]; exact funext fun x=> map_zero (Hive.teen i)
lemma Dirfield.combo{N:Side}{M:ι→Axis→Site N→Mark N}(p:∀ i,Dirfield N (M i))(x:Coords ι): Dirfield N (fun i:Axis=> ShapeLab.columns (fun j=>M j i) x):=by
 have h(T:Finset ι): Dirfield N (∑ i∈T,x i • M i):=by
    induction T using Finset.induction_on with
    | empty=> rw [sum_empty]; exact Dirfield.heat
    | insert i T h ih=> rw [sum_insert h]; exact ((p i).minus _).plus ih
 have eq:(fun i:Axis=> ShapeLab.columns (fun j=>M j i) x)=(∑ i:ι,x i • M i):=funext fun i=>by rw [Finset.sum_apply,ShapeLab.cols_apply]; rfl
 exact eq.symm ▸ h Finset.univ
lemma legDir(i':Wage3):Dirfield Λ (fun x=> spinClass Y s i x i'):=by
 let X:= dynamicSpin (ShapeLab.leg i'); have hv:ChiralX 0 X:= (Θc.equivFun.symm (ShapeLab.leg i')).property; refine ⟨fun t p a b y j=>?_⟩; change flyMark t (_ • _) = _ • ((vigorΩ P s) • _); rw [show flyMark t (vigorΩ P s • _)= _ from fly_scale ..]; change _ • flyMark t (onsiteSensor a (petal (t.s.perm j) ⊗ₖ X))= _ • (vigorΩ P s • _); rw [(show flyMark t _= _ from (spin_shift t j X hv.herm a b y p)),smul_comm]
include P₀
lemma starTurns (D:Division): Poisson Λ (fun i=> starField Y E i D):=by
 refine ⟨fun s p x y h => ?_⟩; unfold starField lunarScale; rw [Complex.coe_smul,fly_scale,show flyMark s _= _ from frontSite (fun i=>jewelO D i E _ _ _ (1/2)) (fun s x X Y q=>posesY D x P₀.C E s X Y q) s x y h]; erw [show (pseudoCharacter _).sgn s= 1 by change hush s.charge _=_; rw [p]; rfl,one_smul]; rw [Complex.coe_smul] -- adjust
lemma qTurns (D:Division): Poisson Λ (fun i=> qField Y E i D):=by
 refine ⟨fun s p x y h => ?_⟩; unfold qField lunarScale; rw [Complex.coe_smul,fly_scale,show flyMark s _= _ from frontSite (fun i=>jewelY D i E _ _ _) (fun s x X Y q=>poses_gauge D x P₀.C E s X Y q) s x y h]; erw [show (pseudoCharacter _).sgn s= 1 by change hush s.charge _=_; rw [p]; rfl,one_smul]; rw [Complex.coe_smul]
lemma beatTurns (D:Division): Dirfield Λ (fun i x=> JField Y E x D (i,false)):=by
 refine ⟨fun z p x y h i' => ?_⟩; unfold JField lunarScale
 let u(j):= jewelJ D y E V₀ pβ Bv (1/2) j
 let b:= z.s; let j:=i'; let x0:=(z.s.perm i',false); let v:=jHull P.R.L (hat P.R.L P.x s)
 rw [Complex.coe_smul,fly_scale, LitCurrent.Chamber.fly_current _ _ _ _ _ _ P₀.C z _ y h,Complex.coe_smul v]; change v • _= _ • (v • (Complex.I • u (i',false))); rw [smul_comm (StressFlux.sign z.s i')]; apply congrArg
 rw [show (pseudoCharacter _).sgn z= 1 from ?_,one_smul,show (faceAt z x0)=(i',z.s.flip i') from ?_]; change Complex.I • u (i',z.s.flip i')=sign z.s i' • _; swap
 · unfold x0 faceAt; simp [Step.rotate,strideD]
 swap; · change hush z.charge _=_; rw [p]; rfl
 unfold sign; cases z.s.flip i'; · simp
 rw [show (i',true)=axisFlip (i',false) from rfl, show u (axisFlip _)= _ from (show u (axisFlip (i',false))= -u (i',false) from funext fun x=> currentSeed_anti _ _ _ _ _ _ _ P₀.C x _)]; simp
-- more ports.. 
omit P₀
lemma Poisson.turned{N:Side} {S:Site N→Mark N}(p:Poisson N S)(R:Ramp)(x:Site N)(h:AtSupport false univ (S x)): R.bill (S x)= S (R.plan.mills _ x):=by rw [rampFly R h]; exact p.rise _ rfl _ _ (turned_plumb R x)
lemma Dirfield.turned{N:Side} {S:Axis→Site N→Mark N}(p:Dirfield N S)(R:Ramp)(i:Axis)(x:Site N)(h:AtSupport false univ (S (R.s.perm i) x)): R.bill (S (R.s.perm i) x)= StressFlux.sign R.s i • S i (R.plan.mills _ x):=by rw [rampFly R h]; exact p.rise _ rfl _ _ (turned_plumb R x) i
lemma Poisson.tagged{N:Side} {S:Site N→Mark N}(p:Poisson N S)(i:Axis)(d:ℤ)(x:Site N)(h:AtSupport false univ (S x)): reflMark i d (S x)=S ((plane i d).mills _ x):=by rw [←flies_theta _ _ _ h]; exact p.rise _ rfl _ _ (turned_m i d x)
lemma Dirfield.tagged{N:Side} {S:Axis→Site N→Mark N}(p:Dirfield N S)(j i:Axis)(d:ℤ)(x:Site N)(h:AtSupport false univ (S j x)): reflMark i d (S j x)= StressFlux.sign (Signed.mirror i) j • S j ((plane i d).mills _ x):=by rw [←flies_theta _ i d h]; exact p.rise _ rfl _ _ (turned_m i d x) j
lemma Dirfield.ς(j i:Axis):StressFlux.sign (Signed.mirror i) j=if i=j then -1 else 1:=by unfold StressFlux.sign; simp [Signed.mirror,eq_comm]
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
