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
abbrev Herm (n:Type)[Fintype n] [DecidableEq n] : Submodule ℝ (Op n):={ carrier:={x|star x=x}, add_mem' {x y} a b:=star_add x y|>.trans (congrArg₂ _ a b), smul_mem' r x h:= (by change star (r • x)=_; rw [star_smul,star_trivial,h]),zero_mem':= star_zero _ }
local notation "M₀"=> Op (Fin 3)
local notation "HE" => Herm (Fin 3)
noncomputable def assembleH : (↥HE × ↥HE) ≃ₗ[ℝ] ↥chiralModule where
 toFun x:= keepsake _ _ x.1.property x.2.property -- `.. middle`
 invFun x:= (⟨Mezzo.passage (↑x) ac ac,(paid_shape x).1⟩,⟨Mezzo.passage (↑x) ab ab,(paid_shape x).2.1⟩)
 left_inv x:= by apply Prod.ext; exact Subtype.ext (coeffJoint x.1.val x.2.val).1; exact Subtype.ext (coeffJoint x.1.val x.2.val).2
 right_inv x:= Subtype.ext (paid_shape x).2.2.symm
 map_add' x y:= Subtype.ext (coeffPlus ..)
 map_smul' r x:= by
    apply Subtype.ext; change sonnet (r • x.1.val) (r • x.2.val)= r • Mezzo.sonnet x.1.val x.2.val; simp_rw [← Complex.coe_smul]; exact coeffScale _ _ (r:ℂ)
-- dim Herm via $A=X+i Y$, no metrics relation. linear_equiv on Op.
variable (n:Type)[Fintype n][DecidableEq n]
local notation "X" => Herm n
local notation "𝐌"=> Op n
local notation "ℐ"=> Complex.I
private def hermInk : (↥X × ↥X) →ₗ[ℝ] 𝐌 where
 toFun p:= p.1.val + ℐ • p.2.val
 map_add' a b:=by change a.1.val+b.1.val+ℐ • (a.2.val+b.2.val)=_; rw [smul_add]; abel
 map_smul' r v:=by change r • _+ℐ • (r • v.2.val)= r • (v.1.val+_); rw [smul_add,smul_comm]
lemma star_quiet {x:↥X}:star (x.val) = x.val:= x.property
private lemma own_par (a:𝐌): ∃ h:X,h.val=(1/2:ℝ) • (a+star a):= by refine ⟨⟨_,(show star ((1/2:ℝ) • (a+star a))=_ from ?_)⟩,rfl⟩; rw [star_smul,star_add, star_trivial, star_star, add_comm]
lemma inkFinite: Bijective (hermInk n):=by
 constructor
 · refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun ⟨x,y⟩ p=>?_); change x.val+ℐ • y.val=0 at p; have h:= congrArg star p; rw [star_add,star_zero,star_smul,star_quiet,star_quiet,Complex.star_def,Complex.conj_I,neg_smul] at h; have e:ℐ • y.val=0:= by
       have hp:x.val=- (ℐ • y.val):=eq_neg_of_add_eq_zero_left p
       rw [hp] at h
       refine ((smul_eq_zero.mp (?_:(2:ℝ) • (ℐ • y.val)=0))).resolve_left (two_ne_zero (α:=ℝ)) -- adjust
       rw [two_smul ℝ]; rw [← neg_add_rev, neg_eq_zero] at h; exact h
   refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_); · change x.val=0; rw [e,add_zero] at p; exact p
   exact (smul_eq_zero.mp e).resolve_left Complex.I_ne_zero
 intro x; obtain ⟨a,b⟩:= own_par n x; obtain ⟨c,d⟩:= own_par n (-ℐ • x); refine ⟨(a,c),?_⟩; change a.val+ℐ • c.val=x; rw [b,d,star_smul,star_neg,Complex.star_def, Complex.conj_I,neg_neg, smul_comm,smul_add ℐ,smul_smul,smul_smul,Complex.I_mul_I,mul_neg, Complex.I_mul_I,neg_neg]; module -- error calc.Se
lemma herbs: Module.finrank ℝ HE= 9:= by
 let h:= (LinearEquiv.ofBijective _ (inkFinite (Fin 3))).finrank_eq; -- infer M dim via $ℂ×9$
 have hp:Module.finrank ℂ (Op (Fin 3))=9:=by change Module.finrank ℂ (Matrix _ _ ℂ)=9; rw [Module.finrank_matrix]; simp
 have hv:= Module.finrank_mul_finrank ℝ ℂ (Op (Fin 3)); rw [Complex.finrank_real_complex,hp] at hv; rw [Module.finrank_prod] at h; omega
lemma spanMeter : Fintype.card Wage3=18:=by simp_rw [Wage3, Fintype.card_fin, ← assembleH.finrank_eq,Module.finrank_prod, herbs]
#print axioms spanMeter
end Orchid
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
