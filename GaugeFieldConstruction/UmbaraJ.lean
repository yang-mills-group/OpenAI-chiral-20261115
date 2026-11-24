import GaugeFieldConstruction.TejasJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.PirangaJ
import GaugeFieldConstruction.PeakJ
import GaugeFieldConstruction.GypA
import GaugeFieldConstruction.StepWorthJ
import GaugeFieldConstruction.OrbisJ
import GaugeFieldConstruction.YieldRampJ
import GaugeFieldConstruction.Budgets
import GaugeFieldConstruction.FairNumJ
import GaugeFieldConstruction.CapriceJ
import GaugeFieldConstruction.NurmaJ
import GaugeFieldConstruction.SamarsJ
import GaugeFieldConstruction.Norwood
import GaugeFieldConstruction.TurnBridgeJ
import GaugeFieldConstruction.FineAlJ
import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k s f j:ℕ) {m n:ℕ}
open Papal AUbard Directory
local notation "η_"=>Y.uv k
local notation "Pq"=>P.R.L
variable (D C t:ℕ→ℝ) (α c τ u0:ℝ)(Nkey:ℕ) -- price scale functions C unused.
open XGarden XGarden.Ledger XGarden.Echo XGarden.MastTin XGarden.Shield XGarden.MastTin.MintB Ing Ing.Iona Ing.Ivey Ing.Ivey.ShoreQ
open Sour Sour.SliceRoof SeasonH Fock.Wosk TableF TableF.Lenten TableF.Lenten.Layout
open Oath Wray
local notation "µs" s:max=> Papal.gram Y s i k
variable (K :ℕ→ℝ)
local notation "NY_" s:max=> Papal.count Y s i
local notation "Zmat" s:max=> KeyUp ((Papal.gram Y s i k).p)
local notation "Γω" s:max=> (PlaceOf Y i k s).step P.V
local notation "Φ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "δp"=> P.R.L
local notation "ρp" => reserve P ℓ
local notation "Tq" s:max=> Papal.count Y s i
open Shield
lemma trim_feeJ (p:3*f ≤ s): lebs P.R.L s ≤ DuoJ P ℓ f s-CapLJ P ℓ:=by
 let x:= P.R.L.val; let y:=(x:ℝ); have hx:1 ≤ y:=by unfold y; exact_mod_cast (show 1≤ x from P.R.L.property)
 have hv:sectPay P.R.L s ≤ y^(s-f) :=by
    unfold sectPay; rw [←Real.rpow_natCast y]; apply Real.rpow_le_rpow_of_exponent_le hx; rw [Nat.cast_sub (by omega : f ≤ s)]; have hz :3*(f:ℝ) ≤ s:=by exact_mod_cast p
    linarith -- tune indentation
 have ht:lebs P.R.L s ≤x^(s-f):=by
    suffices u: (lebs P.R.L s:ℝ) ≤ ((x^(s-f):ℕ):ℝ) by exact_mod_cast u
    push_cast; exact (Nat.floor_le (show 0 ≤ sectPay P.R.L s by unfold sectPay; positivity)).trans hv -- tune
 have hb:1≤ x^(s-f):=one_le_pow₀ (show 1≤ x from P.R.L.property)
 apply ht.trans; unfold DuoJ XûJ
 have hA: CapLJ P ℓ≤ x^(s-f)*CapLJ P ℓ:=le_mul_of_one_le_left (Nat.zero_le _) hb
 change x^_ ≤ x^_*(_+ _)-_
 rw[Nat.mul_add,Nat.mul_add]; omega
-- ancestry indexed COVER trails
local notation "κL"=> P.R.L
open Ratio
def pixJ (L:Side)(x:Cover): Cover:= Lattice.lift (wrap L x)
def parentJ (L:Side)(x:Cover):Cover:= fun i=> ((x-pixJ L x) i) / (L.val:ℤ)
lemma splitP (L:Side)(x:Cover):L.val • parentJ L x + pixJ L x = x:=by
 have h: wrap L (x-pixJ L x)=0:=by unfold pixJ; rw [map_sub,wrap_lift,sub_self]
 funext i
 have hg: (((x-pixJ L x) i:ℤ):ZMod L.val)=0:=congrFun h i
 have hb:= (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hg -- check
 change L.val • (parentJ L x) i + (pixJ L x) i= _; rw[nsmul_eq_mul]; unfold parentJ; rw [mul_comm,Int.ediv_mul_cancel hb]; change x i-pixJ L x i+_= _; ring
lemma pinchP (L:Side)(x:Cover)(i:Axis) (h:Odd L.val):2*|pixJ L x i| ≤ (L.val:ℤ):=by have he:= Ratio.unambiguous h (wrap L x) i; have hp:= lift_centers (wrap L x) i; unfold pixJ; rcases abs_cases (Lattice.lift (wrap L x) i) with h|h <;> rw [h.1] <;> omega -- fill
lemma belowP (c n:Side)(L: Ratio c n)(x:Cover) : L.parent (wrap n x)=wrap c (parentJ L.count x):=by
 have he:L.assemble (wrap c (parentJ L.count x), wrap L.count x)=wrap n x:= by unfold Ratio.assemble; rw[L.embed_wrap,← map_add, ← show pixJ L.count x=Lattice.lift (wrap L.count x) from rfl,splitP]
 rw[←he,L.assemble_parent] -- tune indentation
-- abstract law for cover films, Cost
abbrev PedalJ (L:Side)(T:ℕ → Lattice.Cover) (f r:ℕ):Prop:=∀ s:ℕ,f≤ s→s<r →parentJ L (T (s+1))=T s
lemma CanonJ{X:Type}(T:X→ ℕ → Lattice.Cover)(r:ℕ) (p:∀ x,PedalJ P.R.L (T x) f r): FilmθJ Y i X (fun s j=>wrap (More (side Y i s)) (T j s)) f r:=by
 intro s a b x; rw[belowP]; exact congrArg _ (p x s a b)
#print axioms trim_feeJ
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
