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
-- scarcity on f seats.  L chosen moderately above 8.
abbrev ZoomJ (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i s:ℕ):=ratio (Vale.apt (Y.ir i) P.block P.R.L s)
private lemma zg {a b:Side}(S T:Ratio a b): S=T:=by cases S with | mk v h => cases T with | mk w q=> obtain rfl:v=w:= Subtype.ext (mul_left_cancel₀ a.property.ne' (h.symm.trans q)); rfl
lemma zigZ : ((PlaceOf Y i k s).step P.V).ratio=ZoomJ Y i s:=by -- tune
 exact zg ..
abbrev FilmθJ (X:Type)(G:∀s:ℕ,X→ Seat (Papal.count Y s i))(f r:ℕ):Prop:=∀ s:ℕ,f≤ s→ s<r →∀ u:X,(ZoomJ Y i s).parent (G (s+1) u)=G s u
abbrev EtaΘ (P:Preparation)(s:ℕ):=radiusB (hat P.R.L P.x s)
-- κ margin constant
abbrev CapLJ (P: Preparation)(ℓ:ℕ):= Journey.reserve P ℓ+4
abbrev XûJ (P:Preparation)(ℓ:ℕ)(f:ℕ):= CapLJ P ℓ+100+(EtaΘ P f)^3
-- for ratio lower bound use 9X+4
abbrev ScarJ (X:Type)(G:∀s:ℕ,X→ Seat (Papal.count Y s i))(f:ℕ):Prop:= forall a b:X,a≠b→ 20*XûJ P ℓ f ≤ separation (G f a) (G f b)
local notation "κ"=> CapLJ P ℓ
local notation "ζτ"=>XûJ P ℓ f
local notation "L₀"=>P.R.L.val
abbrev DuoJ (P:Preparation)(ℓ:ℕ)(f s:ℕ):=P.R.L.val^(s-f)*XûJ P ℓ f
abbrev TwineθJ (X:Type)(G:∀s:ℕ,X→ Seat (Papal.count Y s i))(f:ℕ):HousingJ Y i X:=fun s i=> Lattice.halo ((DuoJ P ℓ f s) - CapLJ P ℓ) {G s i}
lemma WorthTwine (a:f ≤ s) :∀ (P:Preparation), ∀ ℓ:ℕ, DuoJ P ℓ f (s+1)=P.R.L.val*(DuoJ P ℓ f s):=by intro P ℓ; unfold DuoJ; rw [show s+1-f=s-f+1 from by omega,pow_succ]; ring
variable {X:Type}(T:∀s:ℕ,X→ Seat (Papal.count Y s i))
include Y
private lemma near (u:Seat (Tq (s+1)))(x:Seat (Tq s))(v:(ZoomJ Y i s).parent u=x): separation ((ZoomJ Y i s).embed x) u ≤ L₀:=by
 rw [←v,separation_comm]; have h:=Corona.near (ZoomJ Y i s) u; have hx:(ZoomJ Y i s).count=P.R.L:=rfl; rw[hx] at h; omega
local notation "ν"=> Y.uv k
variable (F:FilmθJ Y i X T f (Y.uv k))(V: ScarJ Y i X T f)
include F
local notation "Τζ"=> separation
local notation "Υ" s:max=> DuoJ P ℓ f s
omit F Y in
lemma DuoM (P:Preparation)(ℓ:ℕ): 100+CapLJ P ℓ+(EtaΘ P f)^3 ≤ DuoJ P ℓ f s:=le_trans (le_of_eq (by unfold XûJ; ring : _=XûJ P ℓ f)) (le_mul_of_one_le_left (Nat.zero_le _) (one_le_pow₀ (show 1≤P.R.L.val from P.R.L.property)))
local notation "τH"=>ZoomJ Y i s
-- grow & separate
local notation "ψ"=> TwineθJ Y i X T f
include V
lemma stride_J (u:f ≤ s) (b:s ≤ Y.uv k) :∀ x y:X,x≠y→ 8* DuoJ P ℓ f s+4 ≤ separation (T s x) (T s y):=by
 intro x y p; induction u with
 | refl=> have h:= V x y p; unfold DuoJ XûJ at *; rw [Nat.sub_self,pow_zero,one_mul]; omega -- v at f.
 | @step s u ih=>
   have h:=ih (by omega); let K:=ZoomJ Y i s; have he: L₀ * separation (T s x) (T s y) ≤ separation (K.embed (T s x)) (K.embed (T s y)):= Corona.below K _ _; let U:=s+1
   have v:separation (K.embed (T s x)) (K.embed (T s y)) ≤ L₀+(separation (T U x) (T U y)+L₀):= (separation_triangle _ _ _).trans (Nat.add_le_add (near Y i s _ _ (F s u b x)) ((separation_triangle ..).trans (Nat.add_le_add_left ((separation_comm ..).trans_le (near Y i s _ _ (F s u b y))) _))) -- h name tune
   have hx:2*L₀ ≥ 4:=by linarith [P.R.coarse]
   have hp:= (Nat.mul_le_mul_left L₀ h).trans (he.trans v); rw [WorthTwine s f u P ℓ]; unfold U at hp; rw [Nat.mul_add,show L₀*(8* DuoJ P ℓ f s)=8*(L₀*DuoJ P ℓ f s) by ring] at hp; change 8*(L₀*DuoJ P ℓ f s)+4 ≤ Τζ (T (s+1) x) (T (s+1) y); omega
#print axioms zigZ
#check stride_J
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
