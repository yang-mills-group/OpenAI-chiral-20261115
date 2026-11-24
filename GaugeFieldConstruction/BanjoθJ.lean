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
local notation "κ"=> CapLJ P ℓ
local notation "ζτ"=>XûJ P ℓ f
local notation "L₀"=>P.R.L.val
variable {X:Type}(T:∀s:ℕ,X→ Seat (Papal.count Y s i))
local notation "ν"=> Y.uv k
variable (F:FilmθJ Y i X T f (Y.uv k))(V: ScarJ Y i X T f)
local notation "₴"=> separation
local notation "Υ" s:max=> DuoJ P ℓ f s
local notation "τH"=>ZoomJ Y i s
-- grow & separate
local notation "ψ"=> TwineθJ Y i X T f
include F V
lemma ToniJ (a:f ≤ s)(b:s ≤ Y.uv k): Injective (T s):=by intro i' j q; by_contra hz; have he:= stride_J Y i k s f T F V a b i' j hz; rw[q,separation_self] at he; omega
#check Montana
#check distanceLaw
lemma SturdyJ [LinearOrder X]: Montana Y i k (TwineθJ Y i X T f) f:=by
 constructor
 · intro s a b u x p; obtain ⟨i',v,e⟩:= halo_spec.mp p; obtain ⟨r,z,rfl⟩:=mem_image.mp v; obtain ⟨y,h,h₁⟩:= halo_spec.mp z; obtain rfl:y=T s u:=mem_singleton.mp h
   let K:=ZoomJ Y i s; have hx:=Corona.near K (T (s+1) u); have hv:separation (T (s+1) u) (K.embed (T s u))≤ L₀:=by rw [← (show K.parent _=T s u from F s a b u)]; change 2*_≤L₀ at hx; omega
   have hh:L₀*(Υ s-κ) ≤ L₀*Υ s-L₀*κ:= (Nat.mul_sub ..).le
   let C:=Journey.reserve P ℓ; let g:=gross (aliasLaw P) (distanceLaw ℓ) P.R.J -- name tune
   have he:separation (T (s+1) u) x ≤ L₀+(L₀*Υ s-L₀*κ+L₀*g):=(separation_triangle _ _ _).trans (Nat.add_le_add hv ((separation_triangle _ (K.embed r) _).trans (Nat.add_le_add ((Next.Free.scaled_root K _ _).trans ((Nat.mul_le_mul_left L₀ h₁).trans hh)) e))) -- Tune
   have hu: C+1+L₀*g≤ L₀*C:=Tower.width_margin P ℓ
   have hy: L₀*κ=L₀*C+4*L₀:=by unfold CapLJ C; ring
   have hw: L₀*κ≤ L₀*Υ s:=Nat.mul_le_mul_left L₀ (by linarith only [DuoM s f P ℓ, Nat.zero_le ((EtaΘ P f)^3)])
   have ht:3 ≤ L₀:= P.R.coarse; apply halo_spec.mpr; refine ⟨T (s+1) u,mem_singleton_self _,le_trans he ?_⟩; change _≤ DuoJ P ℓ f (s+1)- CapLJ P ℓ; rw [WorthTwine s f a]; rw [show κ=C+4 from rfl] at hy hw ⊢; omega
 intro s a b u v p ξ h y t; obtain ⟨j,hj,j'⟩:=halo_spec.mp h; obtain ⟨l,hl,l'⟩:=halo_spec.mp t; obtain rfl:j=T s u:=mem_singleton.mp hj; obtain rfl:l=T s v:=mem_singleton.mp hl; rw [separation_comm] at l'; have he:=stride_J Y i k s f T F V a b u v p; have ht:=separation_triangle (T s u) ξ (T s v); have hx:=separation_triangle ξ y (T s v)
 have hb:= DuoM s f P ℓ; unfold CapLJ at *; omega
section
omit F V
abbrev TallθJ (P:Preparation)(f:ℕ):Prop:=forall s:ℕ,f ≤ s → (EtaΘ P s)^3 ≤ P.R.L.val^(s-f)* (EtaΘ P f)^3
variable (hL:8 ≤P.R.L.val)
include hL
lemma TallMaturityJ :∀ᶠ f in atTop,TallθJ P f:=by
 let Q:= P.R.L
 filter_upwards [eventually_forall_ge_atTop.mpr ((stage_slope P.V P.x).eventually (Rebuild.geometry (billX Q)))] with f t s a
 induction a with
 | refl=> simp [pow_zero]; -- tune
 | @step s b ih=>
   change (EtaΘ P (s+1))^3 ≤ P.R.L.val^(s+1-f)*_
   have w:EtaΘ P (s+1) ≤ 2*EtaΘ P s:=by 
      unfold EtaΘ; have h:hat P.R.L P.x (s+1)=hat P.R.L P.x s+billX Q:=by unfold hat Q; push_cast; ring
      rw[h]; exact (t s b).1.1 -- indent
   rw [show s+1-f=s-f+1 from by have hv:f ≤ s:=b; omega,pow_succ' _ (s-f),Nat.mul_assoc]; refine (le_trans (Nat.pow_le_pow_left w 3) ?_); rw [mul_pow]; exact Nat.mul_le_mul (by simpa using hL) ih
end
variable {I:Type}[Fintype I][LinearOrder I](u:I→X)(M:ℕ)(p: ∀ x:X,(univ.filter fun i=> u i=x).card ≤ M)
open Riant
include p
lemma Bound_TopθJ (a:f ≤ Y.uv k) : BoundedMark I (T (Y.uv k) ∘ u) M:=by
 let σ:=T ν ∘ u
 intro x; by_cases g:x∈ Set.range (T ν)
 · obtain ⟨y,rfl⟩:=g; exact (card_le_card (show (univ.filter fun i=>σ i=T ν y)⊆ univ.filter (fun i=>u i=y) from fun i z=> (mem_filter.mpr ⟨mem_univ _, ToniJ Y _ k _ f T F V a le_rfl (mem_filter.mp z).2⟩))).trans (p _)
 · rw [filter_eq_empty_iff.mpr ?_,card_empty]; exact Nat.zero_le _; exact fun i _ h=>g ⟨u i,h⟩ -- _ tune shadow i.
lemma MambaθJ (a:f≤ s)(b:s ≤Y.uv k)(ht:TallθJ P f): Force_M ((Papal.gram Y s i k).p.B) (T s ∘ u) M:=by
 let v:=stride_J Y i k s f T F V a b
 have hx:(Papal.gram Y s i k).p.B=EtaΘ P s:= (by rw[(prices_plot Y s i k b).1]; exact (Y.meter.boot s).2.1)
 let B:= EtaΘ P s; have he:B^3≤ DuoJ P ℓ f s:= (ht s a).trans (Nat.mul_le_mul_left _ (by unfold XûJ; omega)); have hu:B≤B^3:=Nat.le_self_pow (by omega) _; change Force_M _ _ _; rw[hx]; let t:=T s∘ u
 have hh(x y:I)(p:u x≠u y): cape_B B+cape_B B+B+B < separation (t x) (t y):=by apply lt_of_lt_of_le _ (v _ _ p); unfold cape_B; omega
 refine ⟨fun i j p=>hh i j (fun o=> p (congrArg (T s) o)), fun y=>?_⟩
 let Q:= reach_B (cape_B B) B t y; by_cases g:Q.Nonempty
 · obtain ⟨z,h⟩:=g; refine (card_le_card (show Q⊆ _ from ?_)).trans (p (u z)); intro w v; refine mem_filter.mpr ⟨mem_univ _,?_⟩; by_contra q
   have E:= hh w z q; have hv:= (mem_filter.mp v).2; have ht:=(mem_filter.mp h).2
   -- Tune filter direction
   change separation _ _ ≤_ at hv ht
   have hg:=separation_triangle (t w) y (t z); rw [separation_comm] at hv; omega
 change Q.card≤M; rw [not_nonempty_iff_eq_empty.mp g,card_empty]; exact Nat.zero_le _
#print axioms SturdyJ
#print axioms TallMaturityJ
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
