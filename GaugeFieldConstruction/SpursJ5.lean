import GaugeFieldConstruction.Trimbo4
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
open Mew Roots Roots.Connect Ing Ing.Iona CoeffArc Frugal
section
variable {m B:Side}{I J A C:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]
variable [Fintype A][Fintype C][DecidableEq A][DecidableEq C]
namespace CoeffArc.Directory
-- induce from finite coordinate declarations. Naming scopes.Color generation.Needs $Full$ on all Principals of source. don't require image.F.P coherence if T0 differs.
variable (D:Directory I A)(H:Directory J C)(e:I↪J)(g:A↪C)(T:Sweep (mid m B))
structure Embassy :Prop where
   kin (i:I): H.kind (e i)=D.kind i
   own (i:I): H.own (e i)=g (D.own i)
   dep (a:A): H.depth (g a)= D.depth a
variable (v:Embassy D H e g)
def nameLift {a:A}{b:Bool}(i:D.NameK a b): H.NameK (g a) b:= ⟨e i.val,(v.own _).trans (congrArg _ i.property.1),(v.kin _).trans i.property.2⟩
variable (s:A→Seat (mid m B))(t:C→Seat (mid m B))(F:D.TourF)(P:H.TourF)
abbrev Rib :Prop:=∀ a:A, ∀ i:D.Pname a, Mason T (F a i)=P (g a) (nameLift D H e g v i)
variable (w:D.ToPC)(b:D.TourG)(G:D.ToMG)(L:Side)
variable (U: Finset I)
abbrev Rn:= ∀ i:I,D.kind i=true → i∈U
abbrev Sigt {I:Type}[Fintype I](W:Finset I)(x:Mew.Key I):Prop:=∀ i:I,i∉ W→x i=0
abbrev Eye (i:I): Key I:= Pi.single i 1
lemma tribe_eye(i:I):D.Tribe (Eye i) (D.own i):=fun x v=> by unfold Eye; exact Pi.single_eq_of_ne (fun e:x=i=>v (e ▸ rfl)) _
lemma PassU {x:Key I}(p:Sigt U x)(q:Rn D U): Sigt U (D.TransferX L s b G w x):=by
 intro i h; have he:D.kind i=false:=Bool.eq_false_iff.mpr (fun v=>h (q _ v)); let A:D.Vname (D.own i):=⟨i,rfl,he⟩
 change D.TransferX L s b G w x A.val=_; rw[κGap_T]; rw [show x A.val= 0 from p i h,mul_zero]
local notation "Ω"=>Λpay (N:=m) (B:=B) T
abbrev Mantle (x:Key I): Key J:=happyQ e (Ω ∘ x)
include v
lemma Achamo {a:A}{x:Key I}(he:D.Tribe x a): H.Tribe (Mantle e T x) (g a):=by
 intro j h; by_cases hp:j∈Set.range e
 · obtain ⟨i,rfl⟩:=hp; have hk:D.own i≠a:=fun e'=>h ((v.own _).trans (congrArg _ e')); unfold Mantle; rw [etaμ,comp_apply,he _ hk,map_zero]
 exact outsideμ _ _ _ hp
lemma Viento (i:I):Mantle e T (Eye i)=Eye (e i):=by
 funext j; by_cases hp:j∈ Set.range e
 · obtain ⟨b,rfl⟩:=hp; by_cases f:b=i; · subst b; unfold Mantle Eye; rw[etaμ,comp_apply, Pi.single_eq_same, Pi.single_eq_same,map_one]
   unfold Mantle Eye; rw [etaμ,comp_apply,Pi.single_eq_of_ne f,Pi.single_eq_of_ne (e.injective.ne f),map_zero]
 unfold Mantle Eye; rw[outsideμ _ _ _ hp,Pi.single_eq_of_ne (fun r=>hp ⟨_,r.symm⟩)]
lemma Katabasis {a:A}(i:H.Vname (g a))(x:Key I): Mantle e T (TransferX D L s b G w x) i.val= (GapGain L (D.depth a):ℂ)*Mantle e T x i.val :=by
 by_cases h:i.val∈Set.range e
 · obtain ⟨j,h⟩:=h
   have he:D.own j=a:= g.injective (((v.own _).symm.trans (congrArg _ h)).trans i.property.1); let k:D.Vname a:=⟨j,he,((v.kin _).symm.trans (congrArg _ h)).trans i.property.2⟩
   rw[←h]; unfold Mantle; rw[etaμ,etaμ]; simp only [comp_apply]
   rw [show TransferX D L s b G w x j=(GapGain L (D.depth a):ℂ)* x j from κGap_T _ _ _ _ _ _ _ _ k,map_mul,inkPay T (GapGain L (D.depth a)),inkR]
 unfold Mantle; rw [outsideμ _ _ _ h,outsideμ _ _ _ h,mul_zero]
lemma Toner (a:A)(x:Key I)(q:Rib D H e g T v F P) : Mason T (Woof (κPart D a true x) (F a))=Woof (κPart H (g a) true (Mantle e T x)) (P (g a)):=by
 let L:D.Pname a↪ H.Pname (g a):= ⟨nameLift D H e g v,fun i j h=> Subtype.ext (e.injective (congrArg Subtype.val h))⟩
 unfold Woof; rw [← sum_subset (s₁:=map L univ) (subset_univ _) ?_, Finset.sum_map]
 · let m:Waves→+ Waves:= {toFun:=Mason T,map_zero':=?_, map_add':=fun x y=> sheen_plus .. }
   swap
   · -- tune
     have h:Mason T 0= (0:ℂ) • Mason T 0:=by
       rw [← show (Ω (0:ℂ))=0 from map_zero _, inkPay,←payY_a]
       congr; exact (Troot_z Packs_U _).symm
     exact h.trans ((show ∀ {A:Type}(P:TPack A),letI:=P.G; letI:=P.S;∀ a:A,(0:ℂ) • a=0 from fun {_} R=>by letI:=R.G;letI:=R.S; exact fun x=>zero_smul ..) Packs_U _)
   change m _= _; rw [map_sum]; apply sum_congr rfl; intro i _
   change Mason T _= _
   rw [payY_a, q a]; unfold κPart Mantle; rw[show (L i).val=e i.val from rfl,etaμ, comp_apply,inkPay]
   rfl
 intro i _ h; have hx: i.val∉Set.range e:=by
    rintro ⟨j,h'⟩; have he:D.own j=a:= g.injective (((v.own _).symm.trans (congrArg _ h')).trans i.property.1); let k:D.Pname a:=⟨j,he,((v.kin _).symm.trans (congrArg _ h')).trans i.property.2⟩
    exact h (mem_map.mpr ⟨k,mem_univ _,Subtype.ext h'⟩)
 unfold κPart Mantle; rw [outsideμ _ _ _ hx]; exact (show ∀ {A:Type}(P:TPack A),letI:=P.G; letI:=P.S;∀ a:A,(0:ℂ) • a=0 from fun {_} R=>by letI:=R.G;letI:=R.S; exact fun x=>zero_smul ..) Packs_U _ -- tune Tpack
omit v
variable {N:Type}[LinearOrder N][Fintype N]
lemma Arriba (u:N→Key I)(z:Key N): Mantle e T (SpotQ u z)=SpotQ (Mantle e T∘u) (Ω ∘ z):=by
 funext i; by_cases h:i∈Set.range e
 · obtain ⟨j,rfl⟩:=h; unfold SpotQ Mantle; rw[etaμ,comp_apply,Finset.sum_apply, Finset.sum_apply, map_sum]; refine sum_congr rfl fun i _=>?_; change Ω (_*u i j)=Ω (z i)*happyQ _ _ (e j); rw [map_mul, etaμ]; rfl -- tune placeholders
 change happyQ _ _ _= _; rw[outsideμ e _ _ h]; symm; unfold SpotQ; rw[Finset.sum_apply]; apply sum_eq_zero; intro x _; change _ * Mantle e T _ _= _; rw [Mantle,outsideμ _ _ _ h,mul_zero]
lemma Augurio(u:N→Key I)(z:N→ℝ): Mantle e T (LegQ u z)=LegQ (Mantle e T∘u) z:=by unfold LegQ; rw[Arriba]; congr 1; exact funext fun i=> (inkPay ..).trans (inkR ..) -- tune
lemma parade {x:Key I}(q:Sigt U x):SpotQ (fun i:U=> Eye (I:=I) i.val) (fun j:U=>x j.val)=x:=by
 funext i; unfold SpotQ; rw[Finset.sum_apply]; by_cases h:i∈U
 · rw [Finset.sum_eq_single (⟨i,h⟩:U)]; · change x i*(Eye (I:=I) i) i=_; simp [Eye]
   · intro j p f; change _ *(Eye (I:=I) j.val) i=0; rw [Eye,Pi.single_eq_of_ne (fun g=>f (Subtype.ext g.symm)),mul_zero]
   simp
 rw [q _ h]; refine sum_eq_zero fun j _=>?_ ; change _ *(Eye (I:=I) j.val) i= _; rw [Eye,Pi.single_eq_of_ne (fun e:i=j.val=>h (e ▸ j.property)),mul_zero]
#print axioms Katabasis
end CoeffArc.Directory
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
