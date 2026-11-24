import GaugeFieldConstruction.TailsongJ
import GaugeFieldConstruction.PortionRentJ
import GaugeFieldConstruction.CunardJ
import GaugeFieldConstruction.SakhaJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
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
#check ProbeθJ
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
structure LampHouseJ where
  stairs : StaE (E:= Fin (θ u))
  sun (l:finsJ)(s:ℕ): ThreadJ (E:= Fin (θ u)) -- H,d; before f0 may arbitrary dummy. at s in comparisons
  rev (l:finsJ)(s:ℕ): ThreadJ (E:= Fin (θ u))
structure LampΤJ (G:LampHouseJ (θ:=θ) u) (T:Slow):Prop where
  step(s:ℕ)(pH:f0 ≤ s): ThreadShopJ (Fin (θ u)) T (Stencil1Q p B0 M x R u A s pH) (G.stairs.C s, G.stairs.a s)
  tilt(l:finsJ)(s:ℕ)(pH:f0 ≤ s): ThreadShopJ (Fin (θ u)) T (Stencil2Q p B0 M x R u l A s pH) (G.sun l s)
  fare(l:finsJ)(s:ℕ)(pH:f0 ≤ s): ThreadShopJ (Fin (θ u)) T (Stencil3Q p B0 M x R u l A s pH) (G.rev l s)
#check LampΤJ
-- preserve heritor plus Clipped Phase.H.Lambda
abbrev DialsBJ(P:Spine)(θ: BandS→ℕ):=∀ x:P.VMark,Signed × Bool→∀u:BandS,LampHouseJ (θ:=θ) u
structure AxonsJ (F: DialsBJ P θ) (V:P.Heritor) :Prop where
  go(x:P.VMark)(R:Signed × Bool)(u:BandS): LampΤJ p B0 M x R u A (F x R u) V.path
lemma countMarkJ(P:Spine): Countable (P.VMark):=by
 let L:= timeMesh P.par; haveI:Countable (marks L):=Function.Surjective.countable (f:=fun i:ℕ×ℤ=>notch L i.1 i.2) (fun i=>by obtain ⟨x,v,rfl⟩:= notch_exists L i; exact ⟨(x,v),rfl⟩); change Countable (Axis→marks L); infer_instance -- tune syntax
lemma AxonsJ.long (S:DialsBJ P θ)(V:P.Heritor)(Q:AxonsJ p B0 M A S V)(a:Slow): AxonsJ p B0 M A S (V.long a) :=by
 let L:=V.path.more_delay a; constructor; intro x R u; have h:= Q.go x R u; exact ⟨fun s p=>ThreadShopJ.delay L (h.step s p),fun l s p=>ThreadShopJ.delay L (h.tilt l s p),fun l s p=>ThreadShopJ.delay L (h.fare l s p)⟩
local notation "Ρ1"=> Stencil1Q p B0 M
local notation "Ρ2"=> Stencil2Q p B0 M
local notation "Ρ3"=> Stencil3Q p B0 M
lemma riseAx (V:P.Heritor): ∃ T:Slow,∃ F:DialsBJ P θ, AxonsJ p B0 M A F (V.long T) :=by
 let U:= P.VMark × (Signed × Bool) × BandS × ({s:ℕ// f0 ≤ s})
 let I:= U ⊕ (U× Bool × finsJ)
 let C (x:P.VMark)(R:Signed × Bool) (u:BandS)(s:{s:ℕ// f0 ≤ s})(i): ThreadJ (E:=Fin (θ u)) := Ρ1 x R u A s.val s.property i
 let D(x:P.VMark)(R:Signed × Bool) (u:BandS)(s:{s:ℕ// f0≤ s})(B:Bool)(l)(i): ThreadJ (E:=Fin (θ u)):= if B then Ρ2 x R u l A s.val s.property i else Ρ3 x R u l A s.val s.property i
 let P' : I→ Slow → Prop := fun i T=> match i with
 | .inl (x,r,u,s)=>∃ F, ThreadShopJ (Fin (θ u)) (V.path.more T) (C x r u s) F
 | .inr ((x,r,u,s),B,l)=>∃ F, ThreadShopJ (Fin (θ u)) (V.path.more T) (D x r u s B l) F
 have h(i: I)(T:Slow):∃ B:Slow,P' i (T.more B):=by
    rcases i with ⟨x,r,u,s⟩|⟨⟨x,r,u,s⟩,b,l⟩
    · obtain ⟨a,k,c,h⟩:= FundsΧ p B0 M x r u 0 A s.val s.property; exact χChooseJ _ k a (V.path.more T) c -- more assoc defeq
    · obtain ⟨a,k,c,h,g⟩:= FundsΧ p B0 M x r u l A s.val s.property; cases b with
      | true=> exact χChooseJ _ _ _ (V.path.more T) h
      | false=> exact χChooseJ _ _ _ (V.path.more T) g
 have he(i: I)(T:Slow)(p:P' i T)(S:Slow)(v:T.Delayed S): P' i S:=by
    have h:(V.path.more T).Delayed (V.path.more S):= v.mono (fun j h=> by obtain ⟨x,b⟩:=h; exact ⟨x,congrArg V.path.subSeq b⟩)
    rcases i with ⟨x,r,u,s⟩|⟨⟨x,r,u,s⟩,b,l⟩ <;> obtain ⟨Z,t⟩:=p <;> exact ⟨Z,ThreadShopJ.delay h t⟩
 haveI: Countable I:=by unfold I U; letI:=countMarkJ P; infer_instance
 obtain ⟨T,w⟩:= Slow.selectors P' h he
 choose Cγ pC using (fun x r u s=> w (.inl (x,r,u,s)))
 choose Dγ pD using (fun x r u s b l=> w (.inr ((x,r,u,s),b,l)))
 let Gβ x r u (s:ℕ) :ThreadJ (E:=Fin (θ u)):= if h:f0 ≤ s then Cγ x r u ⟨s,h⟩ else 0
 let Hκ x r u b l (s:ℕ): ThreadJ (E:=Fin (θ u)):= if h:f0 ≤ s then Dγ x r u ⟨s,h⟩ b l else 0
 let Pκ x r u: StaE (E:=Fin (θ u)):=⟨fun i=>(Gβ x r u i).1,fun i=> (Gβ x r u i).2⟩
 let F:DialsBJ P θ:=fun x r u=>⟨Pκ x r u,Hκ x r u true,Hκ x r u false⟩
 refine ⟨T,F,?_⟩; constructor; intro x r u; constructor
 · intro s p; change ThreadShopJ _ (V.path.more T) _ (Gβ x r u s); unfold Gβ; rw [dif_pos p]; exact pC x r u _
 · intro l s p; change ThreadShopJ _ _ _ (Hκ x r u true l s); unfold Hκ; rw [dif_pos p]; exact pD x r u ⟨s,p⟩ true l
 intro l s p; change ThreadShopJ _ _ _ (Hκ x r u false l s); unfold Hκ; rw [dif_pos p]; exact pD x r u ⟨s,p⟩ false l
#print axioms riseAx
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
