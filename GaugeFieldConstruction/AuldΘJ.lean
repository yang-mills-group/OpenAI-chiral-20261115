import GaugeFieldConstruction.TebessaJ
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
local notation "μP"=> MeshΦ p B0 M x R u pu A T D V s0
-- algebra built from symbols full.s on *whole* point. not separated vectors assumed.
section
-- PP mark sections(topological closure)
def ΔWallP (s0:f0 ≤ s):(FrameK (Fin (θ u))× ℂ) →ₗ[ℂ] ScreensJ P where
 toFun i:= MeshΦ p B0 M x R u pu A T D V s0 i.1 + i.2 • CandΛJ P
 map_add' i j:=by
    let Y:= MeshΦ p B0 M x R u pu A T D V s0
    change Y (i.1+j.1)+(i.2+j.2) • _=_; rw [show Y _= _ from ePlusJ p B0 M x R u pu A T D V s0 i.1 j.1]; funext k s t; simp only [Pi.add_apply,Pi.smul_apply,add_smul]; abel
 map_smul' z i:= by
    let Y:=MeshΦ p B0 M x R u pu A T D V s0
    change Y (z • i.1)+(z*i.2) • _=z • (Y i.1+i.2 • CandΛJ P)
    rw [show Y _ = z • Y i.1 from eTuneJ ..]; funext k s t; simp only [Pi.add_apply,Pi.smul_apply]; simp only [mul_smul,smul_add]
lemma kickΔ (c:ℂ): ΔWallP p B0 M x R u pu A T D V s0 (v,c)=MeshΦ p B0 M x R u pu A T D V s0 v+c • CandΛJ P:=rfl
abbrev Panmart (p:RosterJ P θ G f0)(B0:SωJ θ)(M:JωL θ)(x:P.VMark)(R:Signed × Bool)(u:BandS)(pu:Adept_T θ B0 M G)(A:CalendarJ p B0 M)(T:LampHouseJ (θ:=θ) u)(D:P.Heritor)(V:LampΤJ p B0 M x R u A T D.path)(s:ℕ)(s0:f0≤ s): Submodule ℂ (ScreensJ P):= LinearMap.range (ΔWallP p B0 M x R u pu A T D V s0)
lemma Δmk (c:ℂ) : MeshΦ p B0 M x R u pu A T D V s0 v+ c • CandΛJ P∈ Panmart p B0 M x R u pu A T D V s s0:= ⟨(v,c),rfl⟩
lemma PantryΔ : FiniteDimensional ℂ (Panmart p B0 M x R u pu A T D V s s0):=Module.Finite.range _ -- tune
local notation "κΣ" s:max g:max=>Panmart p B0 M x R u pu A T D V s g
#synth ContinuousAdd (ScreensJ P)
#synth T2Space (ScreensJ P)
lemma PantrySeal : IsClosed (Panmart p B0 M x R u pu A T D V s s0:_root_.Set (ScreensJ P)):=by haveI:= PantryΔ p B0 M x R u pu A T D V s0; exact Submodule.closed_of_finiteDimensional _ -- tune
lemma PantryForever {r:ℕ}(e:s ≤ r): Panmart p B0 M x R u pu A T D V r (s0.trans e)=Panmart p B0 M x R u pu A T D V s s0:=by
 let Q:=MeshΦ p B0 M x R u pu A T D V s0; let F:=PlcJ r s T.stairs e; let H:=AcJ T.stairs r s e; let Q':=MeshΦ p B0 M x R u pu A T D V (s0.trans e); let Ω:=CandΛJ P
 have h (v:FrameK (Fin (θ u)))(z:ℂ): Q v+ z • Ω=Q' (F v)+(z-H v) • Ω:=by rw [show Q v= _ from gateLeyJ p B0 M x R u pu A T D V s0 v e]; change Q' (F v)- H v • Ω+z • Ω=_; funext j u v; simp only [Pi.add_apply,Pi.sub_apply, Pi.smul_apply,sub_smul]; abel
 apply le_antisymm
 · intro i p'; obtain ⟨⟨v,z⟩,rfl⟩:=p'; change Q' v+ z • Ω∈ _; obtain ⟨y,rfl⟩:= ((ΞPlc p B0 M x R u A T D V s0 e).2.1.2 v); exact ⟨(y,z+H y),(show Q y +(z + H y) • Ω= _ from (by rw [h,add_sub_cancel_right]))⟩
 intro i h'; obtain ⟨⟨v,z⟩,rfl⟩:=h'; change Q v+ z • Ω∈ _; exact ⟨(F v,z-H v),(h v z).symm⟩
end
-- Padding prices: mesh only now; continuous all. Cost shelf.
abbrev HeatTaxJ (P:Spine)(j:Axis)(a b:ℝ)(A:P.Slabs j):= P.Eucl j a.toNNReal * A * P.Eucl j b.toNNReal
local notation "Ξμ"=> HeatTaxJ P i
local notation "δ_"=> StallJ P
lemma offWallP (u v:PermWallJ P){F:P.Test}{t:ℕ}{X:P.Slabs i}(p:CallBoxJ x σ τ i F X t)(h:StallJ P σ≤ StallJ P u)(e:StallJ P τ ≤ StallJ P v): CallBoxJ x u v i F (HeatTaxJ P i (StallJ P u-StallJ P σ) (StallJ P v-StallJ P τ) X) t:=by
 have he:=p.pad (D:=x i-u.val) (E:=x i+v.val) (sub_le_sub_left h _) (add_le_add_right e _)
 let k:ℝ:=(x i:ℝ); change P.Habitable _ _ _ _ _ (Ξμ (k-StallJ P σ-(k-StallJ P u)) (k+StallJ P v-(k+StallJ P τ)) X) at he
 rw[show k- StallJ P σ-(k-StallJ P u)=StallJ P u-StallJ P σ by ring,show k+StallJ P v-(k+StallJ P τ)=StallJ P v-StallJ P τ by ring] at he; exact he
abbrev Fuel_J (P:Spine)(S: ScreensJ P):Prop:=∀ (i:Axis)(σ τ U V:PermWallJ P), StallJ P σ ≤ StallJ P U → StallJ P τ ≤ StallJ P V → S i U V=HeatTaxJ P i (StallJ P U-StallJ P σ) (StallJ P V-StallJ P τ) (S i σ τ)
lemma ScaleLoanΓ : Fuel_J P (MeshΦ p B0 M x R u pu A T D V s0 v):=by
 intro i σ τ X Z h e; obtain ⟨f,u',a⟩:=((farWallJ (P:=P) σ τ).and (eventually_ge_atTop f0)).exists
 let Y:=HeatTaxJ P i (StallJ P X-StallJ P σ) (StallJ P Z-StallJ P τ); have hy:Continuous Y:=by unfold Y HeatTaxJ; fun_prop
 apply tendsto_nhds_unique_of_eventuallyEq (ΦGateJ p B0 M x R u pu 0 A T D V s0 X Z i v) (hy.continuousAt.tendsto.comp (ΦGateJ p B0 M x R u pu 0 A T D V s0 σ τ i v)); filter_upwards[eventually_ge_atTop s,eventually_ge_atTop f] with r d k
 exact ((SeroxJ p B0 M x R u pu 0 A T D V a s0 X Z i r v d k ⟨u'.1.trans h,u'.2.trans e⟩).1.same (offWallP x σ τ i X Z (SeroxJ p B0 M x R u pu 0 A T D V a s0 σ τ i r v d k u').1 h e))
lemma ΛUnitsJ (P:Spine) : Fuel_J P (CandΛJ P):=fun i σ τ X Z h e=> (UnitWallJ (0:P.VMark) X Z i 0).same (offWallP _ _ _ _ _ _ (UnitWallJ (0:P.VMark) σ τ i 0) h e)
lemma PhaseFuel {X:ScreensJ P}(h:X∈ Panmart p B0 M x R u pu A T D V s s0) : Fuel_J P X:=by
 obtain ⟨⟨v,z⟩,rfl⟩:=h; rw[kickΔ]; intro i σ τ X Z h e; let W:= HeatTaxJ P i (StallJ P X-StallJ P σ) (StallJ P Z-StallJ P τ); simp only [Pi.add_apply,Pi.smul_apply]; rw [ScaleLoanΓ p B0 M x R u pu A T D V s0 v i σ τ X Z h e, ΛUnitsJ P i σ τ X Z h e]; unfold HeatTaxJ; rw [mul_add,add_mul,mul_smul_comm,smul_mul_assoc] -- tune lhs rewriting.
#print axioms PhaseFuel
#print axioms PantrySeal
#print axioms PantryForever
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
