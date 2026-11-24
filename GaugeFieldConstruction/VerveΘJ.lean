import GaugeFieldConstruction.AlkahJ
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
/-- Mean Euclidean launch. No positivity assumed separate from these operators. -/
def Φscreen_eJ (L':finsJ)(U' H':PermWallJ P)(j:Axis)(v:FrameK (Fin (θ u))):P.Slabs j:= (ΦreleaseJ p B0 M x R u pu L' A T D V s0 U' H' j v).choose
variable (U H:PermWallJ P)(j:Axis)(r:ℕ)(v y:FrameK (Fin (θ u)))
local notation "Tψ" s:max V:max=> Φscreen_eJ p B0 M x R u pu A T D V s -- binder Lean.Reducibility.V! remove
local notation "ΓΘ"=> Φscreen_eJ p B0 M x R u pu A T D V s0
lemma ηsJ (L':finsJ): Tendsto (fun i=> FareΔJ B0 x R u L' T D s i v j U H) atTop (𝓝 (Φscreen_eJ p B0 M x R u pu A T D V s0 L' U H j v)):= (ΦreleaseJ p B0 M x R u pu L' A T D V s0 U H j v).choose_spec
abbrev WageFluxJ (L':finsJ)(l':ℕ):= FareΔJ B0 x R u L' T D s l' v j U H
local notation "Ψκ"=>WageFluxJ B0 x R u T D U H j v -- inference .s? implicit!
include V s0 g
lemma G0rateJ (q:L≠(0:finsJ))(d:s ≤ r)(e:f≤ r)(k:BelowWallJ P U H f): dist (FareΔJ B0 x R u L T D s r v j U H) (Φscreen_eJ p B0 M x R u pu A T D V s0 0 U H j v) ≤ ΦWallet p*FlavorRateJ P u f s r (LoomK v):=by
 let C' (i:ℕ):=ΦWallet p*FlavorRateJ P u f s i (LoomK v)
 have he:Tendsto C' atTop (𝓝 0):=by simpa using (arumJ p u (s:=s) (f:=f) (LoomK v)).const_mul (ΦWallet p)
 have ht(α β:finsJ)(a b:ℕ)(pa:max s f≤a)(pb:max s f≤b)(px:a≠b)(py:α≠β):dist (FareΔJ B0 x R u α T D s a v j U H) (FareΔJ B0 x R u β T D s b v j U H) ≤ C' a+C' b:= (EarpJ p B0 M x R u pu α A T D V g s0 U H j v β k (by omega) (by omega) (by omega) (by omega) px py.symm).trans_eq (mul_add ..)
 exact shoreDist L (WageFluxJ (s:=s) B0 x R u T D U H j v) C' he (max s f) ht (L':=0) (ηsJ p B0 M x R u pu A T D V s0 U H j v 0) q (max_le d e)
omit g
lemma ΦGateJ : Tendsto (fun r:ℕ=>FareΔJ B0 x R u L T D s r v j U H) atTop (𝓝 (Φscreen_eJ p B0 M x R u pu A T D V s0 0 U H j v)):=by
 by_cases h:L=0
 · subst L; exact ηsJ p B0 M x R u pu A T D V s0 U H j v _
 obtain ⟨f,z,f'⟩:= ((eventually_ge_atTop f0).and (farWallJ U H)).exists; let C' (i:ℕ):= ΦWallet p*FlavorRateJ P u f s i (LoomK v)
 have he:Tendsto C' atTop (𝓝 0):=by simpa using (arumJ p u (s:=s) (f:=f) (LoomK v)).const_mul (ΦWallet p)
 apply Metric.tendsto_nhds.mpr; intro ε e
 filter_upwards [he.eventually (gt_mem_nhds e),eventually_ge_atTop f,eventually_ge_atTop s] with i hx hu ht
 exact lt_of_le_of_lt (G0rateJ p B0 M x R u pu L A T D V z s0 U H j i v h ht hu f') hx
-- real price.T.K.Display.linear.
abbrev MeshΦ (s0:f0 ≤ s)(v:FrameK (Fin (θ u))): ScreensJ P:=fun j U H=>Φscreen_eJ p B0 M x R u pu A T D V s0 0 U H j v
local notation "Ξκ"=>MeshΦ p B0 M x R u pu A T D V s0 v j U H
include g
lemma πεArt (L':finsJ)(d:L ≠ L')(a:s≤r)(t:f≤r)(q:BelowWallJ P U H f): dist (FareΔJ B0 x R u L T D s r v j U H) (MeshΦ p B0 M x R u pu A T D V s0 v j U H) ≤ ΦWallet p*FlavorRateJ P u f s r (LoomK v):=by
 -- fix L any incl 0. second lane high.
 let C' (i:ℕ):=ΦWallet p*FlavorRateJ P u f s i (LoomK v)
 have he:Tendsto C' atTop (𝓝 0):=by simpa using (arumJ p u (s:=s) (f:=f) (LoomK v)).const_mul (ΦWallet p)
 have ht(α β:finsJ)(a b:ℕ)(pa:max s f≤a)(pb:max s f≤b)(px:a≠b)(py:α≠β):dist (FareΔJ B0 x R u α T D s a v j U H) (FareΔJ B0 x R u β T D s b v j U H) ≤ C' a+C' b:= (EarpJ p B0 M x R u pu α A T D V g s0 U H j v β q (by omega) (by omega) (by omega) (by omega) px py.symm).trans_eq (mul_add ..)
 exact shoreDist L (WageFluxJ (s:=s) B0 x R u T D U H j v) C' he (max s f) ht (L':=L') (ΦGateJ p B0 M x R u pu L' A T D V s0 U H j v) d (max_le a t)
lemma ΘChargeJ (e:s≤r)(z:f≤r)(k:BelowWallJ P U H f): dist (FareΔJ B0 x R u L T D s r v j U H) (MeshΦ p B0 M x R u pu A T D V s0 v j U H) ≤ ΦWallet p*FlavorRateJ P u f s r (LoomK v):=by
 classical
 by_cases y:L=(0:finsJ); apply πεArt p B0 M x R u pu L A T D V g s0 U H j r v 1 _ e z k; rw[y]; decide
 exact πεArt p B0 M x R u pu L A T D V g s0 U H j r v 0 y e z k
lemma HeatMarkJ (k:BelowWallJ P U H f): ‖MeshΦ p B0 M x R u pu A T D V s0 v j U H‖ ≤ ΦWallet p*FarePQ P f s u (LoomK v):=by
 let C':= FareΔJ B0 x R u 0 T D s; have hz := ΦGateJ p B0 M x R u pu 0 A T D V s0 U H j v; let γ:=ΦWallet p; let M':=FarePQ P f s u (LoomK v); have he:Tendsto (fun i=> γ*ChargeGX P u f s i (LoomK v)) atTop (𝓝 (γ*M')):=by simpa only [zero_add] using (((arumJ p u (s:=s) (f:=f) (LoomK v)).add (tendsto_const_nhds (x:=M'))).const_mul γ)
 exact le_of_tendsto_of_tendsto hz.norm he (((eventually_ge_atTop f).and (eventually_ge_atTop s)).mono (fun i ⟨z,x'⟩=> (SeroxJ p B0 M x R u pu 0 A T D V g s0 U H j i v x' z k).2))
omit g
lemma ePlusJ : MeshΦ p B0 M x R u pu A T D V s0 (v+y)= MeshΦ p B0 M x R u pu A T D V s0 v+MeshΦ p B0 M x R u pu A T D V s0 y:=by
 funext j U H; obtain ⟨f,a,z⟩:= ((eventually_ge_atTop f0).and (farWallJ U H)).exists; let G (v:FrameK (Fin (θ u))):= ΦGateJ p B0 M x R u pu 0 A T D V s0 U H j v
 apply tendsto_nhds_unique_of_eventuallyEq (G (v+y)) ((G v).add (G y)); filter_upwards [eventually_ge_atTop s,eventually_ge_atTop f] with r d h
 have he(w:FrameK (Fin (θ u))):=_root_.id ((SeroxJ p B0 M x R u pu 0 A T D V a s0 U H j r w d h z).1) -- tune id
 let W:= LaunchLJ B0 x R u 0 T D s r d
 exact (he _).same ((by rw[W.map_add]; exact (he v).plus (he y)) : CallBoxJ x U H j (W (v+y)) _ _) -- implicit 
lemma eTuneJ (l':ℂ): MeshΦ p B0 M x R u pu A T D V s0 (l'•v)= l'•MeshΦ p B0 M x R u pu A T D V s0 v:=by
 funext j U H; obtain ⟨f,a,z⟩:=((eventually_ge_atTop f0).and (farWallJ U H)).exists; let G (v:FrameK (Fin (θ u))):= ΦGateJ p B0 M x R u pu 0 A T D V s0 U H j v
 apply tendsto_nhds_unique_of_eventuallyEq (G (l'•v)) ((tendsto_const_nhds (x:=l')).smul (G v)); filter_upwards [eventually_ge_atTop s,eventually_ge_atTop f] with r d h
 have he(w:FrameK (Fin (θ u))):= (SeroxJ p B0 M x R u pu 0 A T D V a s0 U H j r w d h z).1
 let W:=LaunchLJ B0 x R u 0 T D s r d; exact (he _).same ((by rw[W.map_smul]; exact (he v).scale l') : CallBoxJ x U H j (W (l'•v)) _ _)
def Φwall (s0:f0 ≤ s) : FrameK (Fin (θ u))→ₗ[ℂ] ScreensJ P where
 toFun:= MeshΦ p B0 M x R u pu A T D V s0
 map_add' x' y':=ePlusJ ..
 map_smul' l v:=eTuneJ p B0 M x R u pu A T D V s0 v l
#print axioms ΦGateJ
#print axioms ΘChargeJ
#print axioms HeatMarkJ
#print axioms eTuneJ
#print axioms Φwall
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
