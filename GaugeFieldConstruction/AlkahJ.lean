import GaugeFieldConstruction.StevanjaJ
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
-- Universe all mean slabs at strictly positive pad pairs. retain mesh walls centered at x.
-- after pad real extension underlying space no rank shift.
abbrev PermWallJ (P:Spine):= {z :P.meshPin//(0:ℝ)<(z:ℝ)}
abbrev ScreensJ (P:Spine) := ∀ (j:Axis), PermWallJ P→PermWallJ P→ P.Slabs j
variable (U H:PermWallJ P) (j:Axis) (r:ℕ) (v:FrameK (Fin (θ u)))
abbrev StallJ (P:Spine)(d:PermWallJ P):ℝ:= d.val
local notation "δ"=> StallJ P
local notation "Λδ"=> LaunchLJ B0 x R u L T D
abbrev CallBoxJ (F:P.Test) (X:P.Slabs j) (s:ℕ) : Prop:= P.Habitable j F s (x j-U.val) (x j+H.val) X
abbrev BelowWallJ (P:Spine)(U H:PermWallJ P)(f:ℕ):Prop:= PlethoraJ P f ≤ StallJ P U ∧ PlethoraJ P f ≤ StallJ P H
lemma ValPanelJ (h: BelowWallJ P U H f): PanelH_J P f x j (x j-U.val) (x j+H.val):=⟨sub_le_sub_left h.1 _,add_le_add_right h.2 _⟩
lemma farWallJ :∀ᶠ f:ℕ in atTop,BelowWallJ P U H f:=((SecondEraJ P).eventually (ge_mem_nhds U.property)).and ((SecondEraJ P).eventually (ge_mem_nhds H.property)) -- inference tune
-- default quote only used when every forward law ensures Habitable.Unique.Minic
abbrev costΞJ (P:Spine)(j:Axis)(x:P.VMark)(s:ℕ)(U H:PermWallJ P)(F:P.Test):P.Slabs j := if h:∃ X:P.Slabs j,CallBoxJ x U H j F X s then h.choose else 0
lemma ℓγHeard (j:Axis)(x:P.VMark)(F:P.Test){X:P.Slabs j}(u:CallBoxJ x U H j F X s): costΞJ P j x s U H F=X:=by unfold costΞJ; have he:∃ x',CallBoxJ x U H j F x' s:=⟨_,u⟩; rw [dif_pos he]; exact he.choose_spec.same u
abbrev FareΔJ (s r:ℕ)(v:FrameK (Fin (θ u))) : ScreensJ P:= fun j U H=> if h:s≤r then costΞJ P j x r U H (LaunchLJ B0 x R u L T D s r h v) else 0
local notation "τχ" s:max r:max v:max=> FareΔJ B0 x R u L T D s r v j U H -- argument order verify
include pu p V s0 g
lemma SeroxJ (q:s≤r)(z:f ≤ r)(u': BelowWallJ P U H f):CallBoxJ x U H j (LaunchLJ B0 x R u L T D s r q v) (FareΔJ B0 x R u L T D s r v j U H) r∧ ‖FareΔJ B0 x R u L T D s r v j U H‖ ≤ ΦWallet p*ChargeGX P u f s r (LoomK v):=by
 obtain ⟨W,p,q'⟩:= SkyPriceJ p B0 M x R u pu L A T D V g s0 q z v (ValPanelJ x U H j u'); dsimp only [FareΔJ]; rw [dif_pos q,ℓγHeard _ _ _ _ _ p] -- tune parameter
 exact ⟨p,q'⟩
local notation "Gχ" L:max r:max=> FareΔJ B0 x R u L T D s r v j U H
lemma EarpJ {a b:ℕ}(L':finsJ)(u':BelowWallJ P U H f)(e:s≤a)(f':s≤b)(x₁:f≤a)(x₂:f≤b)(d:a≠b)(d':L'≠L): dist (FareΔJ B0 x R u L T D s a v j U H) (FareΔJ B0 x R u L' T D s b v j U H) ≤ ΦWallet p*(FlavorRateJ P u f s a (LoomK v)+FlavorRateJ P u f s b (LoomK v)):=by
 let m:=max a b; have q:=SeroxJ p B0 M x R u pu L A T D V g s0 U H j a v e x₁ u'; have z:=SeroxJ p B0 M x R u pu L' A T D V g s0 U H j b v f' x₂ u'; have ht:a≤ m:=le_max_left ..; have hy:b≤ m:=le_max_right ..; obtain ⟨W,v',q'⟩:= SkyPairJ p B0 M x R u pu L A T D V g s0 L' v e f' x₁ x₂ ht hy d d' _ _ _ (ValPanelJ x U H j u'); rw [dist_eq_norm, show Gχ L a-Gχ L' b=W from (((Habitable.forward ht).1 q.1).minus ((Habitable.forward hy).1 z.1)).same v']; exact q'
omit pu V s0 g
private def fork_tJ (L:finsJ):finsJ:=if L=0 then 1 else 0
omit p in
private lemma forkY (L:finsJ):fork_tJ L≠L:=by by_cases p:L=0; rw [fork_tJ,if_pos p,p]; decide; rw [fork_tJ,if_neg p]; exact Ne.symm p
section abs
variable {Y:Type}[PseudoMetricSpace Y](F:finsJ→ℕ→ Y)(C:ℕ→ℝ)(hp:Tendsto C atTop (𝓝 0))(fq:ℕ)(Uq:∀ (L L':finsJ)(a b:ℕ), fq≤ a→fq≤ b→a≠b→L≠L'→ dist (F L a) (F L' b) ≤ C a+C b)
omit p
include hp Uq
lemma shoreY : CauchySeq (F L):=by
 apply Metric.cauchySeq_iff.mpr; intro ε e; obtain ⟨n,q⟩:=eventually_atTop.mp (hp.eventually (gt_mem_nhds (show 0< ε/4 from by linarith))) -- gt names tune
 refine ⟨max n fq,fun a p b z=>?_⟩
 let l:=max a b+1; have ha:a<l:=by unfold l; omega
 have hb:b<l:=by unfold l; omega
 let L':=fork_tJ L
 have v:=Uq L L' a l (by omega) (by omega) ha.ne (forkY L).symm; have w:=Uq L' L l b (by omega) (by omega) hb.ne' (forkY L)
 have ht:= (dist_triangle ..).trans (add_le_add v w); exact lt_of_le_of_lt ht (by linarith only [q a (by omega),q b (by omega),q l (by omega)])
lemma shoreDist {v:Y}{L':finsJ}(h:Tendsto (F L') atTop (𝓝 v))(d:L≠L'){r:ℕ}(p:fq≤ r):dist (F L r) v≤ C r:=by
 have hx: dist (F L r) v ≤ C r+0:=le_of_tendsto_of_tendsto (tendsto_const_nhds.dist h) (tendsto_const_nhds.add hp) ((eventually_gt_atTop r).mono (fun n q=> Uq L L' r n p (p.trans q.le) q.ne d))
 simpa using hx
end abs
include pu V s0 g
lemma LenwayJ (u0:BelowWallJ P U H f): CauchySeq (fun r:ℕ=>FareΔJ B0 x R u L T D s r v j U H):=by
 let G(k:finsJ)(l:ℕ):=FareΔJ B0 x R u k T D s l v j U H
 let Va (l:ℕ):= ΦWallet p * FlavorRateJ P u f s l (LoomK v)
 refine shoreY L G Va ?_ (max s f) ?_
 · simpa only [mul_zero] using ((arumJ p u (s:=s) (f:=f) (LoomK v)).const_mul (ΦWallet p))
 intro L L' a b p' q d t
 have h:= EarpJ p B0 M x R u pu L A T D V g s0 U H j v (a:=a) (b:=b) L' u0 (by omega) (by omega) (by omega) (by omega) d t.symm
 rw [mul_add] at h; exact h
omit g
lemma ΦreleaseJ :∃ X: P.Slabs j,Tendsto (fun r:ℕ=>FareΔJ B0 x R u L T D s r v j U H) atTop (𝓝 X):=by
 obtain ⟨f,z,f'⟩:= ((eventually_ge_atTop f0).and (farWallJ U H)).exists; exact cauchySeq_tendsto_of_complete (LenwayJ p B0 M x R u pu L A T D V z s0 U H j v f')
#print axioms LenwayJ
#print axioms ΦreleaseJ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
