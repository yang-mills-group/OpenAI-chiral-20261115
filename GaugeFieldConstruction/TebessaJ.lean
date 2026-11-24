import GaugeFieldConstruction.NuttyΞJ
import GaugeFieldConstruction.OptioJ
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
variable {r i k:ℕ} (z:Cover)
local notation "φY" s:max z:max=> strideΨJ P f s z
local notation "Wκ"=> Rigχ P f z
local notation "yκ"=> fleetΨJ P f z x
local notation "ΩW"=>ΟGlow (Rigχ P f z f) false P.par
local notation "Κφ" T:max s:max r:max κ:max=>AcJ (T:LampHouseJ u).stairs r s κ -- use explicit.
section
variable (T':LampHouseJ (θ:=θ) u)(H':LampΤJ p B0 M (fleetΨJ P f z x) R u A T' D.path)
include V H' g
-- l1 price. Phase compensated shot.
variable (v:FrameK (Fin (θ u)))(U H: PermWallJ P)(j:Axis)(φ:BelowWallJ P U H f)(q:f≤ r)
local notation "δ"=> StallJ P
local notation "πk"=> (ΦWallet p)
local notation "Aρ"=> Φwall p B0 M x R u pu A T D V g
local notation "xκ"=> P.vtile f z
local notation "Kρ'"=>RankQJ P.par f
local notation "ΦL"=> FlavorRateJ P u
local notation "μK"=> ScaleμJ P.par u.val
include q φ pu
lemma PicρJ : ‖(P.ambientTurn j (P.vtile f z) (FareΔJ B0 x R u L T D f r v j U H))- (MeshΦ p B0 M (fleetΨJ P f z x) R u pu A T' D H' g v j U H)‖≤ (4*ΦWallet p+4)*FlavorRateJ P u f f r (LoomK v)+4*ΦWallet p*FlavorRateJ P u f f r (LoomK v):=by -- generous 32...
 let Y:=fleetΨJ P f z x; let W:=P.ambientTurn j (xκ); let S:=DownJ T'.stairs r f q; let X:= (T.rev L r).1 (S.1 v); let C:=(T.sun L r); let Z:= (T'.sun L r); let a:= S.2 v+C.2 X; let B:= BrJ u Z.1 X; let V' (v):= MeshΦ p B0 M Y R u pu A T' D H' g v j U H; let Vt':= MeshΦ p B0 M Y R u pu A T' D H' (g.trans q) B j U H; let Ψ:= CandΛJ P j U H; let l:= r-f; let μ:= ScaleμJ P.par u.val; let R':ℂ:= (↑μ:ℂ)^l; let X':= LaunchLJ B0 x R u L T D f r q v; let b:=FareΔJ B0 x R u L T D f r v j U H
 have hP:= WarmStart p B0 M x R u L A T D V g v q; dsimp only at hP; have pe:=PlatoO p B0 M x R u A T D V g z T' H' q; rw[pe] at hP; let hx:=hP.1; let hv:=hP.2.1; let Θ':=strideΨJ P f r z
 have q':P.chartAll Θ' X'=PaletteEJ B0 Y R u D r X - a • (1:P.Test):=by unfold X'; rw [hv, map_sub,map_smul,map_one,A_rShiftJ B0 x R u D z q] -- any extra v
 let α':=ΦWallet p; let Q:= RankQJ P.par f; let M' (z:ℝ):=ΦWallet p* FlavorRateJ P u f r r z
 obtain ⟨W',eW,e⟩:= LawΦsJ p B0 M Y R u pu L A T' D H' g U H j X (g.trans q) q φ -- tune order
 have θT: W b=W'-a • Ψ := by
    have he:= Queenκ x z _ U H j q b (SeroxJ p B0 M x R u pu L A T D V g g U H j r v q q φ).1 -- tuner
    rw[q'] at he; exact he.same (eW.minus ((UnitWallJ Y U H j r).scale a))
 obtain ⟨E,eT,Z'⟩:= FleetBillQ p B0 M x R u pu L A T D V g z T' H' v q; let Δ := V' (E.1 X)+E.2 X • Ψ; have ht:(Vt'+Z.2 X • Ψ)- a • Ψ= V' v - R' • Δ:= congrFun (congrFun (congrFun Z' j) U) H; let G:=Vt'+Z.2 X • Ψ; change ‖W b- V' v‖≤_; rw [show W b- V' v=(W'-G)- R' • Δ from (by rw [θT, show V' v= (G - a • Ψ)+R' • Δ from eq_add_of_sub_eq ht.symm]; abel)]
 have hμ:0≤ μ:= (p.price _ g u f).small; have hq:0≤ Q:= (p.tempo f g).1.le; have he0:0≤ α':= (WalletB p).le; let H₀:= stepRateJ P.par u.val; let T0:= LoomK v; let xB:= 2*(H₀^l*T0); let β:= μ^l; have hy:LoomK X ≤ xB:=hx; have hb:0≤β:=pow_nonneg hμ _; have z:0 ≤ xB:=(noLoom X).trans hy
 have hΔ:‖Δ‖ ≤ (α'+1)*Q*xB:=by
    apply (norm_add_le ..).trans
    have he:= HeatMarkJ p B0 M Y R u pu A T' D H' g g U H j (E.1 X) φ; unfold FarePQ at he; rw [if_pos le_rfl] at he; have hz:= he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((eT.1 X).trans ((one_mul _).le.trans hy)) hq) he0); rw[norm_smul]; refine (add_le_add hz (mul_le_mul ((eT.2 X).trans (mul_le_mul_of_nonneg_left hy (show 0≤1*Q by positivity))) (P.heat_norm ..) (norm_nonneg _) (mul_nonneg (by simpa using hq) z))).trans_eq ?_; unfold α' Q; ring
 have hp:‖R'‖=β:=by unfold R' β; rw [norm_pow,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg hμ]
 unfold FlavorRateJ at e ⊢ -- tune repeated
 refine (norm_sub_le ..).trans ((add_le_add e (show ‖R' • Δ‖≤β*((α'+1)*Q*xB) from ?_)).trans ?_)
 · rw [norm_smul,hp]; exact mul_le_mul_of_nonneg_left hΔ hb
 let τ':=α'* (4* β* Q); have v: 0≤ τ':= mul_nonneg he0 (mul_nonneg (mul_nonneg (by norm_num) hb) hq)
 change α' * (4 * β * Q * H₀^(r-r)*(2*LoomK X))+_≤(4*α'+4)*(4*β*Q*H₀^l*T0)+4*α'*(4*β*Q*H₀^l*T0); rw [Nat.sub_self,pow_zero,mul_one,←mul_assoc]
 apply (add_le_add_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (show 0≤ (2:ℝ) by norm_num)) v) _).trans -- may orientation right
 have hG:0≤ H₀^l*T0:=by linarith only[z]
 unfold τ' xB at *; nlinarith only [mul_nonneg (mul_nonneg hb hq) hG,mul_nonneg he0 (mul_nonneg (mul_nonneg hb hq) hG)]
omit q
lemma floorLipJ (d:BelowWallJ P U H f): P.ambientTurn j (P.vtile f z) (MeshΦ p B0 M x R u pu A T D V g v j U H)= MeshΦ p B0 M (fleetΨJ P f z x) R u pu A T' D H' g v j U H:=by
 let Y:=P.ambientTurn j (P.vtile f z); let Z:=MeshΦ p B0 M (fleetΨJ P f z x) R u pu A T' D H' g v j U H; let R'(i):= FareΔJ B0 x R u 0 T D f i v j U H; have he:=ΦGateJ p B0 M x R u pu 0 A T D V g U H j v; have ha(i:ℕ)(u':f ≤ i):= PicρJ p B0 M x R u pu 0 A T D V g z T' H' v U H j d u'; have hv: Continuous Y:=by unfold Y ambientTurn; fun_prop
 apply tendsto_nhds_unique (hv.continuousAt.tendsto.comp he); let F:= (fun r:ℕ=> FlavorRateJ P u f f r (LoomK v)); let C:=ΦWallet p; have g:Tendsto F atTop (𝓝 0):= arumJ p u _; have he:Tendsto (fun i=>(4*C+4)*F i+4*C*F i) atTop (𝓝 0):=by simpa using ((g.const_mul (4*C+4)).add (g.const_mul (4*C)))
 apply Metric.tendsto_nhds.mpr; intro ε e; filter_upwards [he.eventually (gt_mem_nhds e),eventually_ge_atTop f] with i h z; change dist (Y (R' i)) Z < _; rw [dist_eq_norm]; exact lt_of_le_of_lt (ha i z) h
omit φ
lemma HullLipsJ : P.ambientTurn j (P.vtile f z) (MeshΦ p B0 M x R u pu A T D V g v j U H)= MeshΦ p B0 M (fleetΨJ P f z x) R u pu A T' D H' g v j U H:=by
 let Y:= fleetΨJ P f z x; obtain ⟨r,e,f'⟩:= ((farWallJ U H).and (eventually_ge_atTop f)).exists
 let S:=DownJ T'.stairs r f f'; let V':= (φY r z); have hv:P.vtile r V'=P.vtile f z:=(spoolJ _ f').symm
 have ht:fleetΨJ P r V' x=Y:=congrArg (x+·) hv; have hC: LampΤJ p B0 M (fleetΨJ P r V' x) R u A T' D.path:=by rw[ht]; exact H'
 let Z:=CandΛJ P j U H; let a:=P.vtile f z; let w:=S.1 v; have Hκ:=floorLipJ p B0 M x R u pu A T D V (g.trans f') V' T' hC w U H j e e; -- d redundant? tune
 rw [hv] at Hκ; -- rewrite dependent V. impossible.DLamp incl proof PU. use a forall transport. tune
 have h': P.ambientTurn j a (MeshΦ p B0 M x R u pu A T D V (g.trans f') w j U H)= MeshΦ p B0 M Y R u pu A T' D H' (g.trans f') w j U H:= by
    have hu(x' y':P.VMark)(X: LampΤJ p B0 M x' R u A T' D.path)(Z:LampΤJ p B0 M y' R u A T' D.path)(h:x'=y') : MeshΦ p B0 M x' R u pu A T' D X (g.trans f') = MeshΦ p B0 M y' R u pu A T' D Z (g.trans f'):=by subst y'; rfl
    rw [← hu _ _ hC H' ht]; exact Hκ
 have ha:=PlatoO p B0 M x R u A T D V g z T' H' f'; rw [gateLeyJ p B0 M x R u pu A T D V g v f',gateLeyJ p B0 M Y R u pu A T' D H' g v f', ← DownL, ← DownL, AcJ, AcJ, ha]
 let F:=MeshΦ p B0 M x R u pu A T D V (g.trans f') w j U H; let X:=S.2 v; let W:=P.ambientTurn j a
 change W (F-X • Z)= _; change W (F-X • Z)= MeshΦ p B0 M Y R u pu A T' D H' (g.trans f') w j U H-X • Z
 rw[←h']; have hZ:W Z=Z:=by unfold W ambientTurn; unfold Z CandΛJ; rw[transit_share,mul_assoc,←transit_plus, add_neg_cancel, transit_zero,mul_one]
 change _=W F-X • Z; unfold W ambientTurn; rw[mul_sub,mul_smul_comm,_root_.sub_mul,smul_mul_assoc]; unfold W ambientTurn at hZ; rw [hZ] -- tune
#print axioms PicρJ
#print axioms floorLipJ
#print axioms HullLipsJ
end
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
