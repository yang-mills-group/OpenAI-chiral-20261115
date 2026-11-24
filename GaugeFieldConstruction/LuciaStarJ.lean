import GaugeFieldConstruction.AuldΘJ
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
-- continuity and RP read. Exponent usually U scaled finite horizon. nested across bands and orientations.
section
variable (i:Axis)(U H: PermWallJ P)
variable {F: P.Test}{S:P.Slabs i}
end
abbrev LiPaJ (B:SωJ θ)(R:Signed × Bool)(u:BandS): FrameK (Fin (θ u))→ₗ[ℂ] Waves:=scalB (ThreadΨ B u R)
private lemma RiskQ {E D:Type*}[AddCommMonoid E][AddCommMonoid D][Module ℂ E][Module ℂ D]{I:Type}[Fintype I](W:I→E)(o:E→ₗ[ℂ] D)(z:ℂ)(X:I→ℂ): (∑ i:I,X i • o (z • W i))=o (z • ∑ i:I,X i • W i):=by rw[smul_sum,map_sum]; apply sum_congr rfl; intro i _; rw [smul_comm z]; simp only [map_smul]
lemma PaletteQ (t:ℕ)(X:FrameK (Fin (θ u))): PaletteEJ B0 x R u D t X=D.M t (P.adventJ x t) ((RankQJ P.par t:ℂ) • LiPaJ B0 R u X):=by
 let W:=ThreadΨ B0 u R; let z:ℂ:=RankQJ P.par t; let o:=D.M t (P.adventJ x t)
 change ∑ i:Fin (θ u), X i • o (z • W i)=o (z • ∑ i:Fin (θ u), X i • W i)
 exact RiskQ .. 
variable (u':BandS)(h:u≤u')(R': Signed × Bool)(T':LampHouseJ (θ:=θ) u')(S':LampΤJ p B0 M x R' u' A T' D.path)
include pu p
lemma Tsava : Planaris (M u) ΓProj u.val (ThreadΨ B0 u R) G:= Billierd θ B0 M G P.par pu Unit (fun _=>R) 0 ((),u)
#print Tsava
include h
lemma ToothJ : ∃ A:FrameK (Fin (θ u))→ₗ[ℂ] FrameK (Fin (θ u')), ∀ v:FrameK (Fin (θ u)), LiPaJ B0 R u v= LiPaJ B0 R' u' (A v) ∧ LoomK (A v) ≤ G*(LoomK v*G):=by
 let E:= Tsava p B0 M R u pu; let W':=Tsava p B0 M R' u' pu
 have he(i:Fin (θ u)): ΓProj u'.val (ThreadΨ B0 u R i)=ThreadΨ B0 u R i:=by
    rw [E.saturated,if_pos ((E.ray i).trans h)]
 choose g eg using fun i=> W'.coframe _ (he i)
 let Z:=ArchBuildJ g
 have hG:0≤G:=by obtain ⟨t,F,B,s⟩:=pu; exact (F.trans (WindMore _ F)).trans B
 refine ⟨Z,fun v=>?_⟩; have hx:LiPaJ B0 R u v= LiPaJ B0 R' u' (Z v):=by
    change Woof v (ThreadΨ B0 u R)= LiPaJ B0 R' u' (∑ i:Fin (θ u), v i • g i); unfold Woof; rw[map_sum]; simp_rw[map_smul]; exact sum_congr rfl (fun i _=> congrArg (v i •·) (eg i)) -- tune
 exact ⟨hx, (W'.brake (Z v)).trans (mul_le_mul_of_nonneg_left ((le_of_eq (congrArg norm hx).symm).trans (woof_cost v E.bounded)) hG) ⟩
#print axioms ToothJ
include s0 V S'
local notation "DΘ"=> ΦWallet p
local notation "χK"=> stepRateJ P.par u.val
local notation "Φ'"=>MeshΦ p B0 M x R' u' pu A T' D S'
local notation "Ογ"=> Κg
#check PantryForever
#check LawΦsJ
#check alpha_nnC
lemma aptG (h:u ≤ u'): stepRateJ P.par u.val ≤ stepRateJ P.par u'.val:=by
 have he:(u.val:ℝ)≤ (u'.val:ℝ):=by exact_mod_cast (show u.val≤u'.val from h)
 exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast P.par.R.L.property) (by unfold DimsP; linarith)
lemma LawθNest (v:FrameK (Fin (θ u))): MeshΦ p B0 M x R u pu A T D V s0 v∈ Panmart p B0 M x R' u' pu A T' D S' s s0:=by
 -- use approximation heights r. Mark matched exactly. Pane product topology. pads.any eventually panel
 let Κ := Panmart p B0 M x R' u' pu A T' D S' s s0; let Ψ:=MeshΦ p B0 M x R u pu A T D V s0 v; let T₀:= LoomK v
 obtain ⟨F,qF⟩:= ToothJ p B0 M R u pu u' h R' -- tune
 let lΩ (r:ℕ)(p':s ≤ r):= DownJ T.stairs r s p'; let G0 (r:ℕ)(p':s≤ r):=(T.rev 0 r).1 ((DownJ T.stairs r s p').1 v); let d (r:ℕ)(p':s ≤ r):ℂ:= (lΩ r p').2 v+(T.sun 0 r).2 (G0 r p')
 let X (r:ℕ): ScreensJ P:= if w:s≤r then let Y:=F (G0 r w); let V:=T'.sun 0 r; MeshΦ p B0 M x R' u' pu A T' D S' (s0.trans w) (BrJ u' V.1 Y)+ V.2 Y • CandΛJ P - d r w • CandΛJ P else 0
 have q(r:ℕ)(v:s≤r): X r∈ Κ:=by unfold X Κ; rw[dif_pos v,← PantryForever p B0 M x R' u' pu A T' D S' s0 v]; dsimp only; let M':=T'.sun 0 r; let Y:=F (G0 r v); let A':=MeshΦ p B0 M x R' u' pu A T' D S' (s0.trans v) (BrJ u' M'.1 Y); let W:=CandΛJ P; change A'+M'.2 Y • W- d r v • W∈ _; rw [show A'+M'.2 Y • W- d r v • W=A'+(M'.2 Y-d r v) • W from (by funext k i j; simp only [Pi.sub_apply,Pi.smul_apply, Pi.add_apply]; rw[sub_smul]; abel)]; exact Δmk ..
 refine (PantrySeal p B0 M x R' u' pu A T' D S' s0).mem_of_tendsto (tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr (fun H=> tendsto_pi_nhds.mpr (fun W=>?_)))) ((eventually_ge_atTop s).mono q)
 obtain ⟨f,gF,f'⟩:= ((farWallJ H W).and (eventually_ge_atTop s)).exists
 let U :ℕ → P.Slabs i:= fun r=> FareΔJ B0 x R u 0 T D s r v i H W; have he:= ΦGateJ p B0 M x R u pu 0 A T D V s0 H W i v
 let C'(r:ℕ)(z:ℝ):= ΦWallet p*FlavorRateJ P u' f r r (2*z); let M':ℝ:=stepRateJ P.par u'.val; let Z(r:ℕ):= G*((2*(M'^(r-s)*T₀))*G); let Y r:= C' r (Z r)
 have hz:Tendsto Y atTop (𝓝 0):=by
    let τ:= ΦWallet p; have hy(r:ℕ):Y r=(τ*4*T₀*G*G)*FlavorRateJ P u' f s r 1:=by unfold Y C' Z M' FlavorRateJ; rw [Nat.sub_self,pow_zero]; unfold τ; ring
    simp_rw [show Y=(fun r=> _ *FlavorRateJ P u' f s r 1) from funext hy]; simpa only [mul_zero] using ((arumJ p u' (f:=f) (s:=s) 1).const_mul (τ*4*T₀*G*G)) -- tune binder.
 have hg:0≤G:=let ⟨t,F,B,y⟩:=pu; (F.trans (WindMore _ F)).trans B
 have hh(r:ℕ)(d':f≤r): ‖X r i H W- U r‖≤Y r:=by
    let e:=f'.trans d'; let V0:=G0 r e; let V':=F V0; let w:=T'.sun 0 r; have hY:= (qF V0).2; obtain ⟨X',hu,hy⟩:= LawΦsJ p B0 M x R' u' pu 0 A T' D S' (s0.trans f') H W i V' (s0.trans e) d' gF; have hz:= (SeroxJ p B0 M x R u pu 0 A T D V (s0.trans f') s0 H W i r v e d' gF).1; let Ψ':= CandΛJ P i H W; let Ω':= MeshΦ p B0 M x R' u' pu A T' D S' (s0.trans e) (BrJ u' w.1 V') i H W; let z:=d r e
    obtain ⟨hG',pG,k⟩:= WarmStart p B0 M x R u 0 A T D V s0 v e; have he:PaletteEJ B0 x R u D r V0=PaletteEJ B0 x R' u' D r V':=by rw[PaletteQ,PaletteQ, (qF V0).1]
    unfold X; rw [dif_pos e]; change ‖Ω'+w.2 V' • Ψ'- z • Ψ'- U r‖≤Y r; rw [show U r=X'-z • Ψ' from (by rw[pG,he] at hz; exact hz.same (hu.minus ((UnitWallJ x H W i r).scale z))), sub_sub_sub_cancel_right,norm_sub_rev]
    refine hy.trans (mul_le_mul_of_nonneg_left ?_ (WalletB p).le); let k:=p.price f (s0.trans f') u' r; have he:0 ≤ M':=zero_le_one.trans k.bound
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hY.trans ?_) (by norm_num)) ?_
    · have hz:0≤ stepRateJ P.par u.val:=zero_le_one.trans (p.price _ s0 u r).bound; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hG'.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz (aptG p B0 M x R u pu A T D V s0 u' h R' T' S' h) (r-s)) (noLoom v)) (by norm_num))) hg) hg -- binder tune Apt
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg k.small _)) (k.hot le_rfl d').le) (pow_nonneg he _)
 apply Metric.tendsto_nhds.mpr; intro t ht; filter_upwards [eventually_ge_atTop f,hz.eventually (gt_mem_nhds (show 0<t/2 from half_pos ht)), Metric.tendsto_nhds.mp he _ (half_pos ht)] with i' d h e
 apply lt_of_le_of_lt (dist_triangle _ (U i') _); rw [dist_eq_norm (a:= X i' i H W)] -- tune
 exact lt_of_lt_of_le (add_lt_add (lt_of_le_of_lt (hh i' d) h) e) (le_of_eq (add_halves _))
omit h S'
lemma UnitσP (c:ℂ): c • CandΛJ P∈ Panmart p B0 M x R u pu A T D V s s0:=by refine ⟨(0,c),?_⟩; rw [kickΔ p B0]; change Φwall p B0 M x R u pu A T D V s0 0+_= _; rw [map_zero,zero_add]
include h S'
lemma PlanΘJ : Panmart p B0 M x R u pu A T D V s s0 ≤ Panmart p B0 M x R' u' pu A T' D S' s s0:=by intro i h'; obtain ⟨⟨v,z⟩,rfl⟩:=h'; rw[kickΔ]; exact Submodule.add_mem _ (LawθNest p B0 M x R u pu A T D V s0 u' h R' T' S' v) (UnitσP p B0 M x R' u' pu A T' D S' s0 z) -- `LawθNest ..` implicit params catch
#print axioms PlanΘJ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
