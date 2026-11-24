import GaugeFieldConstruction.BootHearthJ
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
section price
open BProof BProof.PricePort
#check tendsto_pow_atTop_nhds_zero_of_lt_one
#check tendsto_pow_const_mul_const_pow_of_lt_one
#check tendsto_self_mul_const_pow_of_abs_lt_one
#check cauchySeq_iff_le_tendsto_0
#check Metric.cauchySeq_iff
include p
lemma arumJ (q:ℝ) : Tendsto (fun n:ℕ=>FlavorRateJ P u f s n q) atTop (𝓝 0):=by
 let μ:=ScaleμJ P.par u.val; let R':=βρ; let Y:=p.price f0 le_rfl u 0; have hv:1≤R':=Y.bound; have hk:0 ≤ μ*R':=mul_nonneg Y.small (zero_le_one.trans hv); have hz:μ*R'<1:=lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_trans (by linarith only [hv] : R' ≤ 2* R') Y.θpay) Y.small) Y.ψpay
 let M':=max s f; let K:=4*μ^(M'-f)*νP f*R'^(M'-s)*q
 have h':Tendsto (fun n:ℕ=> K * (μ*R')^(n-M')) atTop (𝓝 0):= by
    have hh:Tendsto (fun n:ℕ=> n -M') atTop atTop:= tendsto_atTop.mpr (fun b=> (eventually_ge_atTop (b+M')).mono (fun i h=> by omega))
    simpa only [Function.comp_def,mul_zero] using (((tendsto_pow_atTop_nhds_zero_of_lt_one hk hz).comp hh).const_mul K)
 refine h'.congr' ?_; filter_upwards [eventually_ge_atTop M'] with i hi; change K*(μ*R')^(i-M')= 4*μ^(i-f)*νP f*R'^(i-s)*q; rw [show i-f=M'-f+(i-M') from by unfold M' at *; omega,pow_add,show i-s=M'-s+(i-M') from by unfold M' at *; omega,pow_add]; unfold K; rw[mul_pow]; ring
omit p
local notation "ωf" f:max=> hat P.par.R.L P.par.x f
lemma flowerXJ (P:Spine): ∀ᶠ f in atTop,(WorkWJ P f:ℝ)≤hat P.par.R.L P.par.x f:=by
 let g:= logPrice 0 0 (FiatHighJ P) (c:=1) (d:=0) (w:=0) (v:=1) (Or.inl zero_lt_one) zero_lt_one; filter_upwards [(turnover P.par).eventually g, (turnover P.par).eventually_gt_atTop 0] with i h u; rw [one_mul,coinY u] at h -- tune
 exact h
-- even exponential gap stop.Later quantitative in δ. Store reward on scaled width whenever base less than L, including variable constant.Use LB geometric eventual.
variable {t:ℝ}
lemma PledgeJ (P:Spine)(s:ℕ) :0< PlethoraJ P s :=by
 unfold PlethoraJ; rw [P.mellow_firm]; apply mul_pos (P.mellow_good _); have hx:0<ruler P.par.block:= ruler_gene _; have hs:0<WorkWJ P s:=by unfold WorkWJ XûJ; omega; -- tune
 exact_mod_cast (show 0 < ruler P.par.block*(WorkWJ P s:ℤ) from mul_pos hx (by omega))
lemma PetitionJ (c:ℝ)(hc:0≤ c)(v:c< (P.par.R.L.val:ℝ)) : Tendsto (fun f=> PlethoraJ P f*c^f) atTop (𝓝 0):=by
 let V:=(P.par.R.L.val:ℝ); have p:0<V:= by unfold V; exact_mod_cast P.par.R.L.property
 let a:=c/V; have ha:0≤a:= div_nonneg hc p.le; have hq:a<1:= (div_lt_one p).2 v; let T:=hat P.par.R.L P.par.x; let B:=billX P.par.R.L; let R:ℝ:=ruler P.par.block; have hX:0<R:=by unfold R; exact_mod_cast ruler_gene P.par.block
 let K:=R/2
 have ht:Tendsto (fun f=> K*(T f)*a^f) atTop (𝓝 0):=by
    have he(f:ℕ): K*(T f)*a^f=(K*P.par.x)*a^f+(K*B)*((f:ℝ)*a^f):=by unfold T hat K B; ring
    simp_rw [he]; simpa only [mul_zero,add_zero] using (((tendsto_pow_atTop_nhds_zero_of_lt_one ha hq).const_mul (K*P.par.x)).add ((tendsto_self_mul_const_pow_of_abs_lt_one ((abs_of_nonneg ha).trans_lt hq)).const_mul (K*B)))
 refine squeeze_zero_norm' ?_ ht
 filter_upwards [flowerXJ P] with j v'; change ‖PlethoraJ P j*c^j‖≤ _; rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (PledgeJ P j).le (pow_nonneg hc _))]
 have hu:PlethoraJ P j*c^j= K*WorkWJ P j*a^j:=by unfold PlethoraJ; rw [P.mellow_firm,P.mellow_clock]; rw [Int.cast_mul, Int.cast_natCast]; change 1/(2*V^j)*(R*(WorkWJ P j:ℝ))*c^j=_; unfold K a; rw[div_pow]; ring
 rw[hu]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left v' (div_nonneg hX.le (by norm_num))) (pow_nonneg ha _)
lemma SecondEraJ(P:Spine): Tendsto (PlethoraJ P) atTop (𝓝 0):=by simpa using PetitionJ (P:=P) 1 (zero_le_one) (by exact_mod_cast (show 1<P.par.R.L.val from lt_of_lt_of_le (by norm_num:1<3) P.par.R.coarse))
#print axioms PetitionJ
#print axioms SecondEraJ
#print axioms arumJ
end price
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
