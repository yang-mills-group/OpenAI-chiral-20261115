import GaugeFieldConstruction.LoumBourR
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
local notation "ΤΓ"=> P.run
local notation "Pα"=> P.par
local notation "δα"=> P.par.R.L
open Gleam BProof BProof.PricePort Gleam.Guide Gleam.clocks
-- incomes on any sport track. ensure qF charged fallback
local notation "Τ"=>SpringR P
local notation "Ζ"=>SportR P
local notation "Ξ"=>P.urnMark
local notation "qΓ"=> RankQJ P.par
variable {F A:ℝ}
include p
lemma RailInclR (a:BandS)(f m:ℕ)(v:f0≤ f) : RankQJ P.par f ≤ SpringR P f^(6*m) * RankQJ P.par (SportR P m f):= by
 have he(k:ℕ): RankQJ P.par f≤ 2^k * RankQJ P.par (f+k):=by
    induction k with
    | zero=> simp
    | succ k ih=>
      have hg:= ((p.price f v a (f+k+1)).pass (s:=f+k) (by omega) (by omega)).2; exact ih.trans ((mul_le_mul_of_nonneg_left hg (by positivity : (0:ℝ)≤2^k)).trans_eq (by rw[pow_succ]; simp [add_assoc,mul_assoc])) -- f+k+1 f+(k+1) defeq?
 let L:ℝ:=P.par.R.L.val; have hL:3 ≤ L:=by change 3≤(P.par.R.L.val:ℝ); exact_mod_cast (show (3:ℕ)≤ P.par.R.L.val from P.par.R.coarse)
 let K:=boxNP P f; have hx:(2:ℝ)^8≤ L^6:= le_trans (by norm_num : (2:ℝ)^8 ≤ (3:ℝ)^6) (pow_le_pow_left₀ (by norm_num) hL 6)
 refine (he (K*(8*m))).trans (mul_le_mul_of_nonneg_right ?_ ((p.price f v a _).hot (Nat.le_add_right _ _) le_rfl).le)
 change (2:ℝ)^(K*(8*m)) ≤ (L^K)^(6*m); apply le_trans (b:=(2^8:ℝ)^(K*m)) (le_of_eq (by rw [←pow_mul]; ring_nf)); exact (pow_le_pow_left₀ (by positivity) hx _).trans_eq (by simp_rw [←pow_mul]; ring_nf)
open JetCurry JetCurry.TrekJ
omit p
open Oath.BellPrice
lemma Sport_gainR (P:Spine)(f m:ℕ)(a:BandS) : (ScaleμJ P.par a.val)^(SportR P m f -f) ≤ (SpringR P f^(((3+a.val)*8+7)*m))⁻¹:=by
 let Q:= GapGain P.par.R.L a.val; let L:ℝ:=P.par.R.L.val; have ht:1 ≤ L:=one_le_two.trans (loftL_R ..); have hq:0 ≤L:=zero_le_one.trans ht
 let K:=((3+a.val)*8+7); let w:=boxNP P f
 have hp: L^K≤ Q^8:=by
    let A:ℝ:=3+a.val+(19:ℝ)/20; change _ ≤ (L^A)^8; rw [← Real.rpow_natCast L K, ← Real.rpow_mul_natCast hq] -- lemma tune
    apply Real.rpow_le_rpow_of_exponent_le ht; unfold A K; push_cast; linarith
 change (Q⁻¹:ℝ)^_≤ ((L^w)^(K*m))⁻¹; rw[inv_pow]; apply inv_anti₀ (by positivity : (0:ℝ)<_); have he: SportR P m f -f= 8*(w*m):=by unfold w SportR; rw [Nat.add_sub_cancel_left]; ring
 rw [he,pow_mul Q]; apply le_trans (b:=(L^K)^(w*m)) (by apply le_of_eq; simp_rw[←pow_mul]; ring_nf) (pow_le_pow_left₀ (by positivity) hp _)
variable (m f:ℕ)
open CF.XGarden.MastTin.ArtCart Fock.Flux
lemma incomeR (m:ℕ) (V:Genre): ∀ᶠ f:ℕ in atTop,∀ D:P.Heritor, let S:=SportR P m f; ‖P.FireValue V S (D.β S)‖ ≤ SpringR P f^12:=by
 let W:=RiseP P.par.h 1 V; have hs:RunRate 0 2 W:= RP_K _ V _ -- tune args
 let s:=SportR P m
 have hz:∀ᶠ y:ℝ in atTop,W y ≤ coos y^3:=by
    filter_upwards[logPrice 0 2 hs (c:=0) (d:=3) (v:=1) (w:=0) (Or.inr ⟨rfl,by norm_num⟩) zero_lt_one] with i h
    unfold coos; rw [coin_pow]; norm_num at h ⊢; exact h -- tune
 filter_upwards [(SportR.tale P m).eventually ((turnover P.par).eventually hz),Sport_rateR P m] with f g h D
 intro S; have he: (P.penIt S).threshold= Pressure.temp (P.urnMark S):= (P.run.meter.boot S).1; have hx:= D.crop S
 have hg:= tock_v P.par.h V 1 (P.urnMark S) (D.β S) hx.2 he zero_le_one
 unfold FireValue; rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (V.coin_Bu (P.penIt S) (zero_lt_one.trans_le P.par.height)).le)]; rw[mul_one] at hg
 exact (hg.trans g).trans ((pow_le_pow_left₀ (zero_le_one.trans (coos_R _)) h.2 3).trans_eq (by rw [←pow_mul]))
include p
open BoonsθJ
abbrev TallyInR (D:P.Heritor) (m f n:ℕ)(V:Genre):ℝ:= let X:=SportR P m f
 Richm_R P m f^n * ‖P.FireValue V X (D.β X)‖ / RankQJ P.par X
lemma tallyRate_R (m k d:ℕ)(D:P.Heritor)(V: Genre)(u:BandS)(N:ℝ)(a:0≤N)(e:d≤3+u.val)(b:24+k ≤ m):∀ᶠ f in atTop, let s:=SportR P m f
 TallyInR D m f d V* FlavorRateJ P u f s s N ≤ (SpringR P f^k)⁻¹:=by
 filter_upwards[incomeR (P:=P) m V,eventually_ge_atTop f0,(SpringR.escape P).eventually_ge_atTop (4*N)] with f h s0 f'
 let t:= Τ f; have hx:1 ≤ t:=SpringR.tall _ _; have hz:0<t:=zero_lt_one.trans_le hx
 intro s; have qe:0< qΓ s:= (p.price f s0 u s).hot (SportR.hop ..) le_rfl; have hp:0<qΓ f:= (p.price f s0 u f).hot le_rfl le_rfl
 let R:=‖P.FireValue V s (D.β s)‖; let K:= RankQJ P.par s; have hv:0 ≤R:= norm_nonneg _
 have h0:= RailInclR p u f m s0; let μ:ℝ:=ScaleμJ P.par u.val^(s-f); let W:ℕ:=((3+u.val)*8+7)*m
 let T:= t^W; have hh: T = t^W:=rfl; have hl:0≤ μ:=pow_nonneg (p.price f s0 u s).small _; have hy:μ ≤ T⁻¹:= Sport_gainR P f m u
 let H:ℕ:= (8*m+1)*d; have hg: Richm_R P m f^d=t^H:= (pow_mul ..).symm
 unfold FlavorRateJ; rw [Nat.sub_self,pow_zero,mul_one]; change Richm_R P m f^d * R/K*(4*μ*qΓ f*N) ≤ _; rw[hg]
 calc
    _ ≤ t^H*t^12/K*(4*T⁻¹*(t^(6*m)* K)* N):= by gcongr; exact h D
    _ = t^(H+12+6*m)*(4*N)/T:=by have he:K≠0:=qe.ne'; field_simp; simp_rw [pow_add]; ring
    _ ≤ t^(H+12+6*m+1)/T :=by rw [pow_succ]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left f' (by positivity)) (by positivity)
    _ ≤ (t^k)⁻¹ :=by
       rw [←one_div, div_le_div_iff₀ (by positivity) (by positivity),one_mul, ←pow_add]; refine pow_le_pow_right₀ hx ?_
       have he:u.val <3:=u.isLt
       unfold W H
       have hz:=Nat.mul_le_mul_left (8*m) e; have hx: d ≤ 5:=by omega
       nlinarith only [hz,hx,b]
#print axioms Sport_gainR
#print axioms RailInclR
#print axioms tallyRate_R
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
