import GaugeFieldConstruction.SportusR
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
variable (P)(m f:ℕ)
private lemma mo_c {x y:ℝ}(p:0≤Real.log (Real.log x))(q:1<x)(g:x≤ y):coos x ≤ coos y:=by rw [show coos x=_ from coin_scale x,show coos y=_ from coin_scale y]; gcongr; exact Real.log_pos q
lemma Sport_rateR : ∀ᶠ f:ℕ in atTop,coos (P.urnMark f)≤ coos (P.urnMark (SportR P m f))∧coos (P.urnMark (SportR P m f))≤SpringR P f^4:=by
 filter_upwards [growthL_R P m, ((Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (turnover P.par))).eventually_ge_atTop (Real.log 2)),(turnover P.par).eventually_gt_atTop 1] with f p q h
 let x:=P.urnMark f; let z:=P.urnMark (SportR P m f); have hx:1<x:=h; have ht:x≤z:=p.1; have q:Real.log 2 ≤Real.log (Real.log x):=q; have hz:0≤ Real.log (Real.log x):=(Real.log_nonneg one_le_two).trans q
 refine ⟨mo_c hz h p.1,?_⟩; apply le_trans (mo_c (hz.trans (Real.log_le_log (Real.log_pos hx) (Real.log_le_log (zero_lt_one.trans hx) ht))) (hx.trans_le ht) p.2)
 change coos (x^2) ≤ _; apply le_trans (b:=coos x^4) _ (pow_le_pow_left₀ (zero_le_one.trans (coos_R _)) (SpringR.low P f) _); rw [show coos (x^2)=_ from coin_scale (x^2),show coos x=_ from coin_scale x, Real.log_pow, Real.log_mul (by norm_num) (Real.log_pos hx).ne',← Real.exp_nat_mul]; push_cast; apply Real.exp_monotone; nlinarith only [q,hz,Real.log_nonneg (show (1:ℝ)≤2 by norm_num)]
abbrev Richm_R (P:Spine)(m f:ℕ):=SpringR P f^(8*m+1)
abbrev deltaR (P:Spine)(f:ℕ):=P.mellow f*SpringR P f
lemma Richm_good : 0< Richm_R P m f:= zero_lt_one.trans_le (one_le_pow₀ (SpringR.tall P f))
lemma deltaR_good :0<deltaR P f:= mul_pos (P.mellow_good _) (zero_lt_one.trans_le (SpringR.tall P f))
lemma Richm_peck : P.mellow (SportR P m f) * Richm_R P m f=deltaR P f:=by
 unfold Richm_R deltaR; rw [pow_succ,← mul_assoc,SpringR, ←pow_mul,show boxNP P f*(8*m)=SportR P m f-f from (by unfold SportR; omega),mellow_age P f (SportR P m f) (SportR.hop ..)]
lemma Richm_lit : Tendsto (Richm_R P m) atTop atTop:= (tendsto_pow_atTop (by omega:8*m+1≠0)).comp (SpringR.escape P)
abbrev CapSum_R (P:Spine)(m:ℕ)(x:ℝ):= (coos x*P.par.R.L.val)^(8*m+1)
lemma cap_SumaR : ∀ᶠ f in atTop, Richm_R P m f≤CapSum_R P m (P.urnMark (SportR P m f)):= (Sport_rateR P m).mono fun _ h=> pow_le_pow_left₀ (zero_le_one.trans (SpringR.tall ..)) ((SpringR.high ..).trans (mul_le_mul_of_nonneg_right h.1 (Nat.cast_nonneg _))) _
lemma costSum_R:∃ s:ℝ,RunRate 0 s (CapSum_R P m):=by
 let V:= (RunRate.coins 0 1 0).muc (P.par.R.L.val:ℝ)|>.pow (8*m+1); rw[zero_mul] at V; exact ⟨_,V⟩
lemma sparkC_R(n:ℕ): ∀ᶠ f:ℕ in atTop,SpringR P f^n≤P.urnMark f:=by
 let V:= (RunRate.coins 0 1 0).muc (P.par.R.L.val:ℝ)|>.pow n; rw[zero_mul] at V; filter_upwards [(turnover P.par).eventually (logPrice 0 _ V (c:=1) (d:=0) (v:=1) (w:=0) (Or.inl zero_lt_one) zero_lt_one),(turnover P.par).eventually_gt_atTop 0] with i h g; rw[one_mul,coinY g] at h; exact (pow_le_pow_left₀ (zero_le_one.trans (SpringR.tall ..)) (SpringR.high ..) n).trans h
abbrev W_PhR (P:Spine)(f:ℕ):ℝ:= (ruler P.par.block:ℤ)*(WorkWJ P f:ℝ)
lemma R_pitch : PlethoraJ P f=P.mellow f* W_PhR P f:=by unfold PlethoraJ; rw [P.mellow_firm,Int.cast_mul,Int.cast_natCast]
lemma R_squeeze(P:Spine)(m:ℕ): ∀ᶠ f in atTop,W_PhR P (SportR P m f)≤ SpringR P f^4:=by
 filter_upwards [(SportR.tale P m).eventually ((turnover P.par).eventually (logPrice 0 0 ((FiatHighJ P).cmul (ruler P.par.block:ℝ)) (c:=0) (d:=1) (w:=0) (v:=1) (Or.inr ⟨rfl,zero_lt_one⟩) zero_lt_one)),Sport_rateR P m] with f H g; rw[one_mul] at H; exact H.trans g.2
lemma R_fit : Tendsto (fun f=>PlethoraJ P f/deltaR P f) atTop (𝓝 0):=by
 apply tendsto_order.mpr; refine ⟨fun y h=>Eventually.of_forall fun i=>h.trans (div_pos (BoonsθJ.PledgeJ P i) (deltaR_good P i)),?_⟩; intro ε e; filter_upwards[(turnover P.par).eventually (logPrice 0 0 ((FiatHighJ P).cmul (ruler P.par.block:ℝ)) (c:=0) (d:=1) (w:=0) (v:=ε/2) (Or.inr ⟨rfl,zero_lt_one⟩) (half_pos e))] with i h
 apply (div_lt_iff₀ (deltaR_good P i)).mpr; rw [R_pitch,deltaR,mul_left_comm ε]; refine mul_lt_mul_of_pos_left ?_ (P.mellow_good _); have hx:W_PhR P i≤ (ε/2)*SpringR P i:=h.trans (mul_le_mul_of_nonneg_left (SpringR.low P i) (half_pos e).le); exact lt_of_le_of_lt hx (mul_lt_mul_of_pos_right (half_lt_self e) (zero_lt_one.trans_le (SpringR.tall P i)))
#print axioms R_fit
#print axioms Sport_rateR
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
