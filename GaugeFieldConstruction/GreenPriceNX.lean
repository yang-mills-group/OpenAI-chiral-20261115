import GaugeFieldConstruction.DockPanelNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
variable (P:Spine){n:ℕ}(A B:BeaconNX n)(i:ℤ)
open RosterJ BoonsθJ XGarden XGarden.MastTin XGarden.MastTin.ArtCart
variable (m:ℕ)(J:ℕ→ℤ)(p:Tendsto (fun i=> (Richm_R P m i)⁻¹*↑(ruler P.calibration.B*J i:ℤ)) atTop (𝓝 (1/2)))
variable {Q: Py.Rate.LocalLimit.Badge}{t:ℕ}{u: TintDemand}(H: LicensedHeight (tagged_B Q) t u P.par)
include H
lemma n6MoneyNX:Tendsto (fun i=> (Richm_R P m i)^6*(2*ClockTurn (P.urnMark (SportR P m i)))) atTop (𝓝 0):=by
 obtain ⟨c,h⟩:=costSum_R P m
 have ht:Tendsto (fun z=>CapSum_R P m z^6*(2*ClockTurn z)) atTop (𝓝 0):= ((h.pow 6).mul ((show RunRate (-callE/16) 0 ClockTurn from RunRate.coins ..).cmul 2)).tends (Or.inl (by norm_num [callE,gratuity])) -- tune
 refine squeeze_zero' (Eventually.of_forall fun i=> mul_nonneg (pow_nonneg (Richm_good ..).le _) (mul_nonneg (by norm_num) (BProof.coin_pos ..).le)) ?_ (ht.comp ((turnover P.par).comp (SportR.tale P m)))
 filter_upwards [cap_SumaR P m] with i v; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Richm_good P m i).le v _) (mul_nonneg (by norm_num) (BProof.coin_pos ..).le)
omit p H
-- center
abbrev ScaleFlagNX (P:Spine)(m i:ℕ):ℂ := (Richm_R P m i:ℂ)^3
abbrev SunPlateNX (P:Spine)(A:BeaconNX n)(m i:ℕ) :P.Test:= CenterBudgetR P (SportR P m i) (P.ScaleFlagNX m i • P.plaqueStakeNX A)
private lemma background_bNX {R:Type*}[Ring R][Algebra ℂ R] (Φ:R→ₗ[ℂ] ℂ) (A B:ℂ)(X Y:R)(u:Φ 1=1):Φ ((A • X-Φ (A • X) • 1)*(B • Y-Φ (B • Y) • 1))= A*B*(Φ (X*Y)-Φ X*Φ Y):=by rw [_root_.mul_sub,_root_.sub_mul,_root_.sub_mul]; simp only[smul_mul_assoc,mul_smul_comm, one_mul,mul_one,map_sub,map_smul,smul_eq_mul,u]; ring
lemma RadialFluxNX (j:ℕ): let a:=P.shifts 3 i (P.SunPlateNX A m j); let b:=P.shifts 3 i (P.SunPlateNX B m j); let t:=SportR P m j
 let X:=P.anteBNX A i; let Y:=P.postNowNX B i; let S:=P.publicBill t
 S (P.reflectTest 3 a * b)=(Richm_R P m j:ℂ)^6*(S (P.sharePageNX [X,Y])-S (P.plaqueStakeNX X)*S (P.plaqueStakeNX Y)):=by
 intro a b t X Y S
 have h(W:BeaconNX n) : P.shifts 3 i (P.SunPlateNX W m j)= P.SunPlateNX (P.postNowNX W i) m j := by unfold SunPlateNX; rw [ShiftBudgetR,map_smul (P.shifts 3 i), practiceBNX]
 let U:=P.plaqueStakeNX X; let V:=P.plaqueStakeNX Y; let F:= EvLB P t; let D:= (Richm_R P m j:ℂ)
 have R:P.reflectTest 3 a= P.SunPlateNX X m j:=by
    unfold a; rw[h A]; unfold SunPlateNX; rw[mirrorBudgetR,P.scale_mirror]; rw [show P.reflectTest 3 (P.plaqueStakeNX (P.postNowNX A i))=U from (congrArg (P.reflectTest 3) (P.practiceBNX A _ i).symm).trans (P.triplePlanNX ..)]
    have ht:Star.star (P.ScaleFlagNX m j)=P.ScaleFlagNX m j := by unfold ScaleFlagNX; rw [star_pow]; simp only [Complex.star_def,Complex.conj_ofReal]
    rw[ht]
 rw [R,show b=P.SunPlateNX Y m j from h _]
 have hp:P.sharePageNX [X,Y]= U*V:=congrArg (U*·) (mul_one V); rw [hp]
 change F ((D^3 • U-F (D^3 • U) • 1)*(D^3 • V-F (D^3 • V) • 1))= D^6*(F (U*V)-F U*F V)
 exact (background_bNX F _ _ _ _ (unitB_R ..)).trans (congrArg (fun y:ℂ=> y *(F (U*V)-F U*F V)) (pow_add D 3 3).symm)

include p H
lemma Paid_2NX : Tendsto (fun i=> (Richm_R P m i:ℂ)^6*(P.publicBill (SportR P m i) (P.sharePageNX [P.anteBNX A (J i),P.postNowNX B (J i)])- quadP_NX (P.anteBNX A (J i)) (P.postNowNX B (J i)) κF)) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 obtain ⟨s,C,z,v⟩:= P.marsLineNX A B m J p
 apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) _ (P.n6MoneyNX m H)
 filter_upwards [v,(SportR.tale P m).eventually (P.confirmCallNX n 2 Q t u H C z)] with i v Z; obtain ⟨w,e,y,k,j,X,Y,s,E,B'⟩:=v
 rw [norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg (Richm_good ..).le]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Richm_good ..).le _)
 let X':=P.anteBNX A (J i); let Y':= P.postNowNX B (J i)
 exact Z [X',Y'] w y (cartO 0 k) 3 j (by simp) (fun i hx=>by simp only[List.mem_cons,List.not_mem_nil,or_false] at hx; cases hx with|inl p=>exact p.symm ▸ X| inr p=>exact p.symm ▸ Y) e s E B' _ (P.publicH 3) _ (P.sampleTwoNX ..)
omit p
lemma Paid_1NX : Tendsto (fun i=> (Richm_R P m i:ℂ)^6 * (P.publicBill (SportR P m i) (P.plaqueStakeNX A)- quoteP_NX A κF)) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; obtain ⟨C,v⟩:=P.evergreenNX A.1.patio 3
 apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) _ (P.n6MoneyNX m H); filter_upwards [(SportR.tale P m).eventually (P.confirmCallNX n 1 Q t u H (fun _=> C) (RunRate.const _))] with i Z
 obtain ⟨w,r,S,j,Y,e,s,E,B'⟩:=v i
 have h:=Z [A] w r S 3 j (by simp) (fun i h=> List.mem_singleton.mp h|> fun e=> e.symm ▸ Y) e s E B' _ (P.publicH 3) _ (P.sampleOneNX ..)
 unfold sharePageNX at h; rw [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at h
 rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Richm_good ..).le]
 exact mul_le_mul_of_nonneg_left h (pow_nonneg (Richm_good ..).le _)
omit H in
lemma PublicEraCNX (F:P.Test)(t:ℕ) (x:Axis) : P.publicBill t (P.reflectTest x F)= Star.star (P.publicBill t F):=P.EraH x 0 t _
lemma MirrorQuoteNX : quoteP_NX (P.anteBNX A i) κF = Star.star (quoteP_NX A κF) ∧ quoteP_NX (P.postNowNX A i) κF=quoteP_NX A κF:=by
 let U:= P.evergreenOneNX (n:=n) H 3 _ (P.publicH 3); let Q:= U A
 constructor
 · refine tendsto_nhds_unique (U (P.anteBNX A i)) ((Q.star).congr fun j=>?_) ; change Star.star (P.publicBill j (P.plaqueStakeNX A))=P.publicBill j _
   rw [←P.triplePlanNX,show P.publicBill j (P.reflectTest 3 _)=_ from P.PublicEraCNX (P.shifts 3 i (P.plaqueStakeNX A)) j 3, CruiseFR] -- tune
 refine tendsto_nhds_unique (U (P.postNowNX A i)) (Q.congr fun j=>?_); exact ((congrArg (P.publicBill j) (P.practiceBNX A 3 i).symm).trans (CruiseFR ..)).symm
include p
lemma PadWinnerNX : Tendsto (fun i=> let X:=P.shifts 3 (J i) (P.SunPlateNX A m i); let Y:=P.shifts 3 (J i) (P.SunPlateNX B m i); P.publicBill (SportR P m i) (P.reflectTest 3 X * Y)) atTop (𝓝 (ArmΔScanNX A B)):=by
 let G(i:ℕ):ℝ:=(Richm_R P m i)⁻¹; let f(i:ℕ):=SportR P m i; let X i:= P.anteBNX A (J i); let Y i:= P.postNowNX B (J i); let F i:= CnPadNX (X i) (Y i)
 have W:=P.QuintAxisNX A B (f:=G) (tendsto_inv_atTop_zero.comp (Richm_lit ..)) (Eventually.of_forall fun i=> inv_pos.mpr (Richm_good ..)) J p
 let a:=quoteP_NX A κF; let b:= quoteP_NX B κF
 have E:= (P.Paid_1NX A m H).star.mul ((P.evergreenOneNX H 3 _ (P.publicH 3) B).comp (SportR.tale P m)) -- Δ * true B
 have O:= (((W.add (P.Paid_2NX A B m J p H)).sub E).sub ((P.Paid_1NX B m H).const_mul (star a)))
 rw [add_zero,star_zero,zero_mul,sub_zero,mul_zero,sub_zero] at O
 apply O.congr; intro i; rw [RadialFluxNX]
 let c:=(Richm_R P m i:ℂ)
 change F i/(G i:ℂ)^6+c^6*_ - Star.star (c^6* (P.publicBill (f i) _-a))*_ - Star.star a*_ = c^6*(P.publicBill (f i) (P.sharePageNX [X i,Y i])-P.publicBill _ (P.plaqueStakeNX (X i))*P.publicBill _ (P.plaqueStakeNX (Y i)))
 unfold F X Y CnPadNX; rw [show (G i:ℂ)=c⁻¹ from Complex.ofReal_inv _,inv_pow,div_eq_mul_inv,inv_inv,(P.MirrorQuoteNX A (J i) H).1,(P.MirrorQuoteNX B (J i) H).2, ←triplePlanNX, P.PublicEraCNX,CruiseFR]; let W:= P.publicBill (f i); rw[show P.plaqueStakeNX (P.postNowNX B (J i))= P.shifts 3 (J i) (P.plaqueStakeNX B) from (P.practiceBNX ..).symm,CruiseFR]; simp only [star_mul, star_pow, show Star.star c=c from Complex.conj_ofReal _,star_sub] -- tune congr
 unfold c a f; rw [Function.comp_apply]; ring
#print axioms PadWinnerNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
