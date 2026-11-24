import YM.SU5.WakeFields.OctoberLease

/-!
# Figures for giving Key cashflow from Mentor, explicit clocks
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 540000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
namespace YM.CF.Sour
open Function Filter NormedSpace Lattice Wilson RG Mew Ione
open Push.AbsoluteSums Trees MeasureTheory Finset Cadre Vow Vow.TreasuryFog
open Pressure BPress Py Esti
open scoped Topology ContDiff BigOperators Classical YM.CF.Mew
namespace Ledger
variable (L:Side) (p u t:ℕ) (b k:ℝ→ℝ)
open Nor Furrow
abbrev coinDay (B:ℕ)(p u:ℕ) : ℝ := reserveT u p B (discount B)
lemma smallPL : PL fun x=> coinDay (radiusB x) p u := by
 let α(x:ℝ):ℝ:= stilK (radiusB x)^u; have hα: PL α:= (((PL.const 5).mul (PL_radiusX.add (PL.const 1))).pow u)
 let E : ℝ→ℝ:= fun x=> Real.exp (discount (radiusB x))
 have hz: PL E := (PL.const (Real.exp 1)).mono (Eventually.of_forall fun i=> by
    change |Real.exp (discount (radiusB i))| ≤ |Real.exp 1|; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    cases h:radiusB i with
    |zero=> simp [discount]
    |succ n=> exact (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (by omega)))) -- tune
 unfold coinDay reserveT coin_n; simp_rw [discount,inv_inv]; exact ((hα.mul ((PL.const _).mul (((PL.const _).mul hα).pow p))).mul (((PL_radiusX.pow _).mul (PL.const _)).mul hz))

-- Majorants. Multiplying by the shifted g^2 at the stencil resolution.
abbrev tether (L:Side) (p u t:ℕ) (b k:ℝ→ℝ) (x:ℝ) : ℝ := coinDay (radiusB x) p u * (200*riseFee L p t b k x)
abbrev capAnchor (L:Side)(p u t:ℕ)(b k:ℝ→ℝ)(x:ℝ):ℝ:= (spanV (radiusB x)*(radiusB x:ℝ))* tether L p u t b k x
local notation "ηΩ"=> tether L p u t b k
local notation "cΩ"=> capAnchor L p u t b k
local notation "pin"=> pinpr L
local notation "Ob"=> lscale
abbrev wageDay (L:Side)(p u t:ℕ)(b k:ℝ→ℝ)(y x:ℝ) : ℝ:= (1+(2:ℝ)*t)*capAnchor L p u t b k x+(1+2*Real.exp (y*t))*tether L p u t b k x
lemma toehold (y:ℝ)(hb:PL b)(hk:PL k): PL (wageDay L p u t b k y):=
 let h:= (smallPL p u).mul ((PL.const _).mul (risePL L p t b k hb hk))
 ((PL.const _).mul ((PL_spanV.mul PL_radiusX).mul h)).add ((PL.const _).mul h)
lemma toefoot (y:ℝ)(hb:NPL b)(hk:NPL k): NPL (wageDay L p u t b k y):=
 let h:= (smallPL p u).times ((PL.const _).times (riseNPL L p t b k hb hk))
 ((PL.const _).times ((PL_spanV.mul PL_radiusX).times h)).add ((PL.const _).times h)
variable {x:ℝ}
private lemma inversePay {P:BudgetPoint}(C:Occlus P) : (1-degreePrice P.B C.γ C.η)⁻¹ ≤2:=by
 have hd := C.degree; have hp:0 ≤ (Animals.ballCost P.B:ℝ):=Nat.cast_nonneg _
 have he: C.γ ≤ 100*C.γ:=by linarith only [C.hγ]
 have hx:degreePrice P.B C.γ C.η≤1/2:= by
    refine le_trans (b:=degreePrice P.B (100*C.γ) C.η) ?_ hd; unfold degreePrice stretch; have hv:=C.hη; gcongr
 apply inv_le_of_inv_le₀ (by norm_num); linarith only [hx]
private lemma earn_xy {P:BudgetPoint}(C:Occlus P) (hp : P.order=p)(hu : P.power=u)(hr : P.B=radiusB x)(b0:C.κ=1)(uC:C.η= discount (radiusB x))(g:C.γ=fountain L p t b k x) :
    0 ≤ yσE P C ∧ 0 ≤ yσF P C ∧ yσE P C≤ ηΩ x* pin x ∧ yσF P C= ηΩ x*pin x ∧ payAnchor P C ≤ cΩ x*pin x := by
 let Y:= ηΩ x*pin x; have H:0 ≤ reserveT P.power P.order P.B C.η := by unfold reserveT coin_n stilK; have ht:= C.hη; positivity
 have h : Y = reserveT P.power P.order P.B C.η*(200*C.γ):=by rw [hu,hp,hr,uC,g]; unfold fountain Y tether coinDay; ring
 have he:= inversePay C; have ht:0 ≤ C.γ:= C.hγ.le; have hx : yσE P C ≤ Y:= by rw [h]; apply mul_le_mul_of_nonneg_left _ H; linarith only [mul_le_mul_of_nonneg_left he ht,ht]
 have hv : yσF P C= Y := by rw [h,yσF,b0,inv_one,one_mul,mul_comm C.γ]
 refine ⟨mul_nonneg H (mul_nonneg ht (inv_nonneg.mpr (sub_nonneg.mpr C.degree0.le))),hv.symm ▸ (h.symm ▸ mul_nonneg H (mul_nonneg (by norm_num) ht)),hx,hv,?_⟩ -- shim
 unfold payAnchor capAnchor; apply le_trans (mul_le_mul_of_nonneg_left hx (show 0≤ spanV P.B*C.η⁻¹ from mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr C.hη.le))); apply le_of_eq; unfold Y; rw [hr,uC,discount,inv_inv, ← mul_assoc (_ * _ : ℝ)] -- tune

-- Witness comparison & caps.Fee.calendar, ready for occupancy with exactly P's appointment.
lemma figures (P: BudgetPoint)(C:Occlus P) (hp : P.order=p)(hu : P.power=u)(hr : P.B=radiusB x)(b0:C.κ=1)(uC:C.η= discount (radiusB x))(g:C.γ=fountain L p t b k x)(y:ℝ) :
    payAnchor P C ≤ wageDay L p u t b k y x * pinpr L x ∧
    (2*payAnchor P C*t + sigma (C.η+C.η) P.B*yσE P C) ≤ wageDay L p u t b k y x * pinpr L x ∧
    Real.exp (y*t)*(yσF P C+yσF P C)≤ wageDay L p u t b k y x * pinpr L x := by
 obtain ⟨h1,h2,hE,hF,hQ⟩:= earn_xy L p u t b k C hp hu hr b0 uC g
 let Z:=pinpr L x; let A:=payAnchor P C; let Y:= Real.exp (y*t); have y0:0 ≤ A:=mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr C.hη.le)) h1; have ht:0≤ Y:= (Real.exp_pos _).le
 have hx : wageDay L p u t b k y x*Z=(1+2*t)*(cΩ x*Z)+(1+2*Y)*(yσF P C):=by unfold wageDay; rw [hF]; unfold capAnchor Z Y; ring -- cap stuff
 rw [show wageDay L p u t b k y x*pinpr L x=_ from hx]
 have hA:= mul_le_mul_of_nonneg_left hQ (show (0:ℝ) ≤ 1+2*t by positivity)
 have hB: yσE P C ≤ yσF P C:= hE.trans_eq hF.symm; have hz: sigma (C.η+C.η) P.B ≤ 1:=Real.exp_le_one_iff.mpr (by have hp:= C.hη; apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by norm_num))
 unfold Z at *; unfold A at *
 constructor
 · nlinarith only [hA,h2,mul_nonneg (Nat.cast_nonneg (α:=ℝ) t) y0,mul_nonneg ht h2] -- cap
 constructor
 · nlinarith only [hA, mul_le_mul_of_nonneg_right hz h1,hB, y0, mul_nonneg ht h2]
 nlinarith only [h2,hA,y0,mul_nonneg y0 (Nat.cast_nonneg (α:=ℝ) t)]
end Ledger
end YM.CF.Sour
#print axioms YM.CF.Sour.Ledger.toehold
#print axioms YM.CF.Sour.Ledger.toefoot
#print axioms YM.CF.Sour.Ledger.figures
