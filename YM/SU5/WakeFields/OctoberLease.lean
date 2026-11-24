import YM.SU5.WakeFields.TellerMint
import YM.SU5.WakeFields.AnchorPrice
import YM.SU5.Exchange.Pace.Moon

/-!
# Generating support budget clocks with small bandwidth.

Two cases of costing at election: (NPL full, birth and current-Force at Q times PL),
and the yet better NPL variant in those latter two costs. We generate the very same clocks;
then one can use the improvement in any occurrence budgets requiring it. This file makes
the clocks; the next prices the receipts against those two levels of purchase. -/
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
variable (L:Side) (p t:ℕ) (a b k:ℝ→ℝ)
lemma plume (f:ℝ→ℝ)(p:Chill_v f) : BPress.NPL f := ⟨fun i=>p i⟩
lemma plAbs {a:ℝ→ℝ}(p: BPress.PL a) : PL fun x=>|a x| := p.mono (Eventually.of_forall fun _=>Eq.le (abs_abs ..))
lemma nplAbs {a:ℝ→ℝ}(p : BPress.NPL a) : NPL fun x=>|a x|:= p.mono (Eventually.of_forall fun _=> Eq.le (abs_abs ..))
local notation "lB"=> radiusB
local notation "sB"=> Sour.spanV
local notation "χφ"=> chi_f
abbrev riseFee (L:Side)(p t:ℕ)(b k:ℝ→ℝ)(x:ℝ) : ℝ := pinpr L x + chi_f p*|k x| + 8*(lB x:ℝ)*(coastU (lB x) t*|b x|)
abbrev fountain (L:Side) (p t:ℕ)(b k:ℝ→ℝ)(x:ℝ) : ℝ:= riseFee L p t b k x * pinpr L x
local notation "Q"=> pinpr L
local notation "ν"=> riseFee L p t b k
local notation "γ"=> fountain L p t b k
abbrev beltSpeed (t:ℕ)(a:ℝ→ℝ)(x:ℝ) := coastU (lB x) t * |a x|
local notation "Jν"=> beltSpeed t a
variable (ha:BPress.NPL a)(hb:BPress.PL b)(hk:BPress.PL k)
lemma plCoast : PL (fun x=> coastU (lB x) t) := by
 unfold coastU taxIns; push_cast; exact ((PL.const _).mul ((PL.const _).mul (((PL.const 4).mul PL_radiusX).pow 10))).mul (PL.const _)
include hb hk
lemma risePL : PL (ν) := by
 let v:= ((PL.const 8).mul PL_radiusX); exact (((nq L).pl.add ((PL.const _).mul (plAbs hk))).add (v.mul ((plCoast t).mul (plAbs hb))))
omit hb hk
lemma riseNPL (hb:NPL b)(hk:NPL k) : NPL (ν) := by
 let v:= ((PL.const 8).mul PL_radiusX); exact (((nq L).add ((PL.const _).times (nplAbs hk))).add (v.times ((plCoast t).times (nplAbs hb))))
include ha
lemma nplBelt : NPL (Jν):=(plCoast _).times (nplAbs ha)
omit ha
include hb hk
lemma nplFountain : NPL (γ) := (risePL L p t b k hb hk).times (nq L)
include ha
lemma foresight (y:ℝ) : ∀ᶠ x:ℝ in atTop, 0 < Q x ∧ ∀ P:BudgetPoint, P.supportExponent=1 → P.order=p→ P.B=lB x→∃ C: Occlus P, C.γ=fountain L p t b k x ∧ C.κ=1 ∧ C.η= discount (lB x) ∧ C.uΓ=P.supportExponent + 5*C.η ∧ careRate C=1+8/(lB x:ℝ) ∧
    9*y*t ≤ C.η*(lB x:ℝ)^2 ∧ C.uΓ ≤ P.supportExponent+(1:ℝ)/2 ∧
    Mentor C t |a x| (|b x| *pinpr L x) (k x*pinpr L x) := by
 let r(x:ℝ):ℝ:=lB x; let S(x):=sB (lB x); let U:= nplFountain L p t b k hb hk
 have hR:Tendsto r atTop atTop:=tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
 have hV:NPL (fun x=>γ x*S x*r x):=(U.mul PL_spanV).mul PL_radiusX
 have hS':NPL (fun x=>S x*Jν x*r x*r x):=((PL_spanV.times (nplBelt t a ha)).mul PL_radiusX).mul PL_radiusX
 filter_upwards [hR.eventually_ge_atTop (9*y*t), hR.eventually_ge_atTop (20:ℝ), draft_π L,
    U.drop.eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
    hV.drop.eventually (ge_mem_nhds (show (0:ℝ)<1/1000 by norm_num)),
    hS'.drop.eventually (ge_mem_nhds (show (0:ℝ)<1/8 by norm_num))] with x hz ht vg uv hw hf
 let B:= lB x; let R:= r x; let W:= γ x; let Y:= S x; let I:= discount B; let Z:= Q x
 have xZ:0 < Z:= pow_pos vg.2.1 _; have hY:0 ≤ Y:= Nat.cast_nonneg _; have h20:R≥20:=ht; have hR:0< R:=by linarith only [h20]
 have h1:I=R⁻¹:=rfl; have hI:0<I:=inv_pos.mpr hR; have hz':W ≤ 1/4:=uv; let aF:=Jν x; let aB:=coastU B t*(|b x| *Z); let vF:=Y*R*aF
 have hv: W= Z^2+chi_f p*|k x| *Z+8*(R*aB):=by unfold W fountain riseFee aB Z R r B; ring
 have H:0≤aB:= mul_nonneg (coastSafe _ _) (mul_nonneg (abs_nonneg _) xZ.le); have eT:0≤aF:=mul_nonneg (coastSafe _ _) (abs_nonneg _); have haF:0≤vF:=mul_nonneg (mul_nonneg hY hR.le) eT
 have hμ: chi_f p*|k x| ≥ 0:=mul_nonneg (spicy_f _) (abs_nonneg _)
 have he: 0 <W:=by rw [hv]; positivity
 have heR:W*Y*R ≤1/1000 :=hw
 have heJ:Y*aF*R*R ≤ 1/8:=hf
 have hD(Y:ℝ): degreePrice (lB x) Y I=4*(sB (lB x)*Y*R):=by rw [degreePrice,stretch,div_eq_mul_inv,h1, inv_inv]; rfl
 have hd: degreePrice B W I ≤ 1/2 := by
    rw [hD]; unfold B at *; change 4*(Y*W*R)≤ _; linarith only [heR]
 have hσ : (1-degreePrice B W I)⁻¹ ≤ 2:=by apply inv_le_of_inv_le₀ (by norm_num); linarith only [hd]
 refine ⟨xZ,fun P hp hq Lx=>?_⟩
 let θ:=P.supportExponent+5*I
 let C' : Occlus P := {
    κ:=1,«γ»:=W,uΓ:=θ, w:=I,c:=aF,e:=aB,d:=vF,η:=I,hγ:=he,hη:=hI,
    hw:=by unfold θ; linarith,
    degree:= by rw [Lx,hD]; change 4*(Y*(100*W)*R) ≤1/2; linarith only [heR],
    degree0:= Lx.symm ▸ (show degreePrice B W I< 1 from lt_of_le_of_lt hd (by norm_num)),
    still:=by rw [Lx]; apply le_trans (mul_le_mul_of_nonneg_left hσ he.le); linarith only [hz'],
    covers:=by rw [Lx]; have ht:(0:ℝ)≤Real.exp 1:= (Real.exp_pos _).le; have hv:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσ he.le) ht; have hz:=mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le he.le; linarith only [he,hv,hz] }
 refine ⟨C',rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
 · unfold careRate C' θ; dsimp only; change _+_+_+_=(1:ℝ)+8/R; simp only [Lx, hp,div_eq_mul_inv]; change (1:ℝ)+5*I+I+I+I=1+8*I; ring -- tune
 · apply le_trans hz; change R≤ I*R^2; rw [h1]; exact le_of_eq (by field_simp)
 · have ht:R⁻¹ ≤ 1/20:=by exact (inv_anti₀ (by norm_num) h20).trans_eq (by norm_num)
   change _+5*I≤ _; rw [h1]; linarith only [ht]
 have y: Y*aF*R ≤ Y*aF*R*R:= le_mul_of_one_le_right (mul_nonneg (mul_nonneg hY eT) hR.le) (by linarith only [h20])
 let B':= sB P.B; have hx:B'=Y:=by unfold B'; rw [Lx]
 have xH:vF ≤ I/8:=by apply le_of_mul_le_mul_right _ (show 0<R from hR); rw [h1]; rw [show R⁻¹ /8*R=1/8 from (by field_simp)]; unfold vF; linarith only [heJ]
 have hC:Y*aF ≤ I/8:= by apply le_of_mul_le_mul_right _ hR; rw [h1, show R⁻¹/8*R=1/8 from (by field_simp)]; exact y.trans heJ
 refine ⟨rfl,?_,?_,?_,?_,abs_nonneg _,mul_nonneg (abs_nonneg _) xZ.le,?_,?_,?_,?_⟩
 · change W*B'≤I; rw [hx,h1, ←one_div]; apply (le_div_iff₀ hR).mpr; exact le_trans heR (by norm_num)
 · change B'* I⁻¹*aF ≤ vF; rw [hx,h1,inv_inv]
 · change B'*aF≤ I; rw [hx]; linarith only [hC,hI]
 · change aB+vF*W - (I-B'*aF)*W<0; rw [hx]; have hU:8*aB ≤ W*I:=by rw [h1,← div_eq_mul_inv]; apply (le_div_iff₀ hR).mpr; rw [hv]; nlinarith only [mul_nonneg hμ xZ.le,sq_nonneg Z]; -- note semicolon
   nlinarith only [hU,mul_pos hI he,mul_le_mul_of_nonneg_right xH he.le,mul_le_mul_of_nonneg_right hC he.le]
 · change coastU P.B t*_ ≤ aF; rw [Lx]
 · change coastU P.B t*_ ≤ aB; rw [Lx]
 · rw [hq]; apply lt_of_le_of_lt (b:=chi_f p*|k x| *Z)
   · change χφ p * (_*Z) ≤ _; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (spicy_f _)) xZ.le
   change _< W; rw [hv]; nlinarith only [pow_pos xZ 2, mul_nonneg hR.le H]
 rw [Lx]; unfold R r at h20; exact_mod_cast (show 3≤ (↑(lB x):ℝ) from le_trans (by norm_num : (3:ℝ)≤20) h20)
end Ledger
end YM.CF.Sour
#print axioms YM.CF.Sour.Ledger.foresight
