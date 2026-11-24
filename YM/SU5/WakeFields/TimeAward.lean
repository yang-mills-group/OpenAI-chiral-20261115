import YM.SU5.WakeFields.LightRoute

/-!
# The cold diploma

Enlargement chosen after election. All displayed bounds eventually, in rung
money. Return the same charter used on these programs. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 500000
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
variable (L:Side) (p u t l:ℕ) (a b f:ℝ→ℝ)
open Furrow
abbrev bump (a:ℝ→ℝ)(l:ℕ)(x:ℝ) := Crawl.costLoss l 10*a x
abbrev wageBorn (L:Side)(p u t l:ℕ)(b f:ℝ→ℝ)(x:ℝ) := wageDay L p u t (bump b l) (fun x=> f x/pinpr L x) 2 x
local notation "pin"=> pinpr L
variable (h: NPL a)(hb:PL b)(hf: PL (fun x=> f x/pinpr L x))
lemma brightW (hb:NPL b)(hf:NPL (fun x=> f x/pinpr L x)): NPL (wageBorn L p u t l b f):= toefoot L p u t (bump b l) (fun x=>f x/pin x) 2 (hb.const_mul _) hf
include h hb hf
theorem april : ∀ᶠ x:ℝ in atTop,0<pinpr L x ∧ ∀ (P:BudgetPoint),P.B=radiusB x→P.power=u→P.order=p→P.supportExponent=1→∃ C, generation P t l |a x| (|b x| *pinpr L x) (f x) (wageBorn L p u t l b f x * pinpr L x) 2 C:=by
 let a' := bump a l; let b':= bump b l; let f':= fun (x:ℝ)=> f x/pin x
 refine (foresight L p t a' b' f' (h.const_mul _) ((PL.const _).mul hb) hf 2).mono fun x ht=>?_ ; obtain ⟨p0,hx⟩:=ht
 refine ⟨p0,fun P B pu pt w=>?_⟩
 obtain ⟨C,γ,b0,uC,g,h,r,l',M⟩:= hx P w pt B
 have hp: careRate C=Py.Rate.LocalLimit.Preparation.rScale P:=by rw [h]; unfold Py.Rate.LocalLimit.Preparation.rScale; rw [B]
 have hh:Crawl.costLoss l (careRate C) ≤ Crawl.costLoss l 10:=by
    have he:1 ≤ (↑(radiusB x) : ℝ):= Nat.one_le_cast.mpr (B ▸ P.B_pos)
    unfold Crawl.costLoss; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_right; · rw [h]; linarith only [(show 8/(radiusB x:ℝ)≤ 8 from div_le_self (by norm_num) he)]
    positivity
 let v:= pinpr L x
 have hμ : f' x*v=f x:= div_mul_cancel₀ _ p0.ne'
 let K:= Crawl.costLoss l (careRate C); let Z:=Crawl.costLoss l 10
 have hη(g:ℝ→ℝ): K* |g x| ≤ |bump g l x|:= (mul_le_mul_of_nonneg_right hh (abs_nonneg _)).trans_eq (by unfold bump Crawl.costLoss; rw [abs_mul, abs_of_pos (Real.exp_pos _)] -- K?? left after trans_eq is Z
    )
 have hs:0 ≤ K:= (Real.exp_pos _).le; have hc:0 ≤ C.d:=by -- unnecessary. remove
    apply le_trans _ M.stiff; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr C.hη.le)) ((mul_nonneg (coastSafe _ _) (abs_nonneg _)).trans M.funds)
 have hd : Mentor C t (K* |a x|) (K*(|b x| *v)) (f x):=by
    have v':= mul_le_mul_of_nonneg_right (hη b) p0.le; rw [mul_assoc] at v'
    refine ⟨M.one,M.shelf,M.stiff,M.hard,M.barrier,mul_nonneg hs (abs_nonneg _),mul_nonneg hs (mul_nonneg (abs_nonneg _) p0.le), (mul_le_mul_of_nonneg_left (hη a) (coastSafe P.B t)).trans M.funds, (mul_le_mul_of_nonneg_left v' (coastSafe P.B t)).trans M.hazard, hμ ▸ M.force, M.deg⟩ -- hμ transp
 refine ⟨C,hd,l',hp,?_,by norm_num,?_,figures L p u t b' f' P C pt pu B b0 uC γ (2:ℝ)⟩
 · rw [show (2:ℝ)=1+1 from by ring, Real.exp_add]; nlinarith only [Real.exp_one_gt_two]
 rw [B]; exact r
end Ledger
end YM.CF.Sour
#print axioms YM.CF.Sour.Ledger.april
