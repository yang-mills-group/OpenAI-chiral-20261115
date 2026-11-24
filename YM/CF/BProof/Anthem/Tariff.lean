import YM.CF.BProof.Anthem.Score
/-! Quantified cost; bands tile support with 3 imaginary ext costs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Anthem.Score
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular
open Vault Paige Drapes Moment RG Wilson
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side} {I:Type}[Fintype I]{Y:Yard (More N)}(Q:Score Y I)(i:Y.Index)
variable (x:Pane N)(b:Eyes (More N)){A B C:ℝ}
lemma inn_card : (inn Y i).card ≤ (Y.band i).card:= card_le_card_of_injOn node (fun j p=> (mem_filter.mp (mem_coe.mp p)).2) Tenant.needle.injOn
def capP (l:ℕ)(A B C:ℝ):= (C+B+(l+1)*A)+(l+1)*Real.log sitePrice -- l implicit Nat cast ensure
abbrev capS(l:ℕ)(A B C:ℝ):=2*Real.log 5+ capP l A B C
def slotFee (l s:ℕ)(A B C:ℝ):= Real.exp (capS l A B C*(s:ℝ)^3)
variable (h:Budget Q A B C)
include h
lemma tPrice : ‖(Q.t i x b:ℂ)‖≤ Real.exp (C*(((More N).val:ℝ)^3)):= (by rw [Complex.norm_real,Real.norm_of_nonneg (show 0≤Q.t i x b from (Y.toll_pay i Q.y Q.S x _ h.xi).1)]; exact h.ang i x _)
lemma maks : ‖Q.mask i x b‖≤ (Y.long+1)*A*(((More N).val:ℝ)^3):= by
 obtain ⟨ρ,e,w⟩:=h.rho; apply (Q.M.limit Y i Q.r w e _).trans; rw [show (Y.band i).card=(Y.long+1)*(More N).val^3 from strip_card _ (Y.long_lt.trans Y.count_lt)]; push_cast; apply le_of_eq; ring
lemma amtCost : ‖Q.amt i x b‖≤ Real.exp ((C+B+(Y.long+1)*A)*(((More N).val:ℝ)^3)):=by
 have hz: (↑(Q.gaugeCharge i x)-Q.mask i x b).re ≤(B+(Y.long+1)*A)*(((More N).val:ℝ)^3):=by
    rw [Complex.sub_re,Complex.ofReal_re]; have hv:= Complex.abs_re_le_norm (Q.mask i x b); have ht:= (le_abs_self (Q.gaugeCharge i x)).trans (h.costG i x); have hi:= Q.maks i x b h; have hp:= neg_le_of_abs_le hv; nlinarith only [ht,hi,hp]
 rw [amt,norm_mul,add_assoc,add_mul,Real.exp_add]; exact mul_le_mul (Q.tPrice i x b h) ((Complex.norm_exp ..).trans_le (Real.exp_monotone hz)) (norm_nonneg _) (Real.exp_pos _).le
lemma partPrice : ‖Q.partOp i x b‖≤ Real.exp (capP Y.long A B C*(((More N).val:ℝ)^3)):=by
 rw [partOp,norm_smul,capP,add_mul,Real.exp_add]; apply mul_le_mul (Q.amtCost i x b h) _ (norm_nonneg _) (Real.exp_pos _).le; apply (Madd_money (Q.H_seal i x b) (inn Y i)).trans; apply (pow_le_pow_right₀ sitePrice_p (inn_card i)).trans_eq; rw [show (Y.band i).card=(Y.long+1)*(More N).val^3 from strip_card _ (Y.long_lt.trans Y.count_lt)]; rw [show _*Real.log sitePrice*(((More N).val:ℝ)^3)= ↑((Y.long+1)*(More N).val^3:ℕ)*Real.log sitePrice from (by push_cast; ring),Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le sitePrice_p)]; -- tune
omit h in
lemma named_count : ((Q.named i x).card:ℝ) ≤ Real.exp (2*Real.log 5*(((More N).val:ℝ)^3)):=by
 apply (Nat.cast_le.mpr (card_le_univ ..)).trans_eq; simp only [Angular.Signs,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool, Fintype.card_fin, Per, ZMod.card]; rw [show 2*Real.log 5*(((More N).val:ℝ)^3)=↑(2*(More N).val^3:ℕ)*Real.log 5 from (by push_cast; ring),Real.exp_nat_mul]; rw [Real.exp_log (by norm_num)]; push_cast; try rfl
lemma scope_pay : ‖Q.slot i x‖≤ slotFee Y.long (More N).val A B C:= by
 apply (norm_sum_le ..).trans; apply (sum_le_sum (fun j _=>Q.partPrice i x (Q.basisLabel i x j) h)).trans; rw [sum_const,nsmul_eq_mul,slotFee,capS,add_mul,Real.exp_add]; exact mul_le_mul_of_nonneg_right (named_count ..) (Real.exp_pos _).le
local instance (I : Type)[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _
local instance (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
lemma allowed : Allowed (Y.band i) (Q.slot i):=⟨⟨Q.slot_m i h, slotFee Y.long (More N).val A B C, fun x=> Q.scope_pay i x h⟩,Q.slot_read i h,Q.slot_modes i⟩
lemma part_env : RG.Envelope (uncurry (Q.partOp i)):= ⟨Q.partOp_m i h, Real.exp (capP Y.long A B C*(((More N).val:ℝ)^3)), fun u=> Q.partPrice i u.1 u.2 h⟩
lemma amt_env : RG.Envelope (uncurry (Q.amt i)):= ⟨Q.tapeMeas i h, _,fun u=> Q.amtCost i u.1 u.2 h⟩
end YM.CF.BProof.Anthem.Score
