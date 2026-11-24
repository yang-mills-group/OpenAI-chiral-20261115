import YM.CF.BProof.Oasis.Launch
/-! before comparison y; parameters ε_j paid on future trajectories. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums Civic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
lemma coverC_p(B:ℕ):1 ≤ (coverC B:ℝ):=by unfold coverC; push_cast; norm_num; nlinarith [show (1:ℝ) ≤ ((B:ℝ)+B+1)^4 from one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) B])]
lemma coverC_m: Monotone coverC:= by intro i j h; unfold coverC; gcongr
lemma coverBill{B:ℝ→ℕ}(p:PL (fun y=>(B y:ℝ))):PL (fun y=> (coverC (B y):ℝ)):=by unfold coverC; push_cast; exact ((((p.add p).add (PL.const _)).pow 4).mul (PL.const _))
lemma ageMono {v v':ℝ}(p:v≤v')(q:0≤v'){B Z:ℕ}(u:B≤Z): Cargo.roomAge B v ≤ Cargo.roomAge Z v':=by
 unfold Cargo.roomAge payV; apply mul_le_mul_of_nonneg_right _ puffPrice_p; have hv: (1:ℝ)+coverC B ≤1+ coverC Z:=add_le_add_right (Nat.cast_le.mpr (coverC_m u)) _; exact mul_le_mul p (pow_le_pow_left₀ (by positivity) hv 4) (by positivity) q
lemma ageP{v:ℝ}(p:0≤v)(B:ℕ):0≤Cargo.roomAge B v:=mul_nonneg (mul_nonneg p (by positivity)) puffPrice_p
lemma ageN (B:ℝ→ℕ)(v:ℝ→ℝ)(h:PL (fun y=>(B y:ℝ)))(u:NPL v) : NPL (fun y=>Cargo.roomAge (B y) (v y)):= (u.mulp ((PL.const _|>.add (coverBill h)).pow 4)).mulp (PL.const _)
abbrev rack(p:Pay):ℝ:=2+2/p.rate
def feeα (B:ℝ→ℕ)(p:Pay)(y:ℝ):= (rack p * coverC (B y))⁻¹
theorem α_bill {B:ℝ→ℕ}(p:Pay)(h:PL (fun y=>(B y:ℝ))): PL (fun y=>(feeα B p y)⁻¹):=by unfold feeα; simp_rw [inv_inv]; exact (PL.const _).mul (coverBill h)
def feeVal (B:ℝ→ℕ)(p:Pay)(T:ℝ→ℝ)(y:ℝ):= puffPrice (p.rate/2)* mainW (B y) (coins p) (BProof.g y) (T y) + BProof.g y
lemma fees {B:ℝ→ℕ}(p:Pay)(h:PL (fun y=>(B y:ℝ))){T:ℝ→ℝ}(v:NPL T): NPL (feeVal B p T):=by
 have ht:NPL BProof.g:=coin_n (by norm_num: (-1/2:ℝ)<0 ∨ (-1/2:ℝ)=0 ∧ (0:ℝ)<0) 0; exact ((PL.const _|>.muln (((ht.mulp (PL.const _)).mulp (PL.const _)).add ((ageN B _ h (v.add v)).add (ageN B _ h v)))).add ht)
lemma ratesT(B:ℝ→ℕ)(p:Pay)(y:ℝ): let a:=feeα B p y; 0<a ∧ a ≤ p.rate/2∧ a ≤ 1∧ a*coverC (B y) ≤1/2:=by
 intro a; have h:=coverC_p (B y); have hp:=p.charge; unfold a feeα rack; set t:ℝ:= 2+2/p.rate with ht; set c:ℝ:= ↑(coverC (B y)); change 1≤c at h; have hc:=zero_lt_one.trans_le h; have hv:t≥2:=by unfold t; simp; positivity
 have hw:0<t:=zero_lt_two.trans_le hv; refine ⟨inv_pos.mpr (mul_pos hw hc),?_,?_,?_⟩; · have hd:=mul_le_mul_of_nonneg_left h hw.le; field_simp at ht ⊢; nlinarith [mul_nonneg hp.le (show 0≤ t*c-t by nlinarith)]
 · exact inv_le_one_of_one_le₀ (by nlinarith)
 field_simp; linarith
lemma law_fee {B:ℝ→ℕ}(p:Pay)(h:PL (fun y=>(B y:ℝ))){T:ℝ→ℝ}(v:NPL T)(k:ℝ)(x:coins p≤k): ∀ᶠ y:ℝ in atTop,∀ {N:Side}{D:GramM N}(s:ℝ),0≤ s→s≤T y→D.p.supportExponent=1→D.p.B ≤ B y→ Tube D p k (BProof.g y) s (feeα B p y) (feeVal B p T y):=by
 have he:NPL (fun y=> 64*feeVal B p T y *(feeα B p y)⁻¹):=((PL.const 64|>.muln (fees p h v)).mulp (α_bill p h)); filter_upwards [he.limit.eventually (ge_mem_nhds zero_lt_one)] with y hy; intro N D s hs hu hv hw; obtain ⟨a,b,c,d⟩:= ratesT B p y; have hp : 0 < BProof.g y:=coin_pos ..; have h1:=hs.trans hu; refine ⟨x,b,?_,hp.le,a,c,?_,hv,?_,?_⟩
 · refine le_trans (b:=feeVal B p T y-BProof.g y) (by unfold feeVal mainW; rw [add_sub_cancel_right]; exact mul_le_mul_of_nonneg_left (by have:=add_le_add (ageMono (add_le_add hu hu) (add_nonneg h1 h1) hw) (ageMono hu h1 hw); linarith) puffPrice_p) (sub_le_self _ hp.le)
 · exact le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (coverC_m hw)) a.le) d
 · unfold feeVal mainW; have hb:0≤ BProof.g y*amountJ (coins p)*Real.exp 1:=mul_nonneg (mul_nonneg hp.le (pJ (zero_le_one.trans (coin_ge p)))) (Real.exp_pos _).le; exact add_pos_of_nonneg_of_pos (mul_nonneg puffPrice_p (add_nonneg hb (add_nonneg (ageP (add_nonneg h1 h1) _) (ageP h1 _)))) hp
 change 64*_*(feeα B p y)⁻¹≤1 at hy; rw [←div_eq_mul_inv,div_le_iff₀ a,one_mul] at hy; exact hy -- target Roots.mild
end YM.CF.BProof.Oasis
