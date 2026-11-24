import YM.CF.Continuum.NotLogN
import YM.CF.Continuum.Breath
import YM.CF.Continuum.Block

/-! Per-history gauge pressure at level zero INCLUDING correct vacuum
    pricing in small boxes. Exact exceptional exponents in terms of V (gauge
    lattice volume). Numeric estimates for when shells/kernels below are
    authorized in V. This is reworking SU5-pressure for this algebra. It is a
    complex amplitude estimate (still per-history relative, not uniform matching
    of the raw `GramM.v`). Not claiming analogous rectangle bootstrap. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial Real
open Graph Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova YM.Next.Rank Emu Mint
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {L' B N m:Side}{j n:ℕ}{r b c d e k y a w v B0 C L K H g D μ σ ρ τ η :ℝ}
local notation "xg"=> group.lieDim
local notation "Λ"=> mid m B

lemma budgetTaxEq (N:Side)(β t C L:ℝ)(hp: β*t^3≤1)(hb:0≤β)(ht:0≤t)(hz:t≤1)(h:0≤C):
 taxY N β t C L ≤ N.val^4*(C+C+ |L|) := by
 let a:ℝ:= N.val; have hv:0≤a^4:=by unfold a; positivity
 unfold taxY; change β*(a^4*_) +a^4*_≤a^4*_; rewrite [mul_left_comm, ←mul_add]
 apply mul_le_mul_of_nonneg_left _ hv; rw [mul_add]
 have he(v:ℝ)(t:β*v≤1):β*(C*v)≤ C:=by rw [mul_left_comm]; exact mul_le_of_le_one_right h t
 have hf:β*t^4≤ 1:=by rw [show (4:ℕ)=3+1 from rfl,pow_succ,←mul_assoc]; exact le_trans (mul_le_of_le_one_right (by positivity) hz) hp
 exact add_le_add (add_le_add (he _ hp) (he _ hf)) (by calc
    L*t^2 ≤ |L| * t^2:=mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    _ ≤ |L| := mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht hz))

def sizes (N:Side):ℕ:=(More N).val^4
abbrev massMeter (N:Side):ℝ:=(sizes N:ℝ)
lemma matter_meter (N:Side) : (N.val:ℝ)^4*2^4=massMeter N:=by unfold massMeter sizes More; change _ = (((N.val*2)^4:ℕ):ℝ); push_cast; ring
lemma money_pos(N:Side) : 1 ≤ massMeter N := by apply Nat.one_le_cast.mpr; unfold sizes; exact pow_pos (More N).property _

def strengthLog (g:ℝ) := (group.lieDim:ℝ) * Real.log g
def budgetCharge (_V:GramM N)(g X:ℝ):= massMeter N*(3*strengthLog g+X)
private def mountT (C L:ℝ):=C+C+|L|
private lemma up_peak(V:GramM N)(c:0≤C)(hp: V.beta*V.p.threshold^3 ≤ 1)(b:0≤V.beta): taxY (More N) V.beta V.p.threshold C L ≤ massMeter N*mountT C L:=by
 have hf:= budgetTaxEq (More N) V.beta V.p.threshold C L hp b V.p.threshold_pos.le V.p.threshold_le c; exact hf.trans_eq (by unfold mountT massMeter sizes; push_cast; rfl)
private lemma face_money(N:Side) : (Fintype.card (Face (Per (More N))):ℝ)= massMeter N* Fintype.card PlaqAxes:=by
 change (Fintype.card (Site (More N) × PlaqAxes):ℝ)=_; unfold massMeter sizes; rw [Fintype.card_prod,site_card]; push_cast; rfl
private lemma meter_floor(V:GramM N) (C L:ℝ) (k:V.beta*g^2=1) : stoutY (More N) V.beta g b V.p.threshold C L= massMeter N * (Fintype.card PlaqAxes*(b/2+C^2/2)) + taxY (More N) V.beta V.p.threshold C L:=by
 unfold stoutY goldY; rw [face_money,show b*g^2/2+(C*g)^2/2=(b/2+C^2/2)*g^2 by ring]; congr 1; rw [mul_assoc (massMeter N), show V.beta * _=V.beta*g^2*(massMeter N*(↑(Fintype.card PlaqAxes)*(b/2+C^2/2))) by ring,k,one_mul]
def lowerMoney (O:HaarBudget group)(C L b H:ℝ):=4* Real.log O.small-xg*H-(mountT C L+ (Fintype.card PlaqAxes)*(b/2+C^2/2))
def upperMoney (O:HaarBudget group)(C L c H:ℝ):=mountT C L+Fintype.card PlaqAxes/2+3* Real.log O.big+3*strengthLog (2/c)+3*xg*H
lemma lowerRate(O:HaarBudget group)(V:GramM N)(b':0≤C)(t:0<g)(k:V.beta*g^2=1)(μ:|Real.log g|≤ massMeter N*H)(hp: V.beta*V.p.threshold^3≤1):
 Real.exp (budgetCharge V g (lowerMoney O C L b H)) ≤ clearRate O V C L b g:=by
 let f:=massMeter N; have hv:1≤f:=money_pos _; have he:=O.positive
 let U:=Real.log O.small; let a:=strengthLog g; have hl:U≤0:=Real.log_nonpos he.le O.small_le
 let F:=taxY (More N) V.beta V.p.threshold C L; let q:=mountT C L; have ht:F≤ f*q:= up_peak _ b' hp (variance_beta t k).le
 unfold clearRate; rw [meter_floor _ _ _ k,show O.small*g^xg=Real.exp (U+a) from ?_, ← Real.exp_nat_mul,← Real.exp_add]; swap; · unfold U a strengthLog; rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log he,Real.exp_log t]
 apply Real.exp_monotone; rw [site_card]; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat]; change _ ≤ -(massMeter N * _ + F) + (3 * ((More N).val:ℝ)^4 +1)*(U+a)
 rw [show ((More N).val:ℝ)^4=f from (by unfold f massMeter sizes; push_cast; rfl)]
 have hr: -(f*(xg*H:ℝ)) ≤ a:=by unfold a strengthLog; rw [mul_left_comm,←mul_neg]; exact mul_le_mul_of_nonneg_left ((abs_le.mp μ).1) (by positivity) -- signs?
 have hg: 4*f*U ≤ (3*f+1)*U:= by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv) hl]
 unfold lowerMoney budgetCharge; dsimp only [a,f] at *; linarith only [ht,hr,hg] -- local def q etc
lemma upperRate(O:HaarBudget group)(V:GramM N)(b':0≤C)(t:0<g)(k:V.beta*g^2=1)(μ:|Real.log g|≤ massMeter N*H)(hp: V.beta*V.p.threshold^3≤1)(c:ℝ)(e:0<c)(h:c≤ strength V.funds): fullRate O V C L g ≤ Real.exp (budgetCharge V g (upperMoney O C L c H)):=by
 let f:=massMeter N; have hv:1≤f:=money_pos _; have he:=O.big_ge; let s:=strength V.funds
 let U:=Real.log O.big+ strengthLog (2/c); let a:=strengthLog g; have hl:0≤U:=by
   have hf:1≤ 2/c:= by rw [le_div_iff₀ e,one_mul]; linarith [strength_le_one V.funds]
   exact add_nonneg (Real.log_nonneg he) (mul_nonneg (by positivity) (Real.log_nonneg hf))
 let F:=taxY (More N) V.beta V.p.threshold C L; let q:=mountT C L; have ht:F≤ f*q:= up_peak _ b' hp (variance_beta t k).le
 have ha: O.big * ((2*g)/strength V.funds)^xg ≤ Real.exp (U+a):=by
    unfold U a strengthLog; rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le he),Real.exp_log (div_pos (by norm_num) e),Real.exp_log t, mul_assoc,←mul_pow]; have hf:= strength_pos V.funds; gcongr; rw [div_mul_eq_mul_div]; gcongr
 let n:= sizes N; have hn:1≤n:=Nat.one_le_cast.mp hv
 unfold fullRate rebate; rw [site_card,face_money]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ha _) (Real.exp_pos _).le); swap; · have he:= strength_pos V.funds; positivity
 rw [←Real.exp_nat_mul, ←Real.exp_add]; apply Real.exp_monotone; let D:ℝ:= Fintype.card PlaqAxes; rw [show (More N).val^4=n from rfl]; push_cast [show 3≤3*n by omega]; -- sign?
 change F+f*D/2 + (3*f-3)*(U+a) ≤ _
 have hr: -(f*(xg*H:ℝ)) ≤ a:=by unfold a strengthLog; rw [mul_left_comm,←mul_neg]; exact mul_le_mul_of_nonneg_left ((abs_le.mp μ).1) (by positivity)
 unfold budgetCharge upperMoney; unfold U at *; change _ ≤ massMeter N*(3*a+(q+D/2+_+_+3*xg*H)); unfold f at *; linarith only [hl, ht,hr]
lemma flagBound (n:Side)(H C v z:ℝ)(k:v≤H)(s:z≤H)(h:0≤H)(p:0 ≤ C) : flagBill n v z C ≤ massMeter n *(4*C+3*H*2^4+180*45*6*C):=by rw [flagBill_eq]; let t:= (n.val:ℝ)^4; calc
 _ ≤ (4*C+3*H*2^4+180*45*6*C)*t:=mul_le_mul_of_nonneg_right (by linarith) (by unfold t; positivity)
 _ ≤ _:=by rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold t; rw [←matter_meter]; exact le_mul_of_one_le_right (by positivity) (by norm_num)
end YM.CF.Window
