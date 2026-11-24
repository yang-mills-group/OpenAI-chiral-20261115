import YM.CF.Fixed.OperatorHeat

/-!
# Reflection variational inequality for the flight multiplier

Sum positive eigenvalues of Hermitian link-reflected blocks. Proof independent
of Fock presentation. Use also on systems where one-particle reflection is
retained after partial spatial Fourier. Lower **area** expenses of seam gluing
are probed later. Pay CARE with direction: the inequality proved here works
for the energy term multiplying the heat. Its inverse has the OPPOSITE inequality,
which is relevant because in FiniteGaugeData `capP` there is NO `flight(U,t)` factor.
Nothing alleged about failing PSD of the main readings just because the factor
*can* cost in that direction (also quadratics in other factors).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Bulk
open Function NormedSpace Lattice Fock Filter Metric Matrix Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

section vt
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B X: Op n}

def trR (A:Op n) := A.trace.re
omit [DecidableEq n] in
lemma plus_t (A B:Op n) : trR (A+B)=trR A + trR B:=by unfold trR; rw [trace_add,Complex.add_re]
omit [DecidableEq n] in
lemma debit_t (A:Op n) : trR (-A)= -(trR A):=by simp [trR]
omit [DecidableEq n] in
lemma diff_t (A B:Op n) : trR (A-B)=trR A - trR B:=by rw [sub_eq_add_neg,plus_t,debit_t,sub_eq_add_neg]
omit [DecidableEq n] in
lemma comm_t (A B:Op n) : trR (A*B)=trR (B*A):=congrArg Complex.re (trace_mul_comm ..)
omit [DecidableEq n] in
lemma star_t(A:Op n) : trR (star A)=trR A:=by simp [trR,trace,Matrix.diag,Complex.re_sum]
omit [DecidableEq n] in
lemma scale_t(c:ℝ)(A:Op n) : trR (c•A) = c*trR A:=by unfold trR; simp
lemma sqrt_spec (U:UNI n)(d:n→ℝ)(h:0≤d) : CFC.sqrt (spectral U d)=spectral U (fun i=>Real.sqrt (d i)):=by
  have hp:0≤spectral U d:=by rw [← spectral_zero U,spectral_le]; exact h
  have he: 0≤spectral U (Real.sqrt ∘ d):=by rw [←spectral_zero U, spectral_le]; exact fun i=>Real.sqrt_nonneg _
  refine (CFC.sqrt_eq_iff _ _ hp he).mpr ?_; rw [spectral_mul]; apply congrArg; funext i; exact Real.mul_self_sqrt (h i) -- tune
lemma sqrt_abs(U:UNI n)(d:n→ℝ) : CFC.sqrt ((spectral U d)^2)=spectral U (fun i=>|d i|):=by
  rw [spectral_pow, sqrt_spec U (d^2) (fun i=> sq_nonneg (d i))]; apply congrArg; funext i; exact Real.sqrt_sq_eq_abs _
lemma sqrt_le (A:Op n)(h:IsSelfAdjoint A): 0≤ CFC.sqrt (A^2)+A := by
  obtain ⟨U,d,rfl⟩:= spectral_exists _ h; rw [sqrt_abs, spectral_add,←spectral_zero U,spectral_le]; intro i; change 0≤|d i|+d i; linarith [neg_le_abs (d i)]
lemma tr_positive (h:0≤A)(b:0≤ B):0≤ trR (A*B) := by
  let T:= CFC.sqrt A; have he : T*T=A:= CFC.sqrt_mul_sqrt_self _ h
  have hx : star T=T:=(CFC.sqrt_nonneg A).star_eq
  rw [←he,mul_assoc,comm_t]
  have hp : 0≤ (T*B*T):=by nth_rw 1 [←hx]; exact star_left_conjugate_nonneg b _
  exact (RCLike.nonneg_iff.mp (nonneg_iff_posSemidef.mp hp).trace_nonneg).1
variable [Nonempty n]
lemma projector_comm (p : Safe A) : Commute A (projector A) := by
  obtain ⟨U,d,rfl⟩:=spectral_exists _ p.self; rw [projector_spectral U d p]; rw [Commute,SemiconjBy,spectral_mul,spectral_mul, mul_comm d]
lemma projector_max (p:Safe A)(B:Op n)(h:0≤B)(t:B≤1) : trR (A*B) ≤ trR (A*projector A) := by
  let P:=projector A
  have hp: 0≤ A*P ∧ A*(1-P)≤0:=by obtain ⟨U,d,e⟩:=spectral_exists _ p.self; change 0≤A*projector A ∧ A*(1-projector A)≤0; subst A; rw [projector_spectral _ _ p,spectral_mul, ← spectral_zero U, spectral_le, ←spectral_one U,spectral_sub,spectral_mul,spectral_le]; constructor <;> intro i <;> by_cases h:0<d i <;> simp [occ,h] <;> linarith
  change _ ≤ trR (A*P)
  have hu:= tr_positive hp.1 (sub_nonneg.mpr t); rw [mul_sub, mul_one,diff_t] at hu
  have ht:= tr_positive (neg_nonneg.mpr hp.2) h; rw [neg_mul,debit_t,mul_sub,mul_one,sub_mul,diff_t] at ht; linarith
lemma doublePay (A:Op n)(p:Safe A) : 2 • (A*projector A)= A + CFC.sqrt (A^2):=by
  obtain ⟨U,d,rfl⟩:=spectral_exists _ p.self
  rw [two_smul, projector_spectral U d p,spectral_mul,sqrt_abs,spectral_add,spectral_add]; apply congrArg; funext i; by_cases h:0<d i
  · simp [occ,h,abs_of_pos h]
  · simp [occ,h,abs_of_nonpos (le_of_not_gt h)]

def energy (A:Op n):= trR (A * projector A)
lemma energy_eq (p:Safe A): energy A= (trR A+trR (CFC.sqrt (A^2)))/2 := by
  have he:=congrArg trR (doublePay A p); rw [two_smul, plus_t,plus_t] at he; unfold energy; linarith
lemma energy_f {n:Type*}[LinearOrder n][Fintype n] (A:Op n): energy A=(fermiEnergy A).re:=rfl
end vt

section pair
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (A B C D : Op n)
local notation "F" => Matrix.fromBlocks
local notation "G" => Op (n⊕n)
omit [DecidableEq n] in
lemma block_tr : trR (F A B C D) = trR A + trR D := by simp [trR, trace,Matrix.diag,Fintype.sum_sum_type,Complex.re_sum] -- tune
omit [Fintype n] [DecidableEq n] in
lemma block_star : star (F A B C D)=F (star A) (star C) (star B) (star D):= by ext (i | i) (j | j) <;> rfl
lemma put_pos(p:0≤A)(h:0≤D):0≤ F A 0 0 D:=by
  let a:=CFC.sqrt A; let b:=CFC.sqrt D
  suffices K:F A 0 0 D=(F a 0 0 b)*(star (F a 0 0 b)) by rw [K]; exact mul_star_self_nonneg _
  have ha: a*a=A:=CFC.sqrt_mul_sqrt_self A p; have hb:b*b=D:=CFC.sqrt_mul_sqrt_self D h
  rw [block_star,(show star a=a from (CFC.sqrt_nonneg A).star_eq),(show star b=b from (CFC.sqrt_nonneg D).star_eq)]; simp [fromBlocks_multiply,ha,hb]
lemma from_square_root (X:G) (h:F A B C D=X)(q:B = star C)(hx:A=0)(hy:D=0) : CFC.sqrt (X^2)= F (CFC.sqrt (B*C)) 0 0 (CFC.sqrt (C*B)):=by
  subst X A B D; have hp : 0≤star C*C:=star_mul_self_nonneg _; have ht: 0≤C*star C:=mul_star_self_nonneg _
  rw [sq, fromBlocks_multiply]; simp only [zero_mul,mul_zero,add_zero,zero_add]
  rw [CFC.sqrt_eq_iff _ _ (put_pos _ _ hp ht) (put_pos _ _ (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)),fromBlocks_multiply,CFC.sqrt_mul_sqrt_self _ hp, CFC.sqrt_mul_sqrt_self _ ht]; simp
-- purification of the diagonal one-particle variational leg
lemma half_project (h:0≤A)(s:A≤1) : let b:= CFC.sqrt (A-A*A); IsStarProjection (F A (-b) (-b) (1-A)):=by
  obtain ⟨U,d,rfl⟩:= spectral_exists _ h.isSelfAdjoint; intro b
  have ht : d≤1:=by rw [←spectral_le U d 1,spectral_one]; exact s
  have hu: 0≤d:=by rw [←spectral_le U 0 d,spectral_zero]; exact h
  let X:=spectral U d; let c:= d-d*d; have hc:0≤c:=fun i=>sub_nonneg.mpr ((mul_le_mul_of_nonneg_left (ht i) (hu i)).trans_eq (mul_one _))
  have hE:b = spectral U (fun i=>Real.sqrt (c i)):= by unfold b; rw [spectral_mul,spectral_sub]; exact sqrt_spec U _ hc
  have he : b* b= X-X*X:= by unfold b X; rw [CFC.sqrt_mul_sqrt_self _ _]; rw [spectral_mul,spectral_sub,←spectral_zero U,spectral_le]; exact hc
  have hm:X*b=b*X:=by unfold X; rw [hE,spectral_mul,spectral_mul,mul_comm d]
  constructor
  · change F X _ _ _ * (F X _ _ _) = _
    rw [fromBlocks_multiply]; apply fromBlocks_inj.mpr;
    change X*X+-b*(-b)=X ∧ X*(-b)+ -b *(1-X)= -b ∧ (-b)*X+(1-X)*(-b)= -b ∧ (-b)*(-b)+(1-X)*(1-X)=1-X
    simp only [mul_neg,neg_mul, mul_sub, mul_one, sub_mul, one_mul, he,hm]; constructor
    · abel
    refine ⟨?_,?_,?_⟩<;> abel
  rw [isSelfAdjoint_iff,block_star, star_sub,star_one,h.star_eq,star_neg,(CFC.sqrt_nonneg _|>.star_eq : star b=b)]

-- The crossed channel C/D may differ in both half-rows.

private lemma across_bound (A B Z:Op n) :
    -(trR (B*star A * Z)) - trR (A*star B * star Z) ≤ trR (A*star A * CFC.sqrt (Z*star Z))+trR (B*star B * CFC.sqrt (star Z * Z)):=by
  let X:G:= F 0 Z (star Z) 0; let Y:G:= F A 0 B 0; have hX:IsSelfAdjoint X:= by unfold X; rw [isSelfAdjoint_iff,block_star,star_star,star_zero]
  have hV:= sqrt_le X hX
  rw [from_square_root 0 Z (star Z) 0 X rfl (star_star Z).symm rfl rfl] at hV
  have he:=tr_positive (mul_star_self_nonneg Y) hV; rw [mul_add, plus_t] at he; unfold X Y at he; simp only [block_star,fromBlocks_multiply,block_tr,mul_zero,star_zero,add_zero,zero_add] at he; linarith
/-- `tr A` and `tr B` need not separately vanish. Covers tied spatial-momentum
modes (with varying spatial links but still diagonal at each time slice in spatial
coord after Fourier). This is *not* a reflection inequality for the FiniteGaugeData state. -/
def linkOp (A B C D:Op n): Op (n⊕n):=F A (-(C*star D)) (-(D*star C)) (-B)
variable [Nonempty n]
lemma seam_ineq(p:Safe (linkOp A B C D))(u:Safe (linkOp A A C C))(v: Safe (linkOp B B D D)): 2*energy (linkOp A B C D) ≤ energy (linkOp A A C C)+energy (linkOp B B D D)+ trR A - trR B:=by
  let M:=linkOp A B C D; let R:=projector M; have hs:IsStarProjection R:= p.projection
  obtain ⟨P,T,S,Z,h⟩:∃ P T S Z:Op n,F P T S Z=R:=⟨_,_,_,_, fromBlocks_toBlocks R⟩; have hp:= hs.isSelfAdjoint.star_eq; rw [← h,block_star] at hp; replace hp:=fromBlocks_inj.mp hp
  obtain ⟨hP,-,rfl,hZ⟩:= hp -- rfl? hp.2.2.1 : star T=S, replaces S
  have hu:= hs.isIdempotentElem; unfold IsIdempotentElem at hu; rw [← h,fromBlocks_multiply] at hu; replace hu:=fromBlocks_inj.mp hu
  have hp(X B C Y:Op n)(k:0≤F X B C Y):0≤X ∧ 0≤Y:= by
    replace k:= nonneg_iff_posSemidef.mp k
    exact ⟨nonneg_iff_posSemidef.mpr (k.submatrix Sum.inl),nonneg_iff_posSemidef.mpr (k.submatrix Sum.inr)⟩
  have hn:=hp _ _ _ _ (show 0≤F P T _ Z from h ▸ hs.nonneg)
  have ht:= hs.one_sub.nonneg; rw [← h,←(fromBlocks_one (α:=ℂ) (m:=n) (l:=n)), show F (1:Op n) 0 0 (1: Op n)-_= F (1-P) (-T) (-star T) (1-Z) from (by ext (i|i) (j|j)<;> simp [Matrix.one_apply]) ] at ht
  obtain ⟨ha,hb⟩:= hp _ _ _ _ ht
  let L:= CFC.sqrt (T*star T); let W:= CFC.sqrt (star T*T); let X:= F P (-L) (-L) (1-P); let Y:= F (1-Z) (-W) (-W) Z
  have hh : L=CFC.sqrt (P-P*P):=congrArg CFC.sqrt (show T*star T=P-P*P from eq_sub_of_add_eq ((add_comm ..).trans hu.1)) -- orientation
  have hq : W=CFC.sqrt ((1-Z) -(1-Z)*(1-Z)):=congrArg CFC.sqrt (show star T*T=_ from by rw [show (1-Z)-(1-Z)*(1-Z)= Z-Z*Z from by noncomm_ring]; exact eq_sub_of_add_eq hu.2.2.2)
  have hX:IsStarProjection X:=by unfold X; rw [hh]; exact half_project P hn.1 (sub_nonneg.mp ha)
  have hY:IsStarProjection Y:=by unfold Y; have h:=half_project (1-Z) hb (sub_le_self _ hn.2); rw [hq]; simpa only [sub_sub_cancel] using h -- tune
  let Z1:=linkOp A A C C; let Z2:=linkOp B B D D
  have hcost:= add_le_add (projector_max u X hX.nonneg hX.le_one) (projector_max v Y hY.nonneg hY.le_one)
  change trR (F A _ _ (-A)*X)+trR (F B _ _ (-B)*Y)≤ energy Z1+energy Z2 at hcost
  refine le_trans ?_ (sub_le_sub_right (add_le_add_left hcost _) _)
  change 2*trR (F A _ _ (-B)*R) ≤ _; rw [←h]; unfold X Y
  simp_rw [fromBlocks_multiply,block_tr,plus_t]; simp only [mul_neg,neg_mul, mul_sub, mul_one,diff_t,debit_t]
  unfold L W; linarith [across_bound C D T]
end pair
end YM.CF.Fixed.Bulk
