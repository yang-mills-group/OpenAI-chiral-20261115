import YM.CF.Reed.Lend
set_option linter.unusedSectionVars false

/-! Sign and last insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock NormedSpace Function Finset Pastry Phase
attribute [local instance] opCStarAlgebra
variable {n m : Type*} [LinearOrder n] [Fintype n] [LinearOrder m] [Fintype m]
lemma slip {i : n} {t:Finset n} (p:i∈t) (s) : monu s t*col i=0 := by rw [← insert_erase p,monu_v s _ _ (notMem_erase _ _),neg_mul,Algebra.smul_mul_assoc,mul_assoc, show col i*col i=0 from put_sq _,mul_zero,smul_zero,neg_zero] -- tune
lemma monu_m (s t : Finset n) (i:n) (p:i∉t) : monu s t*col i=(-parity i t) • monu s (insert i t) := by rw [monu_v _ _ _ p,neg_smul,smul_neg,neg_neg,smul_smul,parity_sq,one_smul]
lemma gaze_basis (a b s t : Finset n) (i:n) : zap s t (monu a b * col i)=if i∈t then -parity i t*zap s (t.erase i) (monu a b) else 0 := by
  by_cases h:i∈b
  · rw [slip h,zap_free]; split; rw [zap_one,if_neg,mul_zero]; intro p; have ht := (Prod.mk.inj p).2; rw [←ht] at h; simp at h
    rfl
  rw [monu_m _ _ _ h,zap_s,zap_one]; by_cases g:(s,t)=(a,insert i b)
  · obtain ⟨e,r⟩:= Prod.mk.inj g; subst t; rw [if_pos g, if_pos (mem_insert_self ..),erase_insert h,zap_one,if_pos (by rw [e]),mul_one,mul_one, parity_hi _ _ _ le_rfl]
  rw [if_neg g,mul_zero]; split_ifs with k; swap; rfl
  rw [zap_one,if_neg,mul_zero]; intro p; obtain ⟨e,q⟩:=Prod.mk.inj p; apply g; rw [←q, insert_erase k,e] -- tune
lemma gaze {A : EF n} (h : Plain A) (s t: Finset n) (i:n) : zap s t (A*col i)= if i∈t then -parity i t * zap s (t.erase i) A else 0 := by
  rw [absorb_monu h]; simp only [sum_mul,zap_sum, Algebra.smul_mul_assoc]; simp_rw [zap_s,gaze_basis ..]
  by_cases k:i∈t
  · simp only [if_pos k, mul_sum]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; ring
  simp [k]
lemma nil_exp (A : FC n) (h : A*A=0) : exp A=1+A := by
  rw [exp_eq_tsum ℂ]; dsimp only; rw [tsum_eq_sum (s:=range 2)]; norm_num [sum_range_succ]
  intro i g; have ht := mem_range.not.mp g; obtain ⟨p,hp⟩:=Nat.exists_eq_add_of_le (show 2 ≤ i by omega); rw [hp,pow_add,sq,h,zero_mul,smul_zero]
lemma pairMute (v : Poly n m) (i j : n) : (v.term i*v.term j)*(v.term i*v.term j)=0 := by rw [←mul_assoc,mul_assoc (v.term i),v.swapV j i,mul_neg, ←mul_assoc (v.term i),v.square i]; simp
lemma pairComm (v : Poly n m) (i j k:n) : Commute (v.term i*v.term j) (v.term k) := by
  unfold Commute SemiconjBy; rw [mul_assoc,v.swapV j k, mul_neg, ←mul_assoc, v.swapV i k,neg_mul,neg_neg,mul_assoc]
lemma evenShare (t:Finset n) (i:LeanV n) : Commute (monu t t) (put i) := by
  induction t using Finset.induction_on with
  | empty=> rw [monu_nil]; exact Commute.one_left _
  | insert j t p ih=>
    rw [monu_both p]; apply Commute.neg_left
    unfold Commute SemiconjBy; let s:=monu t t; let x := put i; have h₁ : col j*x= -(x*col j):= eq_neg_of_add_eq_zero_left (put_put ..); have h₂ : bar j*x= -(x*bar j):= eq_neg_of_add_eq_zero_left (put_put ..)
    change bar j*s*col j*x=x*(bar j*s*col j); rw [mul_assoc (bar j*s), h₁,mul_neg,←mul_assoc,mul_assoc (bar j),show s*x=x*s from ih,←mul_assoc (bar j),h₂, neg_mul, neg_mul,neg_neg,mul_assoc,mul_assoc,mul_assoc]
def ballad (i:n) := -(bar i*col i)
def axis (s:Finset n): EF n:= ∑ i∈s, ballad i
def jolt (s:Finset n) := exp (axis s)
lemma jolt_hit {i:n} {S : Finset n} (k:i∉S) : jolt (insert i S)=jolt S*(1+ballad i) := by
  letI : NormedAlgebra ℚ (EF n) := NormedAlgebra.restrictScalars ℚ ℂ _
  have he : Commute (ballad i) (axis S) := Commute.sum_right _ _ _ fun j _=> by
    apply Commute.neg_left; apply Commute.neg_right
    exact (pairComm (cane (LeanV n)) (false,i) (true,i) (false,j)).mul_right (pairComm (cane (LeanV n)) _ _ (true,j))
  rw [jolt,show axis (insert i S)=ballad i+axis S from sum_insert k, add_comm, exp_add_of_commute he.symm,nil_exp (ballad i)]; rfl; unfold ballad; rw [neg_mul_neg]; exact pairMute (cane (LeanV n)) (false,i) (true,i)
lemma lost (s : Finset n) (v : LeanV n) : Commute (jolt s) (put v) := Commute.exp_left (Commute.sum_left _ _ _ (fun i _=> (pairComm (cane (LeanV n)) (false,i) (true,i) v).neg_left))
lemma sesame {S : Finset n} {i:n} (p : i∉ S) {t u: Finset n} (h : t⊆S) (g:u⊆S) (l : insert i t=insert i u): t=u := by
  rw [← erase_insert (show i∉t from fun p₁=>p (h p₁)), l, erase_insert (show i∉u from fun p₁=>p (g p₁))]
lemma jolt_all (s : Finset n) : jolt s=∑ i∈s.powerset, monu i i := by
  induction s using Finset.induction_on with
  | empty=>
    letI : NormedAlgebra ℚ (EF n) := NormedAlgebra.restrictScalars ℚ ℂ _
    simp [jolt,axis,monu_nil]
  | insert i s p ih=>
    rw [jolt_hit p, ih,mul_add,mul_one,sum_mul,powerset_insert, sum_union]
    swap
    · apply disjoint_left.mpr; intro a h g; obtain ⟨b,k,rfl⟩:= mem_image.mp g; exact p (mem_powerset.mp h (mem_insert_self ..))
    rw [sum_image (fun a h b g l=> sesame p (mem_powerset.mp h) (mem_powerset.mp g) l)]; congr 1; apply sum_congr rfl; intro j g; have ht : i∉ j := fun l=>p (mem_powerset.mp g l)
    rw [monu_both ht,ballad,mul_neg, ←mul_assoc, show monu j j * bar i=bar i * monu j j from evenShare j (false,i)]
lemma jolt_abs (s : Finset n) : Plain (jolt s) := by rw [jolt_all]; exact Absorb.lot _ _ (fun i _=>monu_abs ..)
-- S upper. no columns i read for i∈S
abbrev avoid (i:n): Finset (LeanV n):= Finset.univ.erase (true,i)
lemma jolt_end (s : Finset n) (i:n) (h:i∉s) : Absorb (avoid i) (jolt s) := by
  rw [jolt_all]; apply Absorb.lot; intro a g
  obtain ⟨v,hV,f⟩:= monu_unit a a; rw [f]; apply Absorb.scale; apply Absorb.atom; intro j l; apply mem_erase.mpr; refine ⟨fun k=>h ?_,mem_univ _⟩; apply mem_powerset.mp g; rw [k,index_c] at l; exact l
lemma absent {i:n} {t : Finset n} (s) (k:i∈t) {A:EF n} (h : Absorb (avoid i) A) : zap s t A=0 := by unfold zap; rw [h.cold,mul_zero]; exact fun l=> (mem_erase.mp (l ((index_c ..).mpr k))).1 rfl
lemma bar_in (s t: Finset n) {A : EF n} {i:n} (h:i∈s) (p : Absorb (avoid i) A) : zap s t (A * bar i * jolt s)= if i∈t then 0 else parity i t * zap s (insert i t) (A*jolt s) := by
  have hx := (lost s (false,i)).symm; let Q := s.erase i; let B:= jolt Q; let D := A*B
  have he : jolt s=B*(1+ballad i) := by nth_rw 1 [← insert_erase h]; exact jolt_hit (notMem_erase _ _)
  have ht : ballad i*bar i=0 := by
    unfold ballad; rw [neg_mul,mul_assoc]; rw [show col i*bar i= -(bar i*col i) from eq_neg_of_add_eq_zero_left (put_put ..), mul_neg,←mul_assoc, show bar i*bar i=0 from put_sq _]; simp
  have hu : A*bar i*jolt s=D*bar i := by rw [mul_assoc, show bar i*jolt s=jolt s*bar i from hx,he,mul_assoc B (1+ballad i),add_mul,ht,one_mul,add_zero,←mul_assoc] -- tune
  have hw : Absorb (avoid i) D := p.times (jolt_end _ _ (notMem_erase _ _))
  rw [hu]; split_ifs with l
  · exact absent s l (hw.times (Absorb.blade (by simp [avoid])))
  have hQ : Plain (D*bar i) := (hw.packs (subset_univ _)).times (Absorb.blade (mem_univ (false,i)))
  rw [he, show A*(B*(1+ballad i))=D+(-1:ℂ) • ((D*bar i)*col i) by
    rw [←mul_assoc]; change D*(1+ballad i)=_; unfold ballad; rw [mul_add,mul_one,mul_neg, ←mul_assoc,neg_one_smul],zap_l,absent s (mem_insert_self ..) hw, zero_add,zap_s,gaze hQ,if_pos (mem_insert_self ..),erase_insert l, parity_hi t i i le_rfl]; simp only [neg_mul,one_mul,neg_neg]; rw [←mul_assoc,parity_sq,one_mul]
end YM.CF.Reed
