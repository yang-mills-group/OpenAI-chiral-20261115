import Anomaly.Plane.Tripod
/-! Polarization/staging for positive lower and ratios. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric MeasureTheory NormedSpace ProbabilityTheory Finset
open GeometryP
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace Classical
variable {K L:Type}[Fintype K][Fintype L]
abbrev plumK(K:Type):= Fin 2→ K
variable (W:plumK K→ℂ)
def turnip (K:Type):Equiv.Perm (plumK K):=Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl K)
@[simp] lemma turn_zero (i:plumK K): turnip K i 0=i 1:= by simp [turnip]
@[simp] lemma turn_one (i:plumK K): turnip K i 1=i 0:= by simp [turnip]
private lemma eqPU {i j:plumK K}: i=j ↔ i 0=j 0 ∧ i 1=j 1:= ⟨fun h=> by rw [h]; exact ⟨rfl,rfl⟩,fun h=>funext fun i=> Fin.cases h.1 (fun i=> by fin_cases i; exact h.2) i⟩
lemma turn_self (i:plumK K): turnip K (turnip K i)=i:=eqPU.mpr ⟨by rw [turn_zero,turn_one], by rw [turn_one,turn_zero]⟩
def glaze (i:plumK K) := (1/2:ℂ)*(W i+W (turnip K i))
@[simp] lemma glaze_s (i:plumK K): glaze W (turnip K i)=glaze W i:=by unfold glaze; rw [turn_self,add_comm]
variable (R:K→K→ℝ)(V:plumK K→ℂ)
lemma tripSoul (d:plumK K→ℂ)(h:∀ i,d (turnip K i)=d i):∑ i,d i*glaze W i= ∑ i,d i*W i:=by
 let f i:=d i*W i; unfold glaze; simp_rw [mul_left_comm (d _),mul_add (d _),←mul_sum,sum_add_distrib]; rw [show ∑ i:plumK K,d i*W (turnip K i) = ∑ i,d i*W i from (sum_equiv (turnip K) (by simp) fun i _=> congrArg (· *_) (h i).symm)]; ring -- notation tune
lemma glaze_L : lodging R (glaze W) V=lodging R W V:=by
 unfold lodging; rw [sum_comm,sum_comm (f:=fun i j=>twinB R i j • (W i*V j))]; apply sum_congr rfl; intro j _; let x i:ℂ:= (↑(twinB R i j):ℂ)*V j
 have he(i): x (turnip K i)=x i:=by unfold x twinB; rw [turn_zero,turn_one]; ring_nf
 have hx(i:plumK K)(w:ℂ): twinB R i j • (w*V j)=x i*w:=by unfold x; simp only [Complex.real_smul]; ring
 simp_rw [hx]; exact tripSoul W x he
lemma park: lodging R W V= lodging (fun i j=> R j i) V W:=by
 unfold lodging; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_comm (V i)]; congr 1; unfold twinB; ring
lemma glaze_R : lodging R W (glaze V)=lodging R W V:=by rw [park W,park W R V,glaze_L] -- order?
def breve (p:K→L)(c:ℝ) (i j:K):ℝ:= if p i=p j then c else 0
variable (p:K→L) (c:ℝ)
def ledger (p:K→L)(W:plumK K→ℂ)(i:plumK L):=∑ j:plumK K,if p ∘ j=i then W j else 0
lemma ledger_w(z:plumK L→ℂ):∑ i:plumK L,z i*ledger p W i= ∑ j,z (p ∘ j)*W j:=by unfold ledger; simp_rw [mul_sum]; rw [sum_comm]; simp [mul_ite]
lemma ledger_B(V:plumK K→ℂ)(Z:L→L→ℝ): lodging Z (ledger p W) (ledger p V)= lodging (fun i j=> Z (p i) (p j)) W V:=by
 have ht(j:plumK L)(k:ℂ): ∑ l:plumK L,twinB Z j l • (k*ledger p V l)=∑ i:plumK K,twinB Z j (p ∘ i) • (k*V i):=by simp_rw [Complex.real_smul,←mul_assoc]; exact ledger_w ..
 unfold lodging; simp_rw [ht]; rw [sum_comm,sum_comm (f:=fun i j=>twinB _ i j • (W i*V j))]; apply sum_congr rfl; intro j _; let d(i:plumK L):ℂ:=twinB Z i (p ∘ j) • V j; rw [← show ∑ i,d i*ledger p W i= _ from (show ∑ i,d i*ledger p W i=∑ i,twinB Z i (p ∘ j) • (ledger p W i *V j) from sum_congr rfl fun i _=>by unfold d; rw [smul_mul_assoc,mul_comm (V j)])]; rw [ledger_w]; apply sum_congr rfl; intro i _; unfold d; rw [smul_mul_assoc,mul_comm (V j)]; rfl
lemma starredX : ledger p (star W)= star (ledger p W):=by funext i; unfold ledger; simp_rw [Pi.star_apply,star_sum,apply_ite star,star_zero]
lemma glazed : glaze (star W)=star (glaze W):=by funext; simp [glaze]
private lemma coreθ {c:ℝ} (i j:plumK K): twinB (breve id c) i j=(if i=j then c^2 else 0)+(if turnip K i=j then c^2 else 0):=by
 unfold breve twinB; simp_rw [@eqPU K _ _,turn_zero,turn_one]; simp [ite_mul,mul_ite,pow_two,ite_and]; grind
lemma bareL : lodging (breve id c) W (star W)= (2*c^2) • (↑(∑ i:plumK K,‖glaze W i‖^2):ℂ):=by
 rw [←glaze_R,←glaze_L,glazed]; unfold lodging; push_cast; rw [Finset.smul_sum]
 apply sum_congr rfl; intro i _; simp_rw [coreθ,add_smul,ite_smul,zero_smul,sum_add_distrib]; simp only [sum_ite_eq,mem_univ,ite_true,Pi.star_apply,glaze_s]; rw [show glaze W i *star (glaze W i)= ((↑(‖glaze W i‖^2)):ℂ) from (Complex.mul_conj _).trans (by rw [Complex.normSq_eq_norm_sq])]; simp only [Complex.real_smul]; push_cast; ring
lemma positive_X: lodging (breve p c) W (star W)=(2*c^2) • (↑(∑ i:plumK L,‖glaze (ledger p W) i‖^2):ℂ):=by
 change lodging (fun i j=> breve id c (p i) (p j)) W (star W)=_; rw [←ledger_B,starredX,bareL]; -- may defeq dec instances/tally
variable (T:L→ℝ)
def ship(p:K→L)(U:plumK K→ℂ)(d:L→ℝ) := ∑ i,(∏ j,d (p (i j))) • U i
lemma pacing: ship p W T=∑ i:plumK L,(∏ j,T (i j)) • glaze (ledger p W) i:=by
 unfold ship; symm; simp_rw [Complex.real_smul]; let Y:(plumK L)→ℂ:= fun i=>↑(∏ j,T (i j)); change ∑ i,Y i*_=∑ i,Y (p ∘ i)*_; rw [tripSoul (ledger p W)]
 · exact ledger_w ..
 intro i; simp [Y,Fin.prod_univ_succ,mul_comm] -- tune
abbrev priva(T:L→ℝ):= 1+∑ i:plumK L,(∏ j: Fin 2,T (i j))^2
lemma framed (t:ℝ)(h:0 ≤ t)(x:t ≤ (ship p W T).re): t^2 ≤ priva T*∑ i:plumK L, ‖glaze (ledger p W) i‖^2:=by
 let F(i:plumK L):= ∏ j,T (i j); let g:=glaze (ledger p W); let C:= ∑ i, ‖g i‖^2
 rw [pacing W p] at x; have hE:t ≤ ∑ i,|F i| *‖g i‖:= x.trans ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans ((norm_sum_le ..).trans_eq (sum_congr rfl fun i _=> by rw [norm_smul]; rfl))))
 have he:= sum_mul_sq_le_sq_mul_sq univ (fun i=>|F i|) (fun i=>‖g i‖); refine (pow_le_pow_left₀ h hE _).trans (he.trans (?_)); simp_rw [sq_abs]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (sum_nonneg fun _ _=>by positivity)
end YM.Regis.Head.Brecht.Pier
