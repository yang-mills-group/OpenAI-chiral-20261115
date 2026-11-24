import YM.CF.Acorn.Limes
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D]
-- pre support for true degree-2 polynomials. unrestricted scalar masks BEFORE integral.
def PairX (X:Master D Y)(O:n→Y)(R:Seal Y)(a:ℝ)(F:D→FC n)(V:ℝ):Prop:=∃ (J:Type) (_:Fintype J) (U:J→Seal Y)(p q:J→ I n)(f:J→D→ℂ)(v:J→ℝ),
 (∀ i,Pro X (U i) (f i) (v i) ∧ (v i≠0→ R ⊆ U i ∧ O (p i).2∈ U i ∧ O (q i).2 ∈ U i))∧ (∑ i,cost a R (U i)*v i) ≤ V∧ ∀ x,F x=∑ j,f j x • (pen (p j)*pen (q j))
def DriftX(a h v c:ℝ)(k:ℕ):= worth k ^2*h^2*(Real.exp a+v)^2*c
variable {X:Master D Y}{O:n→Y}{a c h v K:ℝ}{S:Seal Y}{F G A B:D→ FC n}
section
variable (t:0≤a)(q:0≤v)(w:PairX X O S a F c)(e:∀ x,UnitR (A x))(P:∀ i:I n, Drop X O a i (fun x=>unitL (A x) (pen i)) v)
private lemma opt(C:ℝ)(T:Seal Y): C=C:=rfl
include t q w e P
lemma motion_k (i)(g:i≤2): Carries X O S a h (fun x=> sent (unitL (A x)) i (F x)) (2*DriftX a h v c X.k) :=by
  obtain ⟨J,l,U,p,r,f,z,k,W,H⟩:=w; let D':=Real.exp a+v
  have hd:0≤D':= add_nonneg (Real.exp_pos _).le q; let T(j):= worth X.k ^ 2 * cost a S (U j) * h^2 * z j*D'*D'
  have hp(j) : Drop X O a j (fun _=>pen j) D':=(Drop.fixed _ _ _ _).more (le_add_of_nonneg_right q); have hq(j) := (P j).more (le_add_of_nonneg_left (Real.exp_pos a).le : v≤D')
  have ht(j)(t₁ t₂:D→FC n)(H:Drop X O a (p j) t₁ D')(Z: Drop X O a (r j) t₂ D'): Carries X O S a h (fun x=> f j x • (t₁ x*t₂ x)) (T j):= H.copp Z t le_rfl (k j).1 (k j).2
  have hi (j:J): Carries X O S a h (fun x=> sent (unitL (A x)) i (f j x • (pen (p j)*pen (r j)))) (2*T j):=by
    let R:=pen (p j); let S':=pen (r j)
    have hx:0≤ T j:= mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (rent_pos ..).le) (sq_nonneg h)) (k j).1.pos) hd) hd
    let g' (x:D):= unitL (A x); let a (x:D):=g' x R; let b (x:D):=g' x S'
    have hc:T j≤ 2*T j:=by linarith
    have hL(x:D):g' x (R*S')= a x*S'+R*b x:=unit_der ..
    interval_cases i
    · simp_rw [sent_zero]; exact (ht j _ _ (hp _) (hp _)).more hc
    · simp_rw [sent,pow_one,map_smul]; norm_num; simp_rw [unit_der, smul_add]; rw [two_mul]; exact (ht j _ _ (hq _) (hp _)).add (ht j _ _ (hp _) (hq _))
    · have hk(x:D):g' x (g' x (R*S'))=(2:ℂ) • (a x*b x):=read_sq _ _ _ (nilS _ (e x) _) (nilS _ (e x) _)
      change Carries X O _ _ _ (fun x=> (↑(Nat.factorial 2):ℂ)⁻¹ • ((g' x * g' x) (f j x • (R*S')))) (2*T j)
      have he(x:D):(↑(Nat.factorial 2):ℂ)⁻¹ • ((g' x * g' x) (f j x • (R*S'))) = f j x • (a x*b x) :=by simp only [map_smul]; change _ • (_ • (g' x (g' x (R*S'))))=_; rw [hk, smul_comm (f j x),← smul_assoc]; norm_num
      simp_rw [he]; exact (ht j _ _ (hq _) (hq _)).more hc
  simp_rw [H]; have he(x:D) (i:ℕ): sent (unitL (A x)) i (∑ j:J,f j x • (pen (p j)*pen (r j)))=∑ j:J,sent (unitL (A x)) i (f j x • (pen (p j)*pen (r j))):= by simp only [sent,map_sum,Finset.smul_sum]
  simp_rw [he]; apply (Carries.all_s Finset.univ _ _ (fun j _=>hi j)).more; rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold T DriftX
  calc
    _ = worth X.k ^ 2*h^2*D'^2 * ∑ i,cost a S (U i)*z i :=by rw [mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left W (by positivity)
omit P t q e in
lemma PairX.pos : 0≤c:=by obtain ⟨J,l,U,p,r,f,z,k,W,H⟩:=w; exact (sum_nonneg fun i _=>mul_nonneg (rent_pos ..).le (k i).1.pos).trans W
-- conjugated proof via rotor ≤2
lemma shook : Carries X O S a h (fun x=> exp (A x)*F x*exp (-A x)) (6*DriftX a h v c X.k):=by
 let n':= 2*Fintype.card n; let R:Finset ℕ:= (range (n'+1)).filter (fun i=>i≤2)
 have hv: R.card≤3:= by apply le_trans (card_le_card (show R⊆ range 3 from fun i h=>mem_range.mpr (by have he:=mem_filter.mp h|>.2; omega))) (le_of_eq (Finset.card_range 3))
 have hu (x):exp (A x)* F x* exp (-A x)= ∑ i∈R,sent (unitL (A x)) i (F x):=by
   rw [rotor (e x).exhaust (unit_negR _ (e x)).exhaust]; refine Eq.symm (sum_subset (filter_subset ..) ?_); intro i g t
   have he:¬ i≤2:= fun h=> t (mem_filter.mpr ⟨g,h⟩)
   obtain ⟨I,hI,U,p,r,f,z,k,W,H⟩:=w
   apply abyss (k:=3) _ _ _ _ (by omega)
   rw [show ∀ y:FC n,(unitL (A x)^3) y= (unitL (A x)) (unitL (A x) (unitL (A x) y)) from fun y=>by rw [pow_succ',pow_two]; rfl,H]; simp_rw [map_sum,map_smul, read_sq _ _ _ (nilS _ (e x) _) (nilS _ (e x) _),map_smul,unit_der,nilS _ (e x),zero_mul,mul_zero,add_zero,smul_zero]; simp
 simp_rw [hu]; apply (Carries.all_s R (h:=h) _ _ (fun i y=>motion_k t q w e P i (mem_filter.mp y).2)).more
 rw [sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_right (show (R.card:ℝ)≤3 by exact_mod_cast hv) ?_) (le_of_eq ?_); · unfold DriftX; have hp:= w.pos; positivity
 ring
end
end YM.CF.Acorn
