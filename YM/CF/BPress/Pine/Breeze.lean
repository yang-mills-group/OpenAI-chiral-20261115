import YM.CF.BPress.Pine.Fruition
import YM.CF.BPress.Locale.Atlas
/- Eq:B-PfC sum over decorated labels. Group with Palmer, fits contour-free theorem part. Pairing *sign* and zero of non-matches/repeats implemented through genuine Pfaffian tested on exterior strings, only geometry projection for power. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y]{F:Branch.Field Y}
namespace Story
variable {D:EdgeD I B Y F}(S:Story J D)(b:B→ℝ)(w:J→ℝ)(p:S.Drone)
variable {C a μ Z γ :ℝ}
include S
-- direct delivery. e is location(P) suction.
lemma flair {b w} (h:Enorm D (a+a) C b)(e:∀ i, 0≤ w i)(v:μ≤ a)(t:0≤μ)(x:Y): score S.fort (S.blue b w) μ x p ≤
     let q:= S.own p.1 x; Real.exp (-(a*F.span x q))*rent μ (S.base p.1)*w p.1 *stiff S b (a+a) p := by
 have he:0≤ a:= t.trans v; unfold score; let q:=S.own p.1 x; let X:=S.base p.1; set z:=a*F.span x q; split; next hx=>
    have ht(z:ℝ)(A B:ℝ)(p:Real.exp z*A ≤ B): A ≤ Real.exp (-z)*B:= by rw [mul_comm, Real.exp_neg,←div_eq_mul_inv]; rw [mul_comm] at p; exact (le_div_iff₀ (Real.exp_pos _)).2 p
    have ht := ht _ _ _ (temperature S p t he v x hx); apply (mul_le_mul_of_nonneg_right ht (blue_pos S b w p e h.f)).trans; unfold blue stiff; exact Eq.le (by ring) -- tune z
 next h' => have he:= e p.1; have ht:=rent_pos μ X; have hp:= stif_s S b p (a+a) h.f; exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le ht.le) he) hp
lemma startup (h:Enorm D (a+a) C b)(e:∀ i, 0≤ w i)(v:μ≤a)(t:0≤ μ)(f: hasSpot F a Z)(x:0≤γ)(H:Cash S.base (fun i=> ahead S (w i) i (1+C)) μ γ): Cash S.fort (S.blue b w) μ (Z*γ):=by
 refine ⟨fun p=> blue_pos S b w p e h.f,?_ ⟩; intro o
 let r(x:Y):= Real.exp (-(a*F.span o x)); let g(p:S.Drone):= score S.fort (S.blue b w) μ o p; let T:= fun (v:J)=> rent μ (S.base v)* (w v*(1+C)^(S.word v).length); let A(v:J):=own S v o; refine ⟨fun i=>?_ , (hasSum_fintype g).summable,?_⟩; unfold score; split; exact mul_nonneg (Real.exp_pos _).le (blue_pos S b w _ e h.f); exact le_rfl -- tune classical DecEq
 have hp(x:Y): 0≤r x:=(Real.exp_pos _).le; have ht(i:J): (∑ t:D.Net (S.word i), g ⟨i,t⟩) ≤ r (A i)*T i:= by
    let φ:=r (A i)*rent μ (S.base i)*w i; apply le_trans (sum_le_sum (g:=fun t:D.Net (S.word i)=>φ*stiff S b (a+a) ⟨i,t⟩) (fun j _=> flair S ⟨i,j⟩ h e v t o)); rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left (prenatal S b h i) (mul_nonneg (mul_nonneg (hp _) (rent_pos ..|>.le)) (e _))).trans_eq (by unfold T; ring)
 rw [tsum_fintype,Fintype.sum_sigma]; apply le_trans (sum_le_sum (fun i _=> ht i)); let v(y i):= score S.base (fun i=> ahead S (w i) i (1+C)) μ y i; refine le_trans (b:=∑ x:J,(∑ y:Y,r y*v y x)) (sum_le_sum (fun i t=>?_)) ?_ -- tune
 · apply le_trans _ (single_le_sum (f:=fun y=>r y*v y i) (fun x _=>mul_nonneg (hp _) ((H.hits x).1 _)) (mem_univ (A i))); unfold v score; rw [if_pos (owner S i o|>.1)]; exact le_rfl
 rw [sum_comm]; simp_rw [←mul_sum]; exact (sum_le_sum (g:=fun i:Y=>r i*γ) (fun i _=> mul_le_mul_of_nonneg_left (budget_sum (H.hits i) univ) (hp _))).trans (by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (f o) x)

omit S
variable {s: Side} {p:ℕ}
def bPay (μ:ℝ) (n:ℕ): ℝ:= Real.exp (-μ/2*(n:ℝ)) * ((4:ℝ)^4*(n+1:ℝ)^4)
abbrev cPay (μ:ℝ):= ∑' i:ℕ, bPay (μ+μ) i
lemma halo_price (x:Site s)(n:ℕ): ((bay (Grid.field 4 s) x n).card:ℝ)≤ 4^4*(n+1:ℝ)^4:=by have he:=Locale.univ_growth (r:=n) x; refine (Nat.cast_le.mpr he).trans ?_; rw [←mul_pow]; exact_mod_cast (show (4*n+1)^4 ≤(4*(n+1))^4 from by gcongr; omega)
lemma root_earn (p:0<μ) (s:Side) : hasSpot (Grid.field 4 s) μ (cPay μ):= by
 let F:=Grid.field 4 s; intro x; let g(n:ℕ):=Real.exp (-(μ*(n:ℝ))); let V:= univ.image (F.span x); rw [show (∑ y:Site s,_) =∑ n∈V,∑ y:Site s with F.span x y=n,g n from ?_]; swap; · simp_rw [sum_filter]; rw [sum_comm]; refine sum_congr rfl (fun i _=>?_); rw [sum_ite_eq]; rw [if_pos (mem_image_of_mem _ (mem_univ i))]; -- tune
 have he:= fund_hit (μ+μ) (4^4) (add_pos p p) (by norm_num); apply le_trans _ (he.sum_le_tsum V ?_); apply sum_le_sum; intro i h; rw [show -(μ+μ)/2= -μ by linarith,sum_const, nsmul_eq_mul,mul_comm, neg_mul]; refine mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (card_le_card ?_)).trans (halo_price x i)) (Real.exp_pos _).le; refine fun x p=> (bay_mem _).mpr (le_of_eq ((mem_filter.mp p).2)); intro i _; positivity -- tune generic φ
lemma root_κ (p:0<μ):0<cPay μ:= (fund_hit (μ+μ) (4^4) (add_pos p p) (by norm_num)).tsum_pos (fun i=>by positivity) 0 (by norm_num)
end Story
end YM.CF.BPress.Pine
