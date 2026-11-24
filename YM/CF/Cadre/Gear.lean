import YM.CF.Cadre.Sike
import YM.CF.Cadre.Pawn
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open PowerSeries
variable (V: leaf A→ Finset A→PS)(v:∀ X:Palot.leaf A,∀ D ⊆ X.val,cent (V X D))(Q: leaf A→ℝ)(q:0≤Q)(κ:ℝ)(m:1≤κ)(L w:ℝ)(b:leaf A→ℝ)
variable {x s:ℝ}(T:Tour b s) (γ c d e h:ℝ)(g:h≥0)(k:∀ o:A,serif V κ L w b o 0 0<γ)
local notation "B"=> loom_v L w b
local notation "K_"=> seed_v V κ
local notation "S"=> serif V κ L w b
variable (p:0 ≤ L-w*h) (r:0 ≤ w)(mQ:0 ≤ γ)(z:Palot.leaf A→ℝ)(z₁:0 ≤ z)
variable (hC:∀ i:A, nook (fog (loom_v L w b 0) Q γ) i ≤ c)(hD:∀ i:A,shelfR (fog (loom_v L w b 0) Q γ) i ≤ d)(hI:∀ i:A, nook (z*loom_v L w b 0) i ≤ e)(hm:0 ≤ c)(hw:s*c ≤ w)
variable (M O:Palot.leaf A→ℝ)(Z:Palot.leaf A→ Finset A→ℝ)(F₀:Palot.leaf A→ℝ)
abbrev cribR (w:Palot.leaf A→ℝ): Rinse A ℝ:=fun _ _ i c=>w i*c
local notation "K"=> cribR M
local notation "U"=>chip K Z
local notation "E"=> nutL K Z
lemma phrase(X:ΣA)(Y:ΣA)(P:Finset A):rill K V (farW A) X P Y=fizz X Y P V (M Y):=by ext i; rw [rils,fizz,coeff_smul,map_sum]; unfold cribR; rw [smul_eq_mul,mul_sum]
lemma ace :flowZ U M M U:=by
 intro X D p i; rw [dash,pingT _ _ _ _ (by simp [cribR])]; unfold arpX; simp_rw [phrase]; exact Eq.le (by rw [moss]; by_cases h:D.Nonempty; simp [h]; simp [h,cribR]) -- tune
lemma oreL0 : flowZ U M 0 E:=by
 intro X D p i; rw [nutL,tide]; unfold arpX moss front; simp_rw [phrase]; split <;>simp
variable (xZ:∀ X:leaf A,∀ D⊆ X.val,0 ≤ Z X D)(xK:0≤ M)
include xZ xK
lemma hire(X:ΣA)(D:Finset A)(p:D⊆ X.val):cent (U X D):=by
 intro n; induction n using Nat.strong_induction_on generalizing X D with
 | h n ih=>
   cases n with
   |zero=> rw [peg]; exact xZ _ _ p
   |succ n=>
    rw [peel,sprig,ore]; apply mul_nonneg (show (0:ℝ)≤ ((n:ℝ)+1)⁻¹ by positivity); apply sum_nonneg; intro i _; apply sum_nonneg; intro G _; apply mul_nonneg (xK i); rw [coeff_prod]; apply sum_nonneg; intro j u; apply prod_nonneg; intro a w; exact ih _ (Nat.lt_succ_of_le ((single_le_sum (fun k _=> Nat.zero_le (j k)) w).trans_eq (mem_finsuppAntidiag.mp u).1)) a _ inter_subset_right
lemma heatR (X:ΣA)(D:Finset A) :cent (E X D):=by
 intro n; cases n; · rw [tick_r]
 rename_i n; unfold nutL; rw [sprig,front,map_sum]; apply mul_nonneg (show (0:ℝ)≤ ((n:ℝ)+1)⁻¹ by positivity); apply sum_nonneg; intro i _; rw [rils]; apply sum_nonneg; intro G p; exact mul_nonneg (xK _) (cent.multi G (fun i:ΣA=> (U i (D∩i.val))) (fun j _=> hire M Z xZ xK _ _ inter_subset_right) _)
variable (xC:∀ i:A,nook (M*loom_v (L+2) 0 b 0) i ≤ c)(cx:0 ≤ c)(m:1≤κ)(sx:0 ≤ s)(G:0 ≤ γ)(a1:s*γ≤1)(pW:s*c ≤ w)(gk:∀ i:A,nook ((roofL Z κ)*loom_v L w b 0) i< γ)(Hτ:0 ≤ L-w*1)(aw:c+s*c*γ - (w-s*c)*γ<0)
include T sx G cx xC gk Hτ pW m r a1 aw
lemma stallK : Timer (chip (cribR M) Z) M κ L w b s γ c (s*c) c 1 M:=by
 let W:= M*loom_v (L+2) 0 b 0; let F:=fog (B 0) M γ; let H:=M*B 0
 have hh(X:ΣA): H X ≤ F X:=le_mul_of_one_le_right (mul_nonneg (xK _) (Real.exp_pos ..|>.le)) (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) G))
 have h1(X:ΣA):F X≤ W X∧F X*X.val.card ≤ s*W X:=by
    let a:=b X; have ht:a≥1:=T.pos _; have hu: (X.val.card:ℝ)*γ ≤ a:=by have he:=mul_le_mul_of_nonneg_right (T.rate X) G; apply he.trans; change (s*a)*γ≤ _; rw [mul_right_comm s]; exact mul_le_of_le_one_left (by linarith) a1
    let k:=Real.exp (L*a+a); have hp:F X ≤ M X*k:=by
       unfold F fog waveL; dsimp only [loom_v]; rw [mul_zero, sub_zero, mul_assoc, ← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add_right hu _)) (xK _)
    have he:k*Real.exp a=loom_v (L+2) 0 b 0 X:=by unfold loom_v k; unfold a; rw [←Real.exp_add]; ring_nf
    have hv:F X*b X ≤ W X:=by
       have hq:a ≤ Real.exp a:= by linarith [Real.add_one_le_exp a]
       change F X*a ≤ _; apply (mul_le_mul hp hq (by linarith) (mul_nonneg (xK _) (Real.exp_pos ..|>.le))).trans_eq; rw [mul_assoc,he]; rfl
    have hz:0 ≤ F X:=mul_nonneg (mul_nonneg (xK _) (Real.exp_pos ..|>.le)) (Real.exp_pos ..|>.le)
    exact ⟨(le_mul_of_one_le_right hz ht).trans hv, (mul_le_mul_of_nonneg_left (T.rate _) hz).trans (by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hv sx)⟩
 refine ⟨hire M Z xZ xK, xK,m,T,sx,cx,zero_le_one,Hτ,r,G,?_,fun i=>(sum_le_sum (s:=spark i) (fun j _=> (h1 j).1)).trans (xC i), ?_, xK,fun i=>(sum_le_sum (s:=spark i) (fun j _=> (hh j).trans (h1 j).1)).trans (xC i),pW,aw,ace M Z⟩
 · intro i; have hp:seed_v (chip (cribR M) Z) κ 0 0=roofL Z κ:=by unfold seed_v bark; simp_rw [car_k,peg]
   unfold serif; rw [hp]; exact gk i
 intro i; apply le_trans ?_ (mul_le_mul_of_nonneg_left (xC i) sx); unfold nook; rw [mul_sum]; exact sum_le_sum fun j _=> (h1 j).2
end YM.CF.Cadre
