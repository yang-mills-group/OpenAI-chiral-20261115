import YM.SU5.FiniteGaugeData.Pannier.Gale
import Refrain.Foundation
import Verses.Database
/-!
# Knife of period-varying Male: the sharp projector on any permitted Pane, stencil.
Uses Lively, truncated at ALL the requested points (estimate in operator norm).
Doesn't require analyticity at the hard flag decision. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {a C r e:ℝ}{n N:Side}
variable {F:Chin n→Op (Single n)}

open CF.Papyrus.Franc
namespace Checkers
private lemma one_pressure {r:ℕ}(S:Seal (Site (More n)))(p:S.card ≤ r)(s T: Pane n)(h:∀ i∈ leaks S, ‖profile s i-profile T i‖ ≤ e)(v:0≤e): fare S (profile s) (profile T) ≤ (r:ℝ)*4*e:=by
 have he: (leaks S).card ≤ r*4:= by
    calc
    _ ≤ Finset.card (S ×ˢ (Finset.univ: Finset Axis)):= card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1, mem_univ _⟩
    _ = S.card*4 := by simp [Axis] -- RHS placeholder ambiguous
    _ ≤ r*4 := Nat.mul_le_mul_right _ p
 unfold fare; refine (sum_le_sum (g:=fun _=> e) (fun i hi=> h i hi)).trans ?_
 rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) v
private lemma windH (p:RootedK (bail n r) (bail n r) a C (fun v : Openc (More n) r=> F v.val))(hr:0<a) (hx:0<r) (d:ℕ)(U V:Pane n)
    (u:Guard U r)(v:Guard V r)(L:Finset (Seat n))(e:ℝ)(h:0≤e)(t:Rightful (Lattice.halo d L) U V e) (T:Op (Single n))
    (det:∀ i j, T i j=0 ∨ node j.1.1∈L ∧ ‖T i j‖≤‖F (profile U) i j-F (profile V) i j‖) :
    Verses.condor T ((2*Real.exp (-(a*d))+ d*4*e/r) * C):=by
 obtain ⟨N,b,p,j,w⟩:=p
 let U':Openc (More n) r:=⟨profile U,U,u,by simpa⟩
 let V':Openc (More n) r:=⟨profile V,V,v,by simpa⟩
 let A:=saleM a b
 let E:=2*Real.exp (-(a*d))+(d:ℝ)*4*e/r
 have hp:0≤E:= by unfold E; positivity
 let Q(i v):= E*A i v
 have hx(i z:Single n): ‖T i z‖≤ Q i z:=by
   obtain t'|⟨x,y⟩:=det i z
   · rw [t',norm_zero]; exact mul_nonneg hp (sale_nn (fun S i j=> (p S).nonn ..) a i z)
   apply y.trans; rw [show F (profile U)=_ from w U', show F (profile V)=_ from w V',Matrix.sum_apply,Matrix.sum_apply,← sum_sub_distrib]; unfold Q A saleM; rw [mul_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro s _
   let a':=b s i z; let H:= (p s).expo i z; have ha : ‖_‖ ≤ _:= H.bounded U'; have hb:= H.bounded V'; let Q:= N s U' i z - N s V' i z; have hQ: ‖Q‖ ≤ a'+a':= (norm_sub_le ..).trans (add_le_add ha hb)
   change ‖Q‖≤ E * (rent a s*a'); rw [←mul_assoc]; by_cases g:a'=0; · rw [g,mul_zero]; simpa [g] using hQ
   rcases le_or_gt s.card d with he|he
   · obtain ⟨s₁,h₁,g₁⟩:=H.triggered g
     have hs(y)(l:y∈s): y ∈ (Lattice.halo d L) := halo_spec.mpr ⟨_,x,(le_of_lt (show separation (node z.1.1) y<s.card from s₁.lim _ g₁ _ l)).trans he⟩
     have hu:= one_pressure s he U V (fun i hi=>t i (mem_filter.mpr ⟨mem_univ _,hs i.1 (mem_filter.mp hi).2.1,hs _ (mem_filter.mp hi).2.2⟩)) h
     apply (H.variation U' V').trans
     rw [mul_comm (E*rent a s)]; apply mul_le_mul_of_nonneg_left _ (show 0≤a' from H.positive)
     change fare s _ _ / |r| ≤ _; rw [abs_of_pos hx]; exact (div_le_div_of_nonneg_right hu hx.le).trans (le_trans (le_add_of_nonneg_left (by positivity)) (le_mul_of_one_le_right hp (rent_one hr.le _)))
   · rw [show a'+a'= 2*a' from (by ring)] at hQ; apply hQ.trans; apply mul_le_mul_of_nonneg_right _ H.positive
     unfold E Branch.rent; rw [add_mul]; apply le_trans _ (le_add_of_nonneg_right (show 0 ≤ ↑d*4*e/r*Real.exp (a*s.card) by positivity)); rw [mul_assoc,←Real.exp_add]; refine le_mul_of_one_le_right (by norm_num) (Real.one_le_exp (by nlinarith [show (d:ℝ) ≤ s.card by exact_mod_cast he.le]))
 intro i; refine (sum_le_sum (fun j _=>hx j i)).trans ?_; unfold Q; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.cols _) hp

-- bounded absolute column costs via the all-coeff Rooted
lemma column (p:RootedK (bail n r) (bail n r) a C (fun v : Openc (More n) r=> F v.val))(hr:0<a)(U:Chin n)(u:U∈Openc (More n) r) : Verses.condor (F U) C:=by
 obtain ⟨N,b,p,j,t⟩:=p
 let V:Openc (More n) r:=⟨U,u⟩
 rw [show F U= _ from t V]
 intro i; refine (Finset.sum_le_sum (fun k _=>?_)).trans (j.cols i)
 rw [Matrix.sum_apply]; refine (norm_sum_le ..).trans (sum_le_sum (fun s _=> ?_)); let H:=(p s).expo k i
 apply (H.bounded V).trans (le_mul_of_one_le_left H.positive (rent_one hr.le _))

structure Sow (j:ℕ) (N:Side)(a C δ:ℝ) : Prop where
 daylight (b:Bool)(M:Tulip.Male)(P:Pane N) (h:Guard P δ): Verses.condor (hand b (spar j M P)) C
 cross (b:Bool)(M:Tulip.Male)(U V:Pane N)(p:Guard U δ)(q:Guard V δ)(S:Finset (Seat N))(ε:ℝ)(d:ℕ)(e:0≤ε)(h:Rightful (Lattice.halo d S) U V ε)(T:Op (Single N)) : (∀ i k,T i k=0 ∨ node k.1.1∈S ∧ ‖T i k‖≤‖(hand b (spar j M U)-hand b (spar j M V)) i k‖)→ Verses.condor T ((2*Real.exp (-(a*d))+d*4*ε/δ)*C)
lemma warm (j:ℕ)(p:1≤j):∃ δ a C:ℝ,0<δ∧0<a∧0<C∧∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val→ Sow j N a C δ:=by
 obtain ⟨a,R,δ,h,Rp,D,hX,u,w⟩:=Lively.link (skew_s j p true) (skew_s j p false)
 refine ⟨δ,a,R,D,h,Rp,(eventually_ge_atTop hX).mono fun k v n q=>?_⟩
 let Vx(b:Bool)(M:Tulip.Male) := skewE j M (!b) n; have he(b:Bool)(M:Tulip.Male)(P:Pane n):Vx b M (profile P)=hand b (spar j M P):=by cases b <;>rfl
 have hp(b M): Solo a R (Vx b M) δ := by cases b; exact u M n (v.trans q); exact w M n (v.trans q)
 constructor; · intro b M U hv; rw [←he]; exact column (hp b M|>.lib) h _ ⟨U,hv,by simpa⟩
 intro b M A B hf hy S ε d e hr T H; simp_rw [←he] at H; exact windH (hp b M|>.lib) h D d A B hf hy S ε e hr T H
end Checkers
end YM.CF.Pannier.Chancel
