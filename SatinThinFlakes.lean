import YM.SU5.FiniteGaugeData.Pannier.Gale
import SatinThinShaft

/-! From Gale (reproving private helper & replacing wind_help with all-entry budget),
 repress the density and projector even out to arbitrary Male. -/
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
private lemma one_pressure {r:ℕ}(S:Seal (Site (More n)))(p:S.card ≤ r)(s T: Pane n)(h:∀ i∈ leaks S, ‖profile s i-profile T i‖ ≤ e)(v:0≤e): fare S (profile s) (profile T) ≤ (r:ℝ)*4*e:=by
 have he: (leaks S).card ≤ r*4:= by
    calc
    _ ≤ Finset.card (S ×ˢ (Finset.univ: Finset Axis)):= card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1, mem_univ _⟩
    _ = S.card*4 := by simp [Axis] -- RHS placeholder ambiguous
    _ ≤ r*4 := Nat.mul_le_mul_right _ p
 unfold fare; refine (sum_le_sum (g:=fun _=> e) (fun i hi=> h i hi)).trans ?_
 rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) v

private lemma wind_col (p:RootedK (bail n r) (bail n r) a C (fun v : Openc (More n) r=> F v.val))(hr:0<a) (hx:0<r) (d:ℕ)(U V:Pane n)
    (u:Guard U r)(v:Guard V r)(L:Finset (Seat n))(e:ℝ)(h:0≤e)(t:Rightful (Lattice.halo d L) U V e) (k:Single n) (lk:node k.1.1∈ L):
    (∑ j:Single n, ‖F (profile U) j k-F (profile V) j k‖) ≤ (2*Real.exp (-(a*d))+ d*4*e/r) * C:=by
 obtain ⟨N,b,p,j,w⟩:=p
 let U':Openc (More n) r:=⟨profile U,U,u,by simpa⟩
 let V':Openc (More n) r:=⟨profile V,V,v,by simpa⟩
 let A:=saleM a b
 let E:=2*Real.exp (-(a*d))+(d:ℝ)*4*e/r
 have hp:0≤E:= by unfold E; positivity
 let Q(i v):= E*A i v
 refine (sum_le_sum (s:=univ) (g:=fun i=>Q i k) fun i _=> ?_).trans ?_
 · let z:=k; have x:=lk; rw [show F (profile U)=_ from w U', show F (profile V)=_ from w V',Matrix.sum_apply,Matrix.sum_apply,← sum_sub_distrib]; unfold Q A saleM; rw [mul_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro s _
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
 · unfold Q; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.cols _) hp

/- Market claims at unbounded near support. `/r` fixed at purchase. -/
abbrev shortfall (a C r e:ℝ)(m:ℕ):ℝ:= (2*Real.exp (-(a*m))+ m*4*e/r)*C
open Fock
structure Colts (j:ℕ) (N:Side) (a C r :ℝ) : Prop where
 c : ∀ (U:Pane N) (M:Tulip.Male) (_:Guard U r) (k:Single N), (∑ i:Single N, ‖(spar j M U) i k‖) ≤ C
 rank (U V:Pane N) (M:Tulip.Male) (_:Guard U r) (_:Guard V r) (k:Single N) (L:Finset (Seat N)) (m:ℕ) (e:ℝ) (_:0≤e)(_:Rightful (Lattice.halo m L) U V e) (_:node k.1.1 ∈ L):
    (∑ i:Single N, ‖(spar j M U-spar j M V) i k‖) ≤ shortfall a C r e m
lemma colts_thrive (j:ℕ)(w:1 ≤ j): ∃ C a v:ℝ,0<C∧0<a∧0<v∧ ∃ n:ℕ,∀ N:Side,n≤N.val→ Colts j N a C v:=by
 -- cf burley
 obtain ⟨a,C,r,h,t,l,v,Q⟩:= funde_s j w
 refine ⟨C,a,r,t,h,l,v,fun n v=> ?_⟩; constructor
 · intro U M u k
   let X:Openc (More n) r:=⟨profile U,U,u,by simpa⟩
   obtain ⟨F,c,H,Z,W⟩:= (show Solo _ _ _ _ from Q M n v).lib
   rw [show spar j M U= _ from W X]; refine (sum_le_sum (g:=fun i=>saleM a c i k) (fun i _=>?_)).trans (Z.cols _); rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (sum_le_sum (fun S _=> ((H S).expo _ _ |>.bounded X).trans (le_mul_of_one_le_left ((H S).nonn ..) (rent_one h.le S))))
 intro U V M u hV k L m θ ht e w
 exact wind_col (Q M n v).lib h l m U V u hV L θ ht e k w

open Papyrus.Franc
variable {j d:ℕ} (W:Colts j n a C r)(M:Tulip.Male)(U V:Pane n)(L:Finset (Seat n))(x:0≤a)(c:0≤C)(v:0<r)
lemma shortfall_ge {k:ℕ}(c:0≤C)(v:0<r)(w:0≤e) : 0≤ shortfall a C r e k:= by unfold shortfall; positivity
include W c v
lemma raising_tickets (p:Guard U r)(t:Guard V r)(w:0≤e)(g:Rightful (Lattice.halo d L) U V e): revE (spar j M U - spar j M V) ≤ (Fintype.card (Single n):ℝ)*shortfall a C r e d + ((modesIn n L)ᶜ: Finset (Single n)).card*(2*C):=by
 let G:=spar j M U; let H:=spar j M V; let S:=shortfall a C r e d; let K:=((modesIn n L)ᶜ: Finset (Single n))
 rw [revE_cols]; refine (sum_le_sum (g:=fun i=>S+if i∈ K then 2*C else 0) (fun i _=>?_)).trans_eq ?_
 · split
   next h=>
      let D:=G-H; let X:=fun k:Single n=>node k.1.1
      apply le_trans (b:= (∑ k: Single n, ‖G k i‖)+(∑ k:Single n, ‖H k i‖)); swap; · have ht:= W.c U M p i; have hx:= W.c V M t i; have s:=shortfall_ge (k:=d) (a:=a) c v w; unfold G H S; linarith only [ht,hx,s]
      rw [← sum_add_distrib]; exact sum_le_sum fun i _=> norm_sub_le ..
   next h=>
      rw [add_zero]; exact W.rank U V M p t i L d e w g ((modes_at ..).1 (notMem_compl.mp h))
 rw [sum_add_distrib,←sum_filter]; simp only [filter_mem_eq_inter,univ_inter,sum_const,card_univ,nsmul_eq_mul,K]; rfl
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.raising_tickets
#print axioms YM.CF.Pannier.Chancel.colts_thrive
