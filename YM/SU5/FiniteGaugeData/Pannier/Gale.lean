import YM.SU5.FiniteGaugeData.Pannier.MobCap
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
private lemma one_pressure {r:ℕ}(S:Seal (Site (More n)))(p:S.card ≤ r)(s T: Pane n)(h:∀ i∈ leaks S, ‖profile s i-profile T i‖ ≤ e)(v:0≤e): fare S (profile s) (profile T) ≤ (r:ℝ)*4*e:=by
 have he: (leaks S).card ≤ r*4:= by
    calc
    _ ≤ Finset.card (S ×ˢ (Finset.univ: Finset Axis)):= card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1, mem_univ _⟩
    _ = S.card*4 := by simp [Axis] -- RHS placeholder ambiguous
    _ ≤ r*4 := Nat.mul_le_mul_right _ p
 unfold fare; refine (sum_le_sum (g:=fun _=> e) (fun i hi=> h i hi)).trans ?_
 rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) v
private lemma vent (p:RootedK (bail n r) (bail n r) a C (fun v : Openc (More n) r=> F v.val))(hr:0<a) (k:ℕ)(U:Chin n)(u:U∈ Openc (More n) r) (q:Op (Single n))
    (g:∀ i j, q i j=0 ∨ (k ≤ separation (node i.1.1) (node j.1.1) ∧ ‖q i j‖ ≤ ‖F U i j‖)): ‖q‖ ≤ Real.exp (-(a*k))*C:=by
 obtain ⟨N,b,p,j,t⟩:=p
 let V:Openc (More n) r:= ⟨U,u⟩
 let E:=Real.exp (-(a*k)); have hp:0≤ E:= (Real.exp_pos _).le
 let A:=saleM a b
 let K(i v):= E*A i v
 apply schur K q (E*C) (mul_nonneg hp j.posP)
 · intro i z; obtain h | ⟨l,h⟩:=g i z
   · rw [h,norm_zero]; exact mul_nonneg hp (sale_nn (fun S i j=> (p S).nonn ..) a i z) -- tune
   apply h.trans; rw [show F U=_ from t V, Matrix.sum_apply]; unfold K A saleM; rw [mul_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum
   intro s _; let a':=b s i z; let H:= (p s).expo i z
   apply (H.bounded V).trans; by_cases e:a'=0; · rw [show b s i z=0 from e,mul_zero,mul_zero]
   obtain ⟨he,hv,w⟩:=H.triggered e
   have hx: k<s.card:= lt_of_le_of_lt l (he.lim _ hv _ w)
   change a'≤ E * (rent a s*a'); rw [←mul_assoc]; apply le_mul_of_one_le_left H.positive; unfold E Branch.rent; rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith [show (k:ℝ) ≤ s.card by exact_mod_cast hx.le]
 · intro i; unfold K; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.rows _) hp
 intro i; unfold K; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.cols _) hp

-- leak condition on Field pairs at set s. use at all requests via stakes.
def Rightful (S:Finset (Seat n)) (U V: Pane n) (d:ℝ) := ∀ i∈ leaks S, ‖profile U i - profile V i‖ ≤ d
private lemma wind_help (p:RootedK (bail n r) (bail n r) a C (fun v : Openc (More n) r=> F v.val))(hr:0<a) (hx:0<r) (d:ℕ)(U V:Pane n)
    (u:Guard U r)(v:Guard V r)(L:Finset (Seat n))(e:ℝ)(h:0≤e)(t:Rightful (Lattice.halo d L) U V e) (T:Op (Single n))
    (det:∀ i j, T i j=0 ∨ node j.1.1∈L ∧ ‖T i j‖≤‖F (profile U) i j-F (profile V) i j‖) :
    ‖T‖ ≤ (2*Real.exp (-(a*d))+ d*4*e/r) * C:=by
 obtain ⟨N,b,p,j,w⟩:=p
 let U':Openc (More n) r:=⟨profile U,U,u,by simpa⟩
 let V':Openc (More n) r:=⟨profile V,V,v,by simpa⟩
 let A:=saleM a b
 let E:=2*Real.exp (-(a*d))+(d:ℝ)*4*e/r
 have hp:0≤E:= by unfold E; positivity
 let Q(i v):= E*A i v
 apply schur Q T (E*C) (mul_nonneg hp j.posP)
 · intro i z; obtain t'|⟨x,y⟩:=det i z
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
 · intro i; unfold Q; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.rows _) hp
 intro i; unfold Q; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.cols _) hp

variable {M:Tulip.Male}
def Widener (N:Side)(P Q:Pane N→ Op (Single N))(h:P=Q) := True -- unused
structure Winter (j:ℕ)(δ:ℝ) (N:Side)(γ:ℝ)(w:ℕ)(ε:ℝ):Prop where
  vent (b:Bool)(M:Tulip.Male)(X:Pane N)(h:Guard X δ)(T:Op (Single N)) : (∀ i k,T i k=0 ∨ w ≤ separation (node i.1.1) (node k.1.1) ∧ ‖T i k‖≤‖hand b (spar j M X) i k‖) → ‖T‖≤ε
  plank (b:Bool)(M:Tulip.Male)(L:Finset (Seat N))(U V:Pane N)(p:Guard U δ)(q:Guard V δ)(X:Rightful (Lattice.halo w L) U V γ) (T:Op (Single N)) : (∀ i k,T i k=0 ∨ node k.1.1∈ L ∧ ‖T i k‖≤‖(hand b (spar j M U)-hand b (spar j M V)) i k‖)→ ‖T‖≤ε
lemma winter (j:ℕ)(p:1≤j): ∃ δ>(0:ℝ),∃ N:ℕ,∀ ε>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N ≤ n.val→Winter j δ n γ w ε:=by
 obtain ⟨a,R,δ,h,Rp,D,hX,u,w⟩:=Lively.link (skew_s j p true) (skew_s j p false)
 refine ⟨δ,D,hX,fun ε ε'=>?_⟩; have hz:Tendsto (fun i:ℕ=>Real.exp (-(a*i))*R) atTop (𝓝 0):=by
    simpa only [Function.comp_apply,zero_mul] using ((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop h))).mul_const R)
 obtain ⟨W,x,r⟩:= ((hz.eventually (ge_mem_nhds (show 0<ε/4 by positivity))).and (eventually_gt_atTop 0)).exists
 let c:= ε*δ/(16*W*R); refine ⟨c,by unfold c; positivity,W,fun n q=>?_⟩
 let Vx(b:Bool)(M:Tulip.Male) := skewE j M (!b) n; have he(b:Bool)(M:Tulip.Male)(P:Pane n):Vx b M (profile P)=hand b (spar j M P):=by cases b <;>rfl
 have hp(b M): Solo a R (Vx b M) δ := by
    cases b; exact u M n q
    exact w M n q
 constructor
 · intro b M U p T' H
   simp_rw [←he] at H; have hx:profile U∈Openc (More n) δ:=⟨U,p,by simpa⟩
   exact (vent (hp b M|>.lib) h W (profile U) hx T' H).trans (x.trans (by linarith))
 intro b M L U V p q X T' H
 simp_rw [←he] at H; apply (wind_help (hp b M|>.lib) h D W U V p q L c (by unfold c; positivity) X T' H).trans; rw [add_mul];
 have hf:W*4*c/δ*R=ε/4:=by unfold c; field_simp; ring -- tune
 linarith
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.winter
