import YM.CF.Exa.Coin
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
section
variable {I D G W κ:Type}[Fintype I][DecidableEq I][TopologicalSpace κ][Fintype W][DecidableEq W][TopologicalSpace D]
variable {b:Stage W I D G}{s t u:Branch.Tag b}{L:License D}
variable {b:Stage W I D G}{s t u: Branch.Tag b}{L:License D}
variable {d e a c:ℝ}{V: κ→ Raw D I}
namespace Vista
lemma infinite[Nonempty κ] (F:ℕ→ κ→Raw D I)(T:ℕ→ℝ)(h:∀ i,Vista L s t (F i) (T i) a)(p:Summable T)(hp:0 ≤ a): Vista L s t (fun i x=> ∑' n,F n i x) (∑' n,T n) a:=by
 choose K Q H U W' using h
 have hl n S i j:0≤Q n S i j:= (H n S|>.1 (Classical.arbitrary κ)).nonn ..
 have he S i j: Summable fun n=> Q n S i j:= p.of_nonneg_of_le (fun _=>hl ..) (fun k=> (U k).price hp (hl k) S i j)
 have hm S d x : Summable fun n=> K n S d x:= kernel_sum _ fun i j=> ((he S i j).of_nonneg_of_le (fun _=>norm_nonneg _) (fun n=>((H n S|>.1 d).expo i j).bounded x)).of_norm
 let V(S:Seal W)(i j:I):= ∑' n,Q n S i j
 have hk i j:saleM a V i j=∑' n,saleM a (Q n) i j:=by
    simp_rw [saleM]; rw [Summable.tsum_finsetSum (f:=fun S n=>Branch.rent a S*Q n S i j)]; unfold V; simp_rw [tsum_mul_left]
    intro S _; exact (he S i j).mul_left _
 have hs i j:Summable fun n=>saleM a (Q n) i j:= summable_sum (s:=univ) fun S _=> (he S i j).mul_left _
 refine ⟨fun S i x=> ∑' n,K n S i x,V,fun S=>⟨fun t=>suite_ts _ _ (fun i=>(H i S).1 t) (he S),fun i=>?_⟩,⟨tsum_nonneg fun i=> (U i).posP,?_,?_⟩,fun i x=>?_⟩
 · apply continuous_matrix; intro x y; simp_rw [kernel_entry (hm _ _ _)]; exact continuous_tsum (fun n=>(H n S|>.2 i).matrix_elem x y) (he S x y) (fun n d=> ((H n S|>.1 d).expo ..).bounded _) -- tune
 · intro i; simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun j n=>saleM a (Q n) i j) (hf:=fun j _=> hs i j)]; exact (summable_sum (fun j (_:j∈(univ:Finset I))=>hs i j)).tsum_le_tsum (fun n=>(U n).rows i) p
 · intro j; simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun i n=>saleM a (Q n) i j) (hf:=fun i _=>hs i j)]; exact (summable_sum (fun i (_:i∈(univ:Finset I))=>hs i j)).tsum_le_tsum (fun n=>(U n).cols j) p
 dsimp only; simp_rw [W']; rw [Summable.tsum_finsetSum (fun i _=>hm i _ _)]
lemma impose(h:Vista L s t V d a) (f:D→D)(hp:Continuous f) (e:∀ g d,f (b.drive g d) = b.drive g (f d))(hq:∀S x y,b.eval S (f x) (f y)=b.eval S x y)(hk:∀ g:D→ℂ,L.valid g→L.valid (fun x=> star (g (f x)))): Vista L t s (fun i x=> star (V i (f x))) d a:=by
 obtain ⟨K,Q,H,p,h⟩:=h
 refine ⟨fun S i x=>star (K S i (f x)),_,fun S=>⟨fun i=>⟨?_,fun j k=> hk _ (H S|>.1 i|>.fuel k j)⟩,fun _=>(H S|>.2 _).star⟩,p.flip,fun i x=>by dsimp only;rw [h,star_sum]⟩
 have hT:Ticket s t S (Q S) (fun x=> K S i (f x)):=by
      refine ⟨fun g x=> by rw [e]; exact (H S|>.1 i).frame ..,fun a b'=>?_⟩
      have hx:=(H S|>.1 i).expo a b'; exact ⟨hx.positive,hx.triggered,fun x=>hx.bounded _,fun x y=> (hx.variation (f x) (f y)).trans_eq (by rw [hq]),hx.connected.comp hp⟩
 exact hT.starT
-- analytics sums exp-1-z.Iota
lemma expo [Nonempty κ] (h: Vista L s s V d a)(hp:0≤d)(hc:d≤1/4)(q:0 ≤ a): Vista L s s (fun i x=> exp (V i x)-1-V i x) (16*Real.exp a*d^2) a:=by
 let C (i:ℕ):=Real.exp a*(1/2:ℝ)^i*(2*d)^2; have hg:Summable C:= ((summable_geometric_of_lt_one (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)).mul_left _).mul_right _
 have hk:∑' i,C i ≤16*Real.exp a*d^2:=by unfold C; rw [tsum_mul_right,tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; nlinarith [Real.exp_pos a]
 let F(j:ℕ)(i:κ)(x:D):Op I:= ((j.factorial:ℂ)⁻¹) • V i x^j
 rw [show (fun i x=> exp (V i x)-1-V i x)=fun i x=> ∑' j:ℕ,F (j+2) i x from ?_];
 swap; · funext i x; have h : Summable fun j=> F j i x:= (norm_expSeries_summable' (𝕂:=ℂ) (V i x)).of_norm
         rw [exp_eq_tsum ℂ]; change (∑' j,F j i x)-1-V i x=_; rw [← h.sum_add_tsum_nat_add 2, sum_range_succ,sum_range_succ]; simp [F,add_comm (2:ℕ)]; abel
 refine (infinite _ C (fun i=>?_ ) hg q).tall hk; apply ((h.slug q (i+2)).scaleC _).tall; unfold C; calc
    _ ≤ 1*(Real.exp a*((1/2:ℝ)^i*(2*d)^2)):=by rw [pow_add]; gcongr <;>first| positivity |linarith| rw [norm_inv,Complex.norm_natCast]; apply inv_le_one_of_one_le₀; exact_mod_cast (Nat.factorial_pos (i+2))
    _ = _:=by ring
lemma icicle [Nonempty κ] (h:Vista L s s V d a)(hp:0≤ d)(hc:d≤1/4)(q:0≤a): Vista L s s (fun i x=>(1+V i x)⁻¹-1) (16*Real.exp a*d) a∧ Vista L s s (fun i x=> Branch.pencil (V i x)) (16* Real.exp a*d) a:=by
 let F(i:ℕ):=Real.exp a*(2*d)*(1/2:ℝ)^i; have hg : Summable F:= (summable_geometric_of_lt_one (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)).mul_left _; have hf:∑' i,F i≤16*Real.exp a*d:=by unfold F; rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; nlinarith [Real.exp_pos a]
 have hx(i:ℕ):Real.exp a*(2*d)^(i+1)≤ F i:=by unfold F; rw [pow_succ',←mul_assoc]; gcongr; linarith
 constructor
 · rw [show (fun i x=>(1+V i x)⁻¹-1)=fun i x=>∑' j:ℕ,(-(V i x))^(j+1) from ?_]; swap
   · funext i x; have he:= (h.stem i).lib.boundOp q x; let U:= -(V i x); have hu:‖-(V i x)‖<1:=by rw [norm_neg]; linarith
     rw [←sub_neg_eq_add 1 (V i x), ← route_inv hu, ← (summable_geometric_of_norm_lt_one hu).sum_add_tsum_nat_add 1]; simp
   exact (infinite _ F (fun i=>(h.neg_m.slug q (i+1)).tall (hx i)) hg q).tall hf
 unfold Branch.pencil; refine (infinite _ F (fun i=>?_) hg q).tall hf
 have he:= (h.slug q (i+1)).scaleC (bcoef i:ℂ); rw [Complex.norm_real] at he; simp_rw [Complex.coe_smul] at he; apply he.tall; exact (mul_le_of_le_one_left (by positivity) (bc_norm _)).trans (hx i)
end Vista
end
end YM.CF.Exa
