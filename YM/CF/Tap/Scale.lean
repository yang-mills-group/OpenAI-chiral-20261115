import YM.CF.Tap.Motto
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open NormedSpace Matrix Tenant Branch
variable (N:Side)
-- small libs canonical
abbrev Br:(ℝ→ℝ):=fun a=> Real.exp a
private lemma bPay(a e:ℝ)(i j:SpinIdx)(V:Op Slot)(p: ∀ g:SU.E, (matter g).val*V=V*(matter g).val): Solo (N:=N) a ((Fintype.card Slot)*(Br a*‖V‖)) (fun _=>∑ b:Site N,panel (b,i) (b,j) V) e:=by
 let F(x:Site N):=(x,i); let G(x:Site N):=(x,j); let R(x:Site N):Finset (Site (More N)):={node x}; let X(b):= reed (F b) (G b) ‖V‖; have hk(b:Site N):Suite (badge _) (bail N e) (bail N e) (R b) (X b) (fun _=>panel (b,i) (b,j) V):=by
    refine panel_ticket (s:=bail N e) (t:=bail N e) (p:=fun g v=>matter (g (node v.1))) (q:=fun g v=>matter (g (node v.1))) (fun _=>rfl) (fun _=>rfl) (b,i) (b,j) (R b) ‖V‖ (fun x=>V) (.single _) (fun k=>show node b∈R b from mem_singleton_self _) (fun k=>show node b∈R b from mem_singleton_self _) (fun g x=> (p (g (node b))).symm) (norm_nonneg _) ((badge _).base V) continuous_const (fun _=>le_rfl) ?_
    intro x y; rw [sub_self,norm_zero]; exact mul_nonneg (norm_nonneg _) ((forum N e).pos ..)
 have hh:0≤Br a *‖V‖:=by unfold Br; positivity
 have hx(i j k): Branch.rent a (R i)*X i j k= reed (F i) (G i) (Br a*‖V‖) j k:=by simp [R,Branch.rent,Br,X,reed,mul_ite]
 refine Crown.absorb R _ X a (by positivity) _ hk (fun _=>rfl) (fun i=>?_) (fun i=>?_)
 · simp_rw [hx]; exact wheel F (fun a b h=> congr_arg Prod.fst h) G _ _ (fun _=>le_rfl) hh _
 simp_rw [hx]; have hx t l k : reed (F t) (G t) (Br a*‖V‖) l k= reed (G t) (F t) (Br a*‖V‖) k l:=by unfold reed; simp only [and_comm];
 simp_rw [hx]; exact wheel G (fun a b h=> congr_arg Prod.fst h) F _ _ (fun _=>le_rfl) hh _
abbrev headW (Z:Op SpinIdx)(z:Op Slot) : Op (Single N):=love N (jump (Equiv.refl _) fun _=> Z ⊗ₖ z)
def wingRent(Z:Op SpinIdx)(a:ℝ):= ∑ i:SpinIdx,∑ j:SpinIdx, (Fintype.card Slot* (Br a * ‖Z i j‖))
lemma plateV (a e:ℝ)(Z:Op SpinIdx)(z:Op Slot)(v:∀ g:SU.E,(matter g).val*z=z*(matter g).val) : Solo a (wingRent Z a *‖z‖) (fun _:Chin N=>headW N Z z) e:=by
 have hx(i j:SpinIdx):let c:= Z i j; Solo a ((Fintype.card Slot)*(Br a*‖c • z‖)) (fun _:Chin N=> ∑ b:Site N, panel (b,i) (b,j) (c • z)) e:=bPay N a e i j _ (fun g=>by rw [Matrix.mul_smul,Matrix.smul_mul,v])
 have he:headW N Z z=∑ i:SpinIdx,∑ j:SpinIdx,∑ b:Site N, panel (b,i) (b,j) (Z i j • z):=by ext ⟨⟨x,i⟩,b⟩ ⟨⟨y,j⟩,l⟩; change jump (Equiv.refl (Site N)) (fun _=>Z⊗ₖ z) (x,i,b) (y,j,l)=_; rw [jump_apply]; by_cases h:x=y <;> simp [panel,h,Matrix.sum_apply,Prod.mk_inj,ite_and] <;> grind
 rw [he]; apply Crown.books (Crown.sumK Finset.univ (f:=fun i K=> _) _ (fun i _=> Crown.sumK Finset.univ _ _ (fun j _=>hx i j))) -- tune
 unfold wingRent; simp only [sum_mul, norm_smul, mul_assoc]; exact le_rfl
lemma epay {e a u:ℝ}{Z:Op (Single N)}(p:Solo a u (fun _:Chin N=>Z) e)(v:0≤a)(k:0≤u)(h:u≤1/4): Solo a (16*Br a*u^2) (fun _: Chin N=> exp Z-1-Z) e:=by
 let C (i:ℕ):=Real.exp a*(1/2:ℝ)^i*(2*u)^2
 have hc:Summable C:= ((summable_geometric_of_lt_one (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)).mul_left _).mul_right _
 have hk:∑' i,C i ≤ 16*Br a*u^2:=by unfold C; rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; unfold Br; try norm_num; have he:=Real.exp_pos a; nlinarith
 let F(i:ℕ):Op (Single N):= ((i.factorial:ℂ)⁻¹) • Z^i
 rw [show exp Z-1-Z=∑' i:ℕ,F (i+2) from ?_]; swap
 · have h : Summable F:= (norm_expSeries_summable' (𝕂:=ℂ) Z).of_norm
   rw [exp_eq_tsum ℂ]
   change (∑' i,F i)-1-Z=_; rw [← h.sum_add_tsum_nat_add 2]; rw [sum_range_succ,sum_range_succ]; simp [F, add_comm (2:ℕ)]; abel
 apply (Crown.tsK C ?_ v hc).books hk; intro i; apply ((p.powers v (i+2)).scale _).books; unfold C
 calc
   _ ≤ 1*(Real.exp a*((1/2:ℝ)^i*(2*u)^2)):=by
     rw [pow_add]; gcongr <;> first | positivity | linarith | rw [norm_inv,Complex.norm_natCast]; apply inv_le_one_of_one_le₀; exact_mod_cast (Nat.factorial_pos (i+2))
   _ =_:=by ring
end YM.CF.Tap
