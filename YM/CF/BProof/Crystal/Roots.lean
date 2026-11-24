import YM.CF.BProof.Crystal.Cutter
/-! rootK quantitative version for actual alpha→0, using FiniteGaugeData cluster lemmas.
Separate to support arbitrary functions inclusive of measure fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Sprinkle Lattice Tenant Palot Gas Branch RG Push.AbsoluteSums Trees Ursell
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]{P:Dew V I}
namespace Roots
variable {N:Side}{v:Y N→ℝ} {α C:ℝ} (a:0<α)(c:0<C)
-- rates α raw, α/2 intermediate, α/4 final
variable {X:V→Y N} {f: Finset V→ℂ}{w:V→ℝ} (p:Moment.Toll (stern ∘ X) w α C)(u:∀ i,w i≠0→ Grove (terr N) (X i).val)
def mild(α C:ℝ):Prop:= 64*C≤ α
include a c p u
theorem raw(h:mild α C) : Ready (fun i=>(X i).val) 0 w (α/2) C (α/2) (1/2):=by
 have hc':0<C:=c; have hx:p=p:=rfl; refine ⟨c,div_pos a (by norm_num),?_,by norm_num,p.nonneg, ticket u p.nonneg ?_⟩; · unfold degreePrice Trees.stretch; norm_num [Animals.ballCost]; unfold mild at h; field_simp; linarith -- tune
 rw [add_halves]; exact (tollPrice _ p.nonneg _ _).mp p -- tune
lemma coin (h:mild α C):Moment.Toll stern (CoinX X w) (α/2) (2*C):=by
 have he:= raw a c p u h; apply (tollPrice _ (fun i=>sum_nonneg (fun _ _=> bigA _ p.nonneg)) _ _).mpr; intro x; apply le_trans (starts u he (by linarith : 0 ≤ α/2) x); norm_num; linarith
lemma inc(h:mild α C): Ready stern 0 (CoinX X w) (α/4) (2*C) (α/4) (1/2):=by
 refine ⟨mul_pos (by norm_num) c, div_pos a (by norm_num), ?_, by norm_num,(coin a c p u h).nonneg, ticket (coin_heat w u) (coin a c p u h).nonneg ?_ ⟩; · unfold degreePrice Trees.stretch; norm_num [Animals.ballCost]; unfold mild at h; field_simp; linarith
 rw [show α/4+α/4=α/2 from by ring]; exact (tollPrice _ (coin a c p u h).nonneg _ _).mp (coin a c p u h)
abbrev price (X:V→Y N)(w:V→ℝ) : Y N→ℝ:= sumTax (CoinX X w)
lemma tariff (h:mild α C): Moment.Toll stern (price X w) (α/4) (4*C):=by
 let W:= CoinX X w; have he:= inc a c p u h; have hp:= (coin a c p u h).nonneg; apply (tollPrice _ (fun i=>tsum_nonneg ?_) _ _).mpr -- tune h implicit
 · intro x; apply le_trans (taxesC he (by linarith : 0 ≤ α/4) x); norm_num; linarith
 intro i; unfold wageA; split; exact clusters_nonneg _ hp _; rfl
lemma connect (h:mild α C)(i:Y N)(v:price X w i≠0): Grove (terr _) i.val:=by
 by_contra f; apply v; refine Eq.trans (tsum_congr (g:=fun _=>0) ?_) tsum_zero; intro z; unfold wageA; split; rename_i g
 · by_contra hv; unfold clusters at hv
   apply f; have ht: coefficient gRule z.2 ≠0:= by intro j; apply hv; simp [j]
   rw [g]; apply ζlink z ht; intro j; apply coin_heat w u; intro k; apply hv; rw [prod_eq_zero (mem_univ j) k,mul_zero,zero_div]
 rfl
omit a c p u
lemma unionSafe {X:V→Y N}{U: Finset V}{S:Y N}(h:U∈ slateF X S)(i:V)(g:i∈ U) : (X i).val ⊆ S.val:=fun _ t=> coverB h ▸ mem_biUnion.mpr ⟨i,g,t⟩
def cents(X:V→Y N)(f: Finset V→ℂ)(S:Y N):ℂ:= jingle (bankB X f) S
variable (h:mild α C) (g: ∀ S,‖f S‖≤∏ i∈S,w i)
include g
lemma safeB(i:Y N):‖bankB X f i‖≤CoinX X w i:=by rw [bank_p]; exact (norm_sum_le ..).trans (sum_le_sum (fun i _=>g i))
include a c p u h
theorem chit(free:Yard X f): (∑ i,f i)=Complex.exp (∑ i:Y N,cents X f i):=Eq.trans (armed f free (safeB g) (by linarith : (0:ℝ)≤α/4) (inc a c p u h)) (congrFun Complex.exp_eq_exp_ℂ _).symm -- name
omit a c p u h in
lemma syrup(i: Y N)(z:Clusters (Y N)): ‖(if i=tideU z then guava gRule (bankB X f) z else 0)‖≤ wageA z i (CoinX X w):=by
 unfold wageA; split; · unfold guava clusters; rw [norm_smul,norm_prod, norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (show (0:ℝ)≤(z.1+1).factorial by positivity), ←mul_div_right_comm]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>safeB g _)) (abs_nonneg _)) (Nat.cast_nonneg _)
 rw [norm_zero]
lemma charge(i:Y N): ‖cents X f i‖≤price X w i:=by
 have he:=τ_w i (inc a c p u h) (by linarith); have hp:= he.of_nonneg_of_le (fun i=>norm_nonneg _) (syrup (X:=X) g i); exact (norm_tsum_le_tsum_norm hp).trans (Summable.tsum_le_tsum (syrup g i) hp he)
omit g a c p u h
lemma outflow(X:V→Y N)(i:Y N){f g: Finset V→ℂ} (e:∀ Z:Finset V,(∀ k∈Z,(X k).val ⊆ i.val)→ f Z=g Z) : cents X f i=cents X g i:=by
 unfold cents jingle; apply tsum_congr; intro z; split; rename_i h; · unfold guava; congr 1; apply prod_congr rfl; intro j _; rw [bank_p,bank_p]; exact sum_congr rfl (fun S s=> e S (fun k t=> (unionSafe s k t).trans (h.symm ▸ κc z j)))
 rfl
lemma meas {D:Type*}[MeasurableSpace D](f:D→ Finset V→ℂ)(g:∀ i,Measurable fun x=> f x i)(S:Y N)(X:V→Y N): Measurable (fun x=>cents X (f x) S):=by
 unfold cents jingle; apply Measurable.tsum; intro i; split; unfold guava; simp_rw [bank_p]; fun_prop; exact measurable_const
variable {D:Type*}[TopologicalSpace D](F:D→Finset V→ℂ)
include a c p u h in
lemma continuity(g:∀ x i,‖F x i‖≤∏ j∈i,w j)(b:∀ i,Continuous (fun x=> F x i))(S:Y N): Continuous (fun x=>cents X (F x) S):=by
 unfold cents jingle; refine continuous_tsum ?_ (τ_w S (inc a c p u h) (by linarith)) (fun z x=>syrup (g x) S z); intro z; split; unfold guava; simp_rw [bank_p]; fun_prop; exact continuous_const
end Roots
end YM.CF.BProof.Crystal
