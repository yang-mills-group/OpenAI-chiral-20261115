import YM.SU5.Thin.Glacier.Hilltop
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)
variable {N:Finset (Cell n)} {τ κA ψ:ℝ}
variable (I:ArcChill J R q p r.count.val m β κ ξ v Λ τ κA ψ) (g0:2*(r.count.val+1)<n.val)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
variable (Q':0 ≤ z') -- z' reserve coefficient per unit universal wall
variable {κ' : ℝ}
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)

variable (g:0<β)(d:0≤ κ')(l:0≤ C)
lemma reckonN (τ:ℝ)(ι:Type*)[Fintype ι] : (∑ N:Finset ι,Real.exp (-τ*N.card))≤ Real.exp (Real.exp (-τ) * Fintype.card ι):=by
 have h(N:Finset ι): Real.exp (-τ*N.card)= ∏ i∈N,Real.exp (-τ):=by rw [mul_comm, Real.exp_nat_mul, prod_const]
 simp_rw [h]; let E:=Real.exp (-τ); rw [show Real.exp (-τ) * ↑(Fintype.card ι)=(Fintype.card ι:ℝ)*E from mul_comm ..,Real.exp_nat_mul]
 refine (le_of_eq ?_) |>.trans (pow_le_pow_left₀ (show 0 ≤ E+1 by unfold E; positivity) (Real.add_one_le_exp _) _); simpa only [prod_const,card_univ,mul_one, prod_const_one,one_pow] using (Fintype.prod_add (fun (_:ι)=>E) (fun _=>1)).symm
include B P L D I d g j wH uH Q'
include u h1 h2 a he g0 l
lemma ice_canyon (pH:4*descendCost J β κ' z'*(r.count.val:ℝ)^4 ≤ ξ) {d₀:ℝ}(hS:4*descendCost J β κ' z'*speckCount (hallBill m)+d₀ ≤ ψ) (Hx:GaugeInvariant φ) (v':∀ (A:Support c)(N:Finset (Cell n)), RimScene B P p r m β v (Q+z'*fritTrap r m A N) τ A N t φ W): (∫ U:Config G n,heatG Z q p β κ κA τ U*Real.exp (t*φ U)∂prior G n) ≤ Real.exp (Roof J β n H + rentRoom r R q m p β v η C S Λ (descendCost J β κ' z') + Q + plumeCost B P W t + trend*b₂^2*t^2 + Real.log 2*(Fintype.card (Site c):ℝ)+Real.exp (-d₀) * Fintype.card (Cell n)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T; let D':= descendCost J β κ' z'
 let X:= fun U:Config G n=> heatG Z q p β κ κA τ U*Real.exp (t*φ U); change (∫ U,X U∂_) ≤ _; have H1:Envelope X:= (heat_env B).mul (expEnv u _); have h':= heat_inv (β:=β) (d:=κ) (κA:=κA) (v:=τ) (p:=p) (n:=n) B; rw [T.pack _ (H1.integrable _) (fun k y U=> by unfold X; rw [Hx,h' k])]; let U0:= Roof J β n H+rentRoom r R q m p β v η C S Λ D' + Q + plumeCost B P W t + trend*b₂^2*t^2; let F'(A:Support c)(N:Finset (Cell n)):= playN Z q p A N T β κ κA τ t φ
 have hp(A:Support c)(N:Finset (Cell n)) : (∫ x,F' A N x ∂T.order G)≤ Real.exp (U0-d₀*N.card) := by
    let p':=(qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩); have hg:= highCore (N:=N) (W:=W) (Q:=Q) (b₂:=b₂) (t:=t) (K':=p') B P L D I Q' j wH uH g d A h hS pH
    apply le_trans _ hg.2
    exact coreBound B P L D I g0 u a h1 h2 A hg.1 g l (fun ⦃i⦄ p=> hall_prop.mpr ⟨mem_univ i,(hall_prop.mp p).2⟩) (v' A N)
 have eqA(x:T.Slice G): X (T.drape x)=∑ i: Support c,∑ N:Finset (Cell n),F' i N x:=by
    unfold F' X playN; simp_rw [← sum_mul]; unfold icing; simp [ite_and]
 rw [funext eqA,integral_finsetSum]; swap; · exact fun i _=>integrable_finsetSum _ (fun n _=> (env_playN B u i n t).integrable _)
 have h(A:Support c): (∫ x, (∑ i,F' A i x) ∂T.order G)=∑ i, (∫ x,F' A i x ∂T.order G):= integral_finsetSum _ fun i _=> (env_playN B u A i t).integrable _
 simp_rw [h]
 let K:= Real.exp (Real.exp (-d₀) * Fintype.card (Cell n))
 refine le_trans (sum_le_sum (g:=fun _: Support c=> Real.exp U0*K) (fun b _=>?_)) (le_of_eq ?_)
 · apply (sum_le_sum (s:=univ) (fun i _=>hp b i)).trans; simp_rw [sub_eq_add_neg U0, Real.exp_add U0, ←neg_mul]; -- `rhs` works sum? test
   rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (reckonN d₀ (Cell n)) (Real.exp_pos _).le
 change _= Real.exp ((U0 + Real.log 2*Fintype.card (Site c)) + _)
 rw [sum_const,nsmul_eq_mul,card_univ,Real.exp_add (U0 + Real.log 2*(Fintype.card (Site c):ℝ)),Real.exp_add U0,mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num)]; unfold Support; simp only [Fintype.card_finset]; push_cast; unfold K; ring

end YM.Gleam