import YM.SU5.Gleam.Prince
/-! # Blocking permissions with width-independent thresholds when right width choice made. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
local notation "B" x:max=> (height x:ℝ)
def soot (L:ℕ)(v x:ℝ):= 4* (v* B x)*(L:ℝ)^4
lemma soothe (k:Clip)(R:Rules G)(D:LocalRatio J)(κ A e:ℝ)(h:0 ≤ A)(g:0<e)(L: Side):∀ᶠ x:ℝ in atTop,∀ w:ℕ, moder (height x) w L → ∀ (b:ℝ) (p:BudgetPoint), x/2≤ b → p.threshold=temp x → Archive J R k p w (height x) b κ (soot w A x) (pace L x) e:=by
 let Z:= k.linear/2; let X(x:ℝ):= (height x:ℝ); have hZ:0 < Z:= half_pos k.tail_pos
 let a:=4*A*(L.val:ℝ)^4; let d:= |κ|+21^4*a; have hd:0≤d:=by unfold d a; positivity
 have he:Real.exp e >1:= by rw [gt_iff_lt,← Real.exp_zero]; exact Real.exp_lt_exp.mpr g
 obtain ⟨r,hr,t⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp (((D.germ 0 (Metric.mem_ball_self D.patch)).continuousAt.tendsto).eventually (ge_mem_nhds (show J.J 0 < Real.exp e from (D.anchored.symm ▸ he))))
 have hf:Tendsto (pace L) atTop (𝓝 0):=by simpa using heel L 0
 filter_upwards [eventually_gt_atTop 0, dust_money 13 (d/Z) (by positivity), parliament (G:=G) k, pace_le L, hf.eventually (ge_mem_nhds (show 0<R.c from R.radius)), hf.eventually (gt_mem_nhds (half_pos D.patch)), hf.eventually (ge_mem_nhds (half_pos hr)), Work.E08.eventual_radiusB 1] with x hx u m t' v V r' hh
 intro w H b p z e'
 have hw:(w:ℝ)≤ L.val* X x ^ 3:= by unfold X; exact_mod_cast H.2
 have hv:soot w A x≤ a* X x^13:=by
    unfold soot; refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hw _) (by positivity:0 ≤ 4*(A*B x))).trans_eq ?_; unfold a X; ring
 refine ⟨m _ e',(e'.symm ▸ t' w H),v,(by linarith only [V]),fun u h=> t (Metric.mem_closedBall.mpr (show dist u 0 ≤ _ from (dist_zero_right _).trans_le (h.trans (by linarith only [r'])))),?_,by unfold soot; positivity,g.le⟩
 rw [e']; calc
 _ ≤ |κ| +21^4*(a* X x^13) := by gcongr; apply le_abs_self
 _ ≤ d* X x^13:=by unfold d; rw [add_mul,mul_assoc ((21:ℝ)^4)]; apply add_le_add_left; exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (Nat.one_le_cast.mpr hh))
 _ ≤ (x/2)*(k.linear*temp x^2):=by unfold X; have he:=mul_le_mul_of_nonneg_left u hZ.le; rw [← mul_assoc,mul_div_cancel₀ d hZ.ne'] at he; unfold Z at he; linarith only [he]
 _ ≤ _ := by have hp:= k.tail_pos; gcongr
-- boundary fraction. stronger growth cubic in block side, linear in bill.
lemma wall_cheap {w d:ℕ}(h:Odd w)(k:d ≤ w/2): (largerBill w d:ℝ) ≤ 8*(d:ℝ)*(w:ℝ)^3:=by
 let P:= (w/2-d)*2+1; have ht:P+2*d=w:=by unfold P; obtain ⟨v,e⟩:=h; omega
 have hp:P ≤ w:=by omega
 have hz:(P:ℝ) ≤ w:=by exact_mod_cast hp
 have he:(w:ℝ)-P=2*d:= sub_eq_iff_eq_add.mpr (by exact_mod_cast ((by omega) : w= 2*d+P))
 rw [show largerBill w d=w^4-P^4 from rfl, Nat.cast_sub (Nat.pow_le_pow_left hp _),Nat.cast_pow,Nat.cast_pow]
 let F:ℝ:= P; let M:ℝ:=w; have hv0:0 ≤ M:=by unfold M; positivity
 have hp0:0 ≤ F:=by unfold F; positivity
 calc
 _ =(M-F)*(M^3+F*M^2+F^2*M+F^3):=by unfold F M; ring
 _ ≤ (M-F)*(M^3+M*M^2+M^2*M+M^3):= by change F ≤ M at hz; have hj:=sub_nonneg.mpr hz; gcongr
 _ = _:= by rw [show M-F=2*(d:ℝ) from he]; unfold M; ring
lemma taller (A:ℝ)(L:Side)(e:ℝ)(t:0≤ A)(h:0 < e): ∀ᶠ x:ℝ in atTop,∀ w:ℕ,Odd w → moder (height x) w L → let E:= hallBill (height x); E≤ w/2 ∧ 4*(A* B x)*(largerBill w E) + Real.log 2 ≤ e*(w:ℝ)^4:=by
 obtain ⟨d,hp⟩:= exists_nat_gt ((128*A+Real.log 2)/e); filter_upwards [Work.E08.eventual_radiusB d,Work.E08.eventual_radiusB 10] with x hx hD w g k E; let b:=height x; let V:=B x; let M:ℝ:= w
 have ht : E≤4*b:= by unfold E hallBill Sequest; change 10≤b at hD; omega
 have hf:E≤w/2:=by
    have hv:b^3≤ w:= k.1; have hg:10 ≤ b:=hD; have hj: 8*b ≤ b^3:=by nlinarith only [hg, mul_le_mul_right' (Nat.pow_le_pow_left hg 2) b]
    omega
 have hv: V^3≤M:=by unfold V M; exact_mod_cast k.1
 have hB:1 ≤ V:= by have hm:=Nat.cast_le (α:=ℝ).mpr hD; push_cast at hm; exact le_trans (by norm_num : (1:ℝ)≤10) hm
 have hl:1≤ M:= le_trans (one_le_pow₀ hB) hv
 have hK:4*(A*V)*(largerBill w E) ≤ 128*A*V^2*M^3:=by
    refine (mul_le_mul_of_nonneg_left (wall_cheap g hf) (by positivity : 0≤4*(A*V))).trans ?_; have hi : (E:ℝ)≤4*V:=by unfold V; exact_mod_cast ht -- unfold V first
    apply le_trans (b:=4*(A*V)*(8*(4*V)*M^3)) ?_ (le_of_eq (by ring)); gcongr
 refine ⟨hf,?_⟩; let m:=Real.log 2; have hm:0≤ m:=Real.log_nonneg (by norm_num); have hw:(d:ℝ)≤V:= by unfold V; exact_mod_cast hx
 have hu:128*A+m ≤ e*V:= by rw [mul_comm e]; exact (div_le_iff₀ h).mp (hp.le.trans hw)
 have he :128*A*V^2+m* V^2 ≤ e*M:=calc
        _=(128*A+m)*V^2:=by ring
        _ ≤e* V * V^2:= mul_le_mul_of_nonneg_right hu (sq_nonneg _)
        _ ≤ e*M:=by rw [mul_assoc,show V*V^2=V^3 by ring]; gcongr
 have hh : m≤ m*V^2*M^3:= (le_mul_of_one_le_right hm (one_le_pow₀ hB)).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl))
 change _+m≤ e*M^4; linarith only [he,hK,mul_le_mul_of_nonneg_right he (show 0≤ M^3 by positivity),hh]
lemma serial (k: Clip)(R: Rules G)(D:LocalRatio J)(t:ℝ)(L:Side)(p:0<η)(g:0≤C)(S:ℝ)(h:0 ≤ t)(κ e:ℝ)(r:0<e): ∀ᶠ x:ℝ in atTop, ∀ w:Side, Odd w.val → moder (height x) w.val L→ ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ (n c:Side)(R':Ratio c n),2*(R'.count.val+1)<n.val → R'.count=w → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B':Z.Bounds k η C S){μ a:ℝ}(q:Floor H k n μ a),0<μ → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ t) → (∫ U:Config G n,angBill Z k p' β κ U ∂prior G n) ≤ Real.exp (Roof J β n H + e*Fintype.card (Site n)):=by
 let u:=e/8; have he:0<u:=div_pos r (by norm_num); obtain ⟨A,hA,hX⟩:= margin_fee J D t h; filter_upwards [soothe k R D κ A u hA.le he L,hX, (shown k R L p g S).eventually (ge_mem_nhds he), eventually_gt_atTop 0,taller A L u hA.le he] with x hu hf hT hx t' w l H p' β hβ vP n c X wX wL H Z V B' μ a q h₁ d
 let v:=X.count; have he':Odd X.count.val:=(show X.count=w from wL).symm ▸ l; have ht: moder (height x) X.count.val L:=wL.symm ▸ ‹moder _ _ _›; -- ht H shadowed
 let W:= height x; let J':= pace L x; let φ:= margin J β t
 obtain ⟨hh,hM⟩:= t' v.val he' ht; have hv: φ ≤ A * B x:= hf β hβ.1 hβ.2
 refine (wide_ship B' V q D (hu _ ht _ p' hβ.1 vP) wX h ((half_pos hx).trans_le hβ.1) g (show Odd X.count.val from he') hh d h₁ ?_).trans (Real.exp_monotone ?_)
 · unfold soot; gcongr
 unfold rentRoom; let N:ℝ:= Fintype.card (Site n); let M:ℝ:=Fintype.card (Site c); let t:= largerBill v.val (hallBill W); have hz:0≤N:=by unfold N; positivity
 have hp:0≤M:=by unfold M; positivity
 have hN:N=M*(v.val:ℝ)^4:=by unfold N M v; rw [site_card,site_card,X.exact_size]; push_cast; ring
 have hu':= mul_le_mul_of_nonneg_left hM hp; have hm: taxΔ R k n p' β J' η C S W ≤ u*N:= (bill_simpl L k hβ.2 vP R g hx.le).trans (mul_le_mul_of_nonneg_right hT hz); -- tune binder r'
 rw [add_assoc]; apply add_le_add_right; change _+4*u*N + 4*φ*M*t + Real.log 2*M ≤ _; let w:ℝ:=v.val; change M*(4*(A*B x)*t+_)≤ M*(u*w^4) at hu'; have ht:= le_trans (show 4*φ*M*t ≤ M*(4*(A*B x)*t) from ?_) (le_refl _); swap; · have hh:0 ≤ (t:ℝ):=Nat.cast_nonneg _; nlinarith only [mul_le_mul_of_nonneg_left hv (show 0 ≤ M*(t:ℝ) from mul_nonneg hp hh)]
 unfold u at *; change N=M*w^4 at hN; change _+4*(e/8)*N+_ + _ ≤ e*N; nlinarith only [ht,hN,hm,hu',hz,mul_nonneg r.le hz,mul_le_mul_of_nonneg_left hN.le r.le,mul_le_mul_of_nonneg_left hN.ge r.le]
end clocks
end YM.Gleam
#print axioms YM.Gleam.clocks.serial
