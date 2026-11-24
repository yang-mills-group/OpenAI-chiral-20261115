import YM.SU5.FiniteGaugeData.Largo.Luna
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Tulip
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable (o:Rim) (p:Slab o) {x:Momentum}{a:ℝ} (k:SpinIdx)
/- Frieze symbol = restricted only along time, same stencil, ignores all other inputs. Enters standard cart. Cube analytic via projecting to fixed tangent p first, rail overlap & real-firm purchase. -/
def plainL (p:Rim)(z: Momentum): Momentum:= full (fun i:Tang=>(p i:ℂ)) (z 3)
lemma firm_real (t:ℝ): plainL o (tmap (full o t))=tmap (full o t):=by unfold plainL; funext i; fin_cases i <;> rfl
private lemma firm_t (x:Momentum): plainL o x= Function.update (floorPin o 0) 3 (x 3):=by funext i; fin_cases i <;> rfl
lemma semblance (q:physical x): physical (plainL o x):=by rw [physical_iff]; intro i; fin_cases i <;> first| rfl | exact (physical_iff x).mp q 3
lemma plane_D : Differentiable ℂ (plainL o):=by unfold plainL; apply differentiable_pi.mpr; intro i; fin_cases i <;> first| exact differentiable_const _ | exact (differentiable_apply (𝕜:=ℂ) (i:=(3:Axis)))
lemma firm_cash(x:Momentum)(v:Cover): plainL o (x+reciprocal v)=plainL o x+reciprocal (full (fun _=>0) (v 3)):= by
 simp_rw [firm_t]; funext i; by_cases h:i=3; · simp [h,reciprocal, full_last]
 have he: full (fun _:Tang=> (0:ℤ)) (v 3) i=0:=by fin_cases i <;> first| rfl| exfalso; apply h; rfl
 simp [Function.update_of_ne h, reciprocal,he]
include p
private lemma pt_low {i:Tang}: |o i| ≤ Real.pi:= (abs_le.mpr ⟨by have h:=p i; linarith [Real.pi_gt_three],by have h:=p i; linarith [Real.pi_gt_three]⟩)
private lemma cuber (u:0<a) (H:x∈ cube a): plainL o x∈ cube a:= by
 have hx:floorPin o 0 ∈ cube a:= mem_cube_real (base_subset_realCube u (town_quote o p (by rw [abs_zero]; exact Real.pi_pos.le))) u
 rw [firm_t]; constructor <;> intro i <;> by_cases h:i=3
 · rw [h, Function.update_self]; exact H.1 _
 · rw [Function.update_of_ne h]; exact hx.1 i
 · rw [h,Function.update_self]; exact H.2 _
 rw [Function.update_of_ne h]; exact hx.2 i
lemma trimL (h:x∈baseCube): plainL o x∈ baseCube:= by
 refine ⟨semblance o h.1,?_⟩; rw [firm_t]; intro i; by_cases u:i=3; · rw [u,Function.update_self]; exact h.2 _
 rw [Function.update_of_ne u]; exact (town_quote o p (by rw [abs_zero]; exact Real.pi_pos.le)).2 i
lemma box_quote (h:x∈realCube a)(v:0<a): plainL o x∈ realCube a:=⟨semblance o h.1,(cuber o p v (mem_cube_real h v)).2⟩ -- remove h implicit
omit p
variable (M:Tulip.Male)(S:Momentum) (V:ℕ)
def shineF (f:Momentum→Momentum): Momentum→Op SpinIdx:=fun z=> -zen (f z)
def stairF(V:ℕ) (o:Rim)(M:Tulip.Male)(v:Momentum):Momentum:= (shell V M.val (plainL o v))⁻¹ • (skin V M.val (plainL o v))
-- sap lower price. need domain where complex symbol may be used on THICK slab with h ≤ zone. real needed for overlapping to exactly mix. `tub`. 
include p
lemma coast_reel (he:x∈realCube zone)(l:1≤V):stairF V o M x=mixL V M.val (plainL o x) :=by
 unfold stairF; let v:=plainL o x; let z:=(box_quote o p he zone_pos); rw [skin_mix _ _ z, inv_smul_smul₀ _]; rw [shell_inv _ _ z]; apply inv_ne_zero (graphs_ne (phys_mix _ M.val M.property _ z.1));
 intro a; have he:= congr_fun a (0:Axis); apply not_le_of_gt (show 0 < o 0 from zero_lt_one.trans_le (p 0).1); exact le_of_eq (ofReal_eq_zero.mp he)
omit p
variable {X:Type*} {F:X→Momentum→ℂ}{q:X→Rim}(h: ∀ i, Slab (q i))(m:X→Male)
include h
lemma fireHire (P: Moderate (fun _:X=>1) F): Moderate (fun _:X=>1) (fun i x=> F i (plainL (q i) x)):=by
 obtain ⟨η,C,u,e,g⟩:=P; exact ⟨η,C,u,e,fun i=> ⟨fun x p=> ((g i).hol _ (cuber (q i) (h i) u p)).comp _ (plane_D (q i) _), fun x p=> (g i).bound _ (cuber _ (h i) u p)⟩⟩
lemma fireHost (u:1≤V): Firm (fun _:X=>1) (fun i x=> shell V (m i).val (plainL (q i) x)):=by
 obtain ⟨a,b,h₁,h₂,W⟩:= Jill.zip u; refine ⟨zone,a,zone_pos,h₁,fun i x t=> ?_⟩; let v:= inside x; let p:= plainL (q i) v; have hz: p∈baseCube:= trimL (q i) (h i) (inside_base t.1); have hQ:=box_quote _ (h i) t zone_pos
 let P:= plainL (q i) x; let Q:= fun j:Axis=> (p j).re; have he: tmap Q=p:= pq p hz.1 -- tune
 have hG:(‖Q‖:ℝ)≥1:=by refine (norm_le_pi_norm Q (0:Axis)).trans' ?_; rw [Real.norm_eq_abs, show Q 0=q i 0 from rfl]; exact (h i 0|>.1).trans (le_abs_self _)
 have hx: ‖Q‖ ≤ Real.pi:= (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 (fun j=> hz.2 j); have hr:a ≤ ‖shell V (m i).val p‖:=he ▸ ((W _ Q hx).1.trans' (by nlinarith only [hG,h₁,sq_nonneg (‖Q‖-1), one_le_pow₀ hG (n:=2)] )) -- placeholder
 let T:=full (fun _=>0) (relift x 3); have hk:p=P+reciprocal T:= firm_cash (q i) x (relift x)
 rw [hk, shell_overlap _ _ P hQ T (hk ▸ base_subset_realCube zone_pos hz)] at hr; simpa using hr
lemma fireEarn (u:1 ≤ V): Pay (fun _:X=>1) fun i v=> shineF (stairF V (q i) (m i)) v:= by
 have he: ∀ a:Axis, Moderate (fun _:X=>1) (fun i x=> stairF V (q i) (m i) x a):= by
    intro a; let F:= fireHire h (skinPay V u (fun i=> (m i).val) (fun i=> (m i).property) a); let H:= (fireHire h (shellPay V u (fun i:X=> (m i).val) (fun i=> (m i).property))).inv (fireHost V h m u) (fun i=> zero_lt_one)
    convert! H.mul F using 1; · simp
 let K:=zenBudget (ι:=X) (fun _=>zero_le_one) _ he; exact ⟨fun _=>zero_le_one,fun i j=>(K.tap i j).neg⟩
omit h
open Rush
structure Ream (A:Momentum→Op SpinIdx)(σ C:ℝ):Prop where
 reserve : Laurent.Width σ C (tub A)
 foe : Rush.Reads (tub A) A
lemma reamS{F:X→Momentum→ Op SpinIdx}(Q:Pay (fun _=>1) F)(h:∀ i p, p∈realCube zone→∀ x,p+reciprocal x∈realCube zone→ F i (p+reciprocal x)=F i p): ∃ σ C:ℝ,0<σ ∧ 0<C ∧ ∀ i, Ream (F i) σ C:=by
 obtain ⟨⟨c,C,b,t,T⟩,R⟩:=tub_bill Q h; refine ⟨c,16*C,b,by positivity,fun i=> ⟨?_,Rush.paid Q h _⟩⟩; simp only [mul_one] at T; let f:= F i; let A(x):= tub f x; let D:=T i; let g(x:Cover):=Real.exp (c*Laurent.size x); let v(l:SpinIdx)(j:SpinIdx)(x:Cover):= g x*‖A x l j‖
 let V(z:Cover):=∑ i:SpinIdx,∑ j:SpinIdx,v i j z; have hs(i j):Summable (v i j):=(T _ i j).2.1; let K:=summable_sum (s:=(univ:Finset SpinIdx)) fun i _=> summable_sum (s:=(univ:Finset SpinIdx)) fun j _=> hs i j; have hk(x:Cover): g x * ‖tub (F i) x‖ ≤ V x:= by
    unfold V v; simp_rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; let Z:= A x; apply Branch.schur (fun i j=>‖Z i j‖) _ _ (by positivity) (fun i j=>le_rfl); · intro a; exact Finset.single_le_sum (f:=fun i => ∑ j:SpinIdx,‖Z i j‖) (fun i _=>by positivity) (mem_univ _)
    intro j; rw [sum_comm]; apply Finset.single_le_sum (f:=fun j=> ∑ i:SpinIdx, ‖Z i j‖) (fun _ _=>by positivity) (mem_univ _)
 let x:=Summable.of_nonneg_of_le (fun i=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hk K; refine ⟨fun i=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _), x,(x.tsum_le_tsum hk K).trans ?_⟩; change (∑' i,V i)≤_; unfold V; rw [Summable.tsum_finsetSum _]; swap; · intro i _; exact summable_sum fun j _=>hs i j
 simp_rw [Summable.tsum_finsetSum (fun i _=> hs _ i)]; exact (sum_le_sum (fun i _=>sum_le_sum (fun j _=> (T _ i j).2.2))).trans_eq (by simp; ring)
lemma pull_bar : ∃ σ C:ℝ, 0<σ∧ 0<C∧ ∀ m:Male,Ream (bar 4 m.val) σ C:= reamS (barBudget 4 (by omega) (fun i:Male=>i.val) (fun i=>i.property)) fun i _ x z h=>bar_overlap _ _ x z h
include h in
lemma blastOff (u:1 ≤ V) : ∃ σ C:ℝ, 0<σ ∧ 0<C∧ ∀ i:X, Ream (shineF (stairF V (q i) (m i))) σ C:=by
 refine reamS (fireEarn V h m u) ?_; intro i x t z s; rw [shineF,shineF,coast_reel (q i) (h i) _ V t u,coast_reel (q i) (h i) _ V s u, firm_cash,mix_period]
lemma dairy : ∃ σ C:ℝ,0<σ∧0<C∧∀ (v:Rim) (_e:Slab v)(m:Male), Ream (shineF (stairF 4 v m)) σ C:=by
 obtain ⟨σ,C,t,h,V⟩:=blastOff 4 (X:= Male × {x:Rim// Slab x}) (q:=fun i=>i.2.1) (fun i=>i.2.2) Prod.fst (by omega); exact ⟨σ,C,t,h,fun i p m=>V (m,⟨i,p⟩)⟩
end YM.CF.Window.Largo
