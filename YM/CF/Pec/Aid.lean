import YM.CF.Pec.Fizz
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N:Side}{a b:ℝ}
def datam(x:Orig n)(K:Dues n)(X:Cloud n):ℂ:= ∑ i,∑ j, inner ℝ (heat x (collect group X) i) (heat x (collect group X) j) • K i j
lemma datag (x:Orig n)(K:Dues n):Nacre.crystal 2 (tag x K ∘ represent) (datam x K):=by
 intro v; unfold tag datam Function.comp; simp_rw [smul_sum]; refine tendsto_finsetSum _ fun i _=>tendsto_finsetSum _ fun j _=>?_ ; have hh:= ((pulled_l x i v).inner (𝕜:=ℝ) (pulled_l x j v)).smul_const (K i j)
 refine hh.congr fun t=>?_ ; simp [real_inner_smul_left,real_inner_smul_right, pow_two,smul_smul,mul_assoc]
lemma zdata(W:Pride n): Nacre.crystal 2 (zinger W ∘ represent) (fun x=> ∑ i, datam (node i) (W i) x):=by intro x; unfold zinger Function.comp; simp_rw [smul_sum]; exact tendsto_finsetSum _ fun i _=> datag _ _ x
def diem (K:Pride n)(x:Cloud n):ℂ:= (Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, pays s (∑ i:Site n, datam (node i) (K i) (litX s x))
lemma zpark(K:Pride n): Nacre.crystal 2 (pigment K ∘ represent) (diem K):=by
 intro x; unfold pigment lexn Function.comp diem; simp_rw [roomy]; let u:= ((Fintype.card Signed):ℝ)⁻¹
 have hh(i:Signed):= ((pays i).continuous.tendsto _).comp (zdata K (litX i x))
 refine ((tendsto_finsetSum (s:=univ) fun i _=> hh i).const_smul u).congr (fun t=>?_); unfold Function.comp u; simp_rw [map_smul]; rw [← Finset.smul_sum,smul_comm ((Fintype.card Signed:ℝ)⁻¹) ((t^2)⁻¹)] -- tuning
lemma tick0(K:Pride n): ContDiffAt ℝ ω (zinger K ∘ represent) 0:=by
 apply ContDiffAt.sum (s:=Finset.univ) (f:=fun i x=> tag (node i) (K i) (represent x)); intro i _; have ht(p):ContDiffAt ℝ ω (fun x:Cloud n=> silt (node i) p (represent x)) 0:= by apply rent_f; intro e; exact (repr_m e).contDiffAt
 refine ContDiffAt.sum (s:=univ) (f:=fun p x=> ∑ j, (inner ℝ (silt (node i) p (represent x)) (silt (node i) j (represent x))) • K i p j) fun p _=> ContDiffAt.sum fun j _=> ((ht p).inner ℝ (ht j)).smul contDiffAt_const
lemma tuck(K:Pride n):ContDiffAt ℝ ω (pigment K ∘ represent) 0:=by
 refine ContDiffAt.const_smul ((Fintype.card Signed:ℝ)⁻¹) (ContDiffAt.sum (s:=univ) (f:=fun i x=>pays i (zinger K (Yg (incX i) (represent x)))) fun i _=> ?_); let L:= AnalyticNext.QuarticMatch.Joint.shifts (G:=group) i (0:Orig n); simp_rw [Ywin, ←AnalyticNext.QuarticMatch.Joint.rep_shifts]; exact (pays i).contDiff.contDiffAt.comp 0 ((show ContDiffAt ℝ ω (zinger K ∘ represent) (L 0) by rw [map_zero]; exact tick0 K).comp 0 L.contDiff.contDiffAt)
lemma tagP (K T:Dues n)(x:Orig n):datam x (K+T)=datam x K+ datam x T:=by funext p; simp only [datam,Pi.add_apply,smul_add,sum_add_distrib]
lemma stemF(K T:Pride n): pigment (K+T)=pigment K+pigment T:=by funext x; simp only [pigment,lexn,zinger,tag, Pi.add_apply,sum_add_distrib,smul_add,map_add]
lemma stemR(K T:Pride n): diem (K+T)=diem K+diem T:=by funext x; simp only [diem,Pi.add_apply,tagP,sum_add_distrib,smul_add,map_add]
lemma coverG(p: Orig n)(X Y: Dues n): cents p (X+Y) a ≤ cents p X a+cents p Y a:=by
 unfold cents; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [← sum_add_distrib]; apply sum_le_sum; intro j _; rw [←mul_add,Pi.add_apply, Pi.add_apply]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (nick_pos a (ct_pos ..)|>.le)
lemma coverN(p:Orig n)(X:Dues n)(c:ℂ):cents p (c • X) a= ‖c‖*cents p X a:=by unfold cents; simp_rw [Pi.smul_apply, norm_smul,mul_left_comm _ ‖c‖, ← Finset.mul_sum]
def rebate (t:Site n)(K:Pride n):Pride n:=fun x i j=>K (x+t) (feedback t i) (feedback t j)
lemma word_p(t:Site n)(P:Pride n)(i:Site n):mom ((rebate t P) i)=mom (P (i+t)):=by
 let A:=(Equiv.addRight ((assembly n).embed t)); have he (j:Orig n)(u:PlaqAxes):feedback t (Sum.inl (j,u))=Sum.inl (A j,u):=by
    unfold feedback; change Sum.inl (j+wrap _ (2 • lift t),u)= Sum.inl (j+_,u); rw [← show (assembly n).embed (wrap n (lift t))=wrap _ (2 • lift t) from Ratio.embed_wrap ..,wrap_lift]; rfl
 funext x y; simp only [rebate,mom]; simp_rw [he]; conv_rhs => rw [← Equiv.sum_comp A]
 refine sum_congr rfl fun k _=> Equiv.sum_comp A (fun v:Orig n=> P (i+t) (Sum.inl (A k,x)) (Sum.inl (v,y)))
lemma reb_light(t:Site n)(K:Pride n)(x):cents (node x) ((rebate t K) x) a=cents (node (x+t)) (K (x+t)) a:=by
 let L:=feedback t; have he(i:Ok n): dial (node x) i=dial (node (x+t)) (L i):=by
    have h:=pin_d (n:=n) (lift t) (x,0) i; simp only [rollH, terse,wrap_lift] at h; exact h.symm
 unfold cents; conv_rhs=> rw [←Equiv.sum_comp L]
 refine sum_congr rfl fun i _=> ?_; conv_rhs=> rw [←Equiv.sum_comp L]
 refine sum_congr rfl fun j _=>?_; unfold contour; rw [← he, ←he]; rfl
def torch(n:Side):= (Fintype.card (Site n):ℝ)⁻¹
def stageM(K:Pride n):Pride n:= torch n • ∑ t:Site n, rebate t K
lemma repose(K:Pride n): WordK (stageM K):=by intro i t a b; simp_rw [stageM,Pi.smul_apply,Finset.sum_apply,rebate,mint,add_assoc]; rw [←Equiv.sum_comp (Equiv.addLeft t) (fun v=>K (i+v) _ _)]; rfl
lemma momentL(t:Site n)(K:Pride n)(h: merit K): merit (rebate t K):= by intro x i j; rw [word_p]; apply h
lemma W_h_cost {K:Pride n}{C:ℝ}(h:∀ i,cents (node i) (K i) a ≤ C)(x): cents (node x) ((stageM K) x) a≤ C:=by
 let V(t:Site n):= rebate t K
 have ht(t): cents (node x) (V t x) a≤ C:=(reb_light ..).trans_le (h _)
 have hy: (stageM K x)= torch n • ∑ i,V i x:=by unfold stageM V; simp
 have he(s:Finset (Site n)): cents (node x) (∑ i∈s,V i x) a ≤ s.card*C:=by induction s using Finset.induction_on with
 | empty => simp [cents]
 | @insert i s h ih=> simp only [h,not_false_eq_true,sum_insert, Finset.card_insert_of_notMem,Nat.cast_add, Nat.cast_one]; exact (coverG ..).trans ((add_le_add (ht i) ih).trans_eq (by ring))
 rw [hy]; have hx(X:Dues n): cents (node x) (torch n • X) a = torch n * cents (node x) X a:=by unfold cents; simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0≤torch n by unfold torch; positivity)]; simp_rw [mul_left_comm _ (torch n),←mul_sum]
 rw [hx]; apply (mul_le_mul_of_nonneg_left (he univ) (by unfold torch; positivity)).trans_eq; rw [card_univ,torch,inv_mul_cancel_left₀ (by positivity)]
end YM.CF.Pec
