import YM.CF.Tap.Havana
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Work.F08
variable (m:ℕ)
def tweight (x:Cover):ℝ:= (1+Laurent.size x :ℝ)^m
def Cp (f: Cover→ ℂ)(a:ℝ):= RG.SumBudget (fun p=> tweight m p*‖f p‖) a
lemma tw_one(x):1≤tweight m x:=one_le_pow₀ (by simp)
lemma tw_pos(x):0≤tweight m x:=zero_le_one.trans (tw_one m x)
lemma tw_n (x y:Cover):tweight m (x+y)≤ tweight m x*tweight m y:=by
 unfold tweight; rw [←mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ m
 have h:(Laurent.size (x+y):ℝ)≤Laurent.size x+Laurent.size y:=by exact_mod_cast Laurent.size_add x y
 nlinarith [Nat.cast_nonneg (α:=ℝ) (Laurent.size x),Nat.cast_nonneg (α:=ℝ) (Laurent.size y)]
def groove (f g : Cover→ ℂ) (k:Cover):= ∑' x,f x*g (k-x)
variable {m} {f g: Cover→ ℂ}{a b:ℝ}
lemma Cp.falls (h:Cp m f a): RG.SumBudget (fun x=> ‖f x‖) a:=budget_minor h (fun x=>norm_nonneg _) fun x=> le_mul_of_one_le_left (norm_nonneg _) (tw_one ..)
lemma Cp.p (h:Cp m f a):0≤a:=(tsum_nonneg h.1).trans h.2.2
private lemma hill(h:Cp m f a)(e:Cp m g b):RG.SumBudget (fun v:Cover×Cover=> tweight m v.2* ‖f v.1*g (v.2-v.1)‖) (a*b):=by
 let W:=tweight m; let H(x):=W x*‖f x‖; let G(x):=W x*‖g x‖; let A(v:Cover×Cover):= H v.1*G (v.2-v.1)
 have hp(v):0 ≤ A v:=mul_nonneg (h.1 _) (e.1 _)
 have hx (x:Cover): Summable fun z => A (x,z):=by
    have he := (Equiv.addRight (-x)).summable_iff.mpr (show Summable G from e.2.1); have h:Summable fun z=> G (z-x):=by simpa [Function.comp_def, sub_eq_add_neg] using he
    exact h.mul_left (H x) -- tune
 have he (x:Cover):∑' z,A (x,z)≤ H x*b:=by change (∑' z,H x*G (z-x))≤_; rw [tsum_mul_left,show (∑' z,G (z-x))=∑' z,G z from (by simpa [ sub_eq_add_neg] using (Equiv.addRight (-x)).tsum_eq G)]; exact mul_le_mul_of_nonneg_left e.2.2 (h.1 _)
 have hl : Summable fun x=>∑' z,A (x,z):= (h.2.1.mul_right b).of_nonneg_of_le (fun _=>tsum_nonneg fun _=>hp _) he
 have hk: Summable A:=(summable_prod_of_nonneg (show ∀ x,0≤A x from hp)).mpr ⟨hx,hl⟩
 have hr:RG.SumBudget A (a*b):=by refine ⟨hp,hk,?_⟩; rw [hk.tsum_prod]; refine (hl.tsum_le_tsum he (h.2.1.mul_right b)).trans ?_; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 e.p
 refine budget_minor hr (fun v=>mul_nonneg (tw_pos ..) (norm_nonneg _)) ?_; intro p; unfold A H G; rw [norm_mul]; calc
   _ ≤ tweight m p.1*tweight m (p.2-p.1)*(‖f p.1‖*‖g _‖):=mul_le_mul_of_nonneg_right (show tweight m p.2≤ tweight m p.1* _ from (Eq.trans_le (congr_arg _ (show p.2=p.1+(p.2-p.1) by abel)) (tw_n ..))) (by positivity) -- tune
   _ =_:=by unfold W; ring
variable {ι : Type*}[Fintype ι][DecidableEq ι]
def symT (f:Cover→ Op ι): Momentum→ Op ι:=fun p i j=> Laurent.read (fun x=> f x i j) p
abbrev RailP(m:ℕ)(f:Cover→Op ι)(a:ℝ):=∀ i j,Cp m (fun x=>f x i j) a
lemma readsP {f:Cover→ Op ι} (h:RailP m f a): Reads f (symT f):=⟨fun i j=>(h i j).falls.2.1,fun _ _ _ _=>rfl⟩
private lemma plankS(h:Cp m f a)(k:Cp m g b):Summable (fun v: Cover×Cover=>‖f v.1*g (v.2-v.1)‖):=by
 let p:=hill h k; exact p.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) (fun x=> le_mul_of_one_le_left (norm_nonneg _) (tw_one ..))
lemma Cp.groove_p(h:Cp m f a)(k:Cp m g b):Cp m (groove f g) (a*b):=by
 let A(v:Cover×Cover):=tweight m v.2*‖f v.1*g (v.2-v.1)‖; have hp:=hill h k; have ht:Summable A:=hp.2.1; let X(y):=∑' x,A (x,y); have hx: RG.SumBudget X (a*b):=⟨fun x=> tsum_nonneg fun y=>hp.1 _, ((summable_prod_of_nonneg (f:=fun p:Cover×Cover=>A p.swap) fun i=>hp.1 _).mp ht.prod_symm).2,Eq.trans_le (show (∑' x,X x)=∑' v,A v from (by unfold X; rw [← Summable.tsum_comm (f:=fun p z=> A (z,p)) ht.prod_symm,← ht.tsum_prod])) hp.2.2⟩
 apply budget_minor hx (fun _=> mul_nonneg (tw_pos ..) (norm_nonneg _)); intro x; unfold X A groove; dsimp only; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ((plankS h k).prod_symm.prod_factor _)) (tw_pos ..)
def foldY (f g:Cover→Op ι) : Cover→Op ι:=fun x i j=>∑ k:ι, groove (fun x=> f x i k) (fun x=>g x k j) x
lemma Cp.sumY {f:ι→Cover→ℂ}(h:∀ i,Cp m (f i) a): Cp m (fun x=>∑ i,f i x) (Fintype.card ι*a):=by
 let F(i:ι)(x):= tweight m x*‖f i x‖; have he(i): Summable (F i):=(h i).2.1
 apply budget_minor (show RG.SumBudget (fun x=>∑ i,F i x) _ from ⟨fun x=> sum_nonneg (fun i _=>(h i).1 _),summable_sum fun i _=>he i,by rw [Summable.tsum_finsetSum (fun i _=>he i)]; exact (sum_le_sum (fun i _=> (h i).2.2)).trans_eq (by simp)⟩) (fun _=> mul_nonneg (tw_pos ..) (norm_nonneg _)); intro x; unfold F; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (tw_pos ..)
lemma foldYP {f g:Cover→ Op ι}(h:RailP m f a)(k: RailP m g b): RailP m (foldY f g) (Fintype.card ι*(a*b)):=fun i j=>Cp.sumY (fun l=>(h i l).groove_p (k l j))
private lemma stem(h:Cp m f a)(k:Cp m g b)(p:Momentum)(e:p∈baseCube): Laurent.read (groove f g) p=Laurent.read f p*Laurent.read g p:=by
 let M(x):ℂ:=Laurent.mode p x; let F(y x:Cover):= M y*(f x*g (y-x))
 have hh: Summable (Function.uncurry F):= by apply Summable.of_norm; simpa only [Prod.snd_swap,Prod.fst_swap,F,M, Function.comp_def, Function.uncurry,norm_mul _ (f _* _), Laurent.mode_real _ _ e.1,one_mul] using (plankS h k).prod_symm
 unfold Laurent.read; conv_lhs=> simp only [smul_eq_mul,groove,←tsum_mul_left]
 change (∑' x,∑' y,F x y)= _; rw [← hh.tsum_comm]
 have h(x): (∑' y,F y x)=(M x*f x)*(∑' y,M y*g y):=by rw [← (Equiv.addRight x).tsum_eq (fun y=> F y x), ← tsum_mul_left]; apply tsum_congr; intro y; unfold F M; rw [show Equiv.addRight x y=y+x from rfl,mode_shift,add_sub_cancel_right]; ring -- tune
 simp_rw [h,tsum_mul_right]; rfl
lemma reads_fold{f g:Cover→Op ι}{A B:Momentum→ Op ι}(h: RailP m f a)(k:RailP m g b)(p: Reads f A)(q: Reads g B): Reads (foldY f g) (fun x=>A x*B x):=by
 refine ⟨(readsP (foldYP h k)).sumK,fun x hx i j=>?_⟩
 simp only [foldY, Laurent.read,Finset.smul_sum, Matrix.mul_apply]
 let F(l):= groove (fun x=> f x i l) (fun x=>g x l j)
 have hp(l):Summable fun y=> Laurent.mode x y • (F l y):=by apply Summable.of_norm; simpa only [norm_smul, Laurent.mode_real x _ hx.1, one_mul] using (show Cp m (F l) (a*b) from (h i l).groove_p (k l j)).falls.2.1
 rw [Summable.tsum_finsetSum (fun l _=>hp l)]; apply sum_congr rfl; intro l _; change Laurent.read (F l) x= _; rw [show _= Laurent.read (fun z=> f z i l) x*Laurent.read (fun z=>g z l j) x from stem (h i l) (k l j) x hx,p.readK x hx,q.readK x hx]
end YM.CF.Tap
