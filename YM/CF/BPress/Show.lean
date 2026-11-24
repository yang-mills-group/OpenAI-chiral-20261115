import YM.CF.BPress.Hanger
/-!
eq:B-ang-M packaging BEFORE any condition/fix. support on bands in physical algebra. and the Fock operator product paid as sum over frames: feeds exact gauge-expanded integral.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Net
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Tunnel Finset RG Wilson
open Law Push.SectorMeasure Env
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
open Tulip Fixed Fock Scree Skye Girt Net Bands Paige Dial
variable {N : Side}{B : BandWidth}(X:Bands (More N) B){T : Sheet.Atlas}{C C' Lf y : ℝ}{b : ℕ}(F:Net (More N) T Lf y C C' b) (s:List X.Index)(A:X.Index→ Theatre N) {K:X.Index→ℝ}
-- argument ordering X F maybe prefer F.lean method
-- slots can take in order chronclock or ANY ordering (commuting), using operator MUL.
def shows : Fixed.Test N:= walkMul s fun i=> F.showM X i (A i)
lemma watch_apply (U:Micro (More N)) : F.shows X s A U=walkMul s fun i=> F.showM X i (A i) U:=by induction s with|nil=> rfl|cons i s ih=> change F.showM X i (A i) U*_= F.showM X i (A i) U*_; exact congrArg _ ih
variable (H:∀ i,Extends F X i (A i) (K i)) (t:T.Coasts y)
include H t
lemma licensed_show : IsMark (s.toFinset.biUnion X.band) (F.shows X s A) (walkMul s (fun i=>25*quoteN (y:=y) X i*(K i))) := IsMark.list_product _ _ _ fun i p=> (F.show_mark X i (A i) (H i) t).weaken (subset_biUnion_of_mem X.band (by simpa using p)) le_rfl
lemma show_turn (a : Mach (More N))(p:X.frozen a)(U : Micro (More N)): F.shows X s A (gauge a U)=twist (quantU (tradew _ a)) (F.shows X s A U):=by
 have he (i:X.Index) : F.showM X i (A i) (gauge a U)= twist (quantU (tradew _ a)) (F.showM X i (A i) U):= by
    by_cases v:i ∈ X.dc; exact idle (X.band i) _ (p i v) (F.show_mark X i (A i) (H i) t) _; exact F.show_turnN X i (A i) (mem_sdiff.mpr ⟨mem_univ _,v⟩) U t (H i) a
 rw [F.watch_apply,F.watch_apply]; unfold walkMul; simp_rw [he]; induction s <;> simp_all
omit H t
-- stripped argument includes all readings of the same gauge U in orbital factors. Subsequent sampling.
def readout (w:X.Slates) (U:Micro (More N)) : FC (Single N):= walkMul s fun i=> A i (U,X.putF T y U i (w i)) -- binder F omitted? uses T y not F
-- integral notation separate, permit indexing all choices
include H in
lemma readout_env (w:X.Slates): Envelope (readout (T:=T) (y:=y) X s A w):= listP s (f:=fun i U=> A i (U,X.putF T y U i (w i))) fun i=> Env.along (H i).env (g:=fun U=>(U,X.putF T y U i (w i))) (measurable_id.prodMk (X.putF_meas _ _ _ _))

def stake (w : X.Slates)(U:Micro (More N)) := ∏ i:X.Index,F.takeN X U i (X.putF T y U i (w i))
lemma shows_stake (w : X.Slates): Envelope (F.stake X w):= by
 let g(i:X.Index) := fun U:Micro (More N)=> F.takeN X U i (X.putF T y U i (w i)); have p(i) : Envelope (g i):= ⟨(F.takeN_meas X i).comp (f:=fun U=>(U,X.putF T y U i (w i))) (measurable_id.prodMk (X.putF_meas _ _ _ _)), quoteN (y:=y) X i, fun U => by unfold g; rw [Real.norm_eq_abs, abs_of_nonneg (F.takeN_pos ..)]; exact F.quoteN_bound ..⟩
 have h(t : Finset X.Index) : Envelope fun U=> ∏ i∈t,g i U:= by induction t using Finset.induction_on with|empty=>simpa using fixedP (X:=Micro (More N)) (1:ℝ)|insert i t ht ih=> simp_rw [prod_insert ht]; exact prodP (p i) ih
 exact h _
lemma expand_show (U:Micro (More N))(h:s.Nodup)(p:∀ i,i∈s) : F.shows X s A U= ∑ x∈X.permit T y U, ((F.stake X x U):ℂ) • readout (T:=T) (y:=y) X s A x U := by
 rw [F.watch_apply]; unfold showM; let f(i:X.Index)(a:Labels (More N)):= F.price X i (A i) U (X.putF T y U i a); let g : X.Index → Finset (Labels (More N)):= X.choices T y U; change (walkMul s (fun i=>∑ p∈g i,f i p))=_
 rw [walk_sum s g f h p]; apply sum_congr _; swap; · ext x; simp [Bands.permit,g]
 intro x _; unfold f price; rw [walk_scalar]; unfold readout stake; rw [walk_prod s h p, Complex.ofReal_prod]

def encore (f:Orbit N → Phys N) (w:X.Slates) (x:Orbit N): ℂ:= integrand (readout (T:=T) (y:=y) X s A w) f x
open Girt
variable (f:Orbit N→Phys N)(p:Envelope f)
lemma scaled_test {R : Finset X.Slates} (x:Orbit N)(A:X.Slates→FC (Single N))(b:X.Slates→ℝ) : beamZ N (acts (∑ i∈R,(b i:ℂ) • A i) (f x))= ∑ i∈R,b i • beamZ N (acts (A i) (f x)):=by
 induction R using Finset.induction_on with
 | empty=> simp [beamZ]
 | insert i R h ih=> rw [sum_insert h,sum_insert h,act_add,act_smul,←ih, beamZ, inner_add_right,inner_smul_right]; unfold beamZ; rw [Complex.real_smul] -- tune includes ofReal smul
lemma at_expansion (x:Orbit N)(h:s.Nodup)(w:∀ i,i∈s) : integrand (F.shows X s A) f x= ∑ i∈ X.permit T y x.1, F.stake X i x.1 • encore (T:=T) (y:=y) X s A f i x := by
 unfold encore; unfold integrand; rw [F.expand_show X s A _ h w]; exact scaled_test X f x (fun i=>readout (T:=T) (y:=y) X s A i x.1) (fun i=> F.stake X i x.1)
include p H
lemma encore_env (w:X.Slates) : Envelope (encore (T:=T) (y:=y) X s A f w):=by
 obtain ⟨C,c⟩:=(readout_env X F s A H w).cost; obtain ⟨K,k⟩:=p.cost; let g:=fun z: FC (Single N) × Phys N => beamZ N (acts z.1 z.2); refine ⟨ ((show Continuous g from continuous_const.inner ((acts_cont.comp continuous_fst).clm_apply continuous_snd)).measurable).comp (f:=fun x:Orbit N=> (readout (T:=T) (y:=y) X s A w x.1,f x)) (((F.readout_env X s A H w).meas.comp measurable_fst).prodMk p.meas), C*K,fun U =>?_⟩
 let a:=f U; let i:=readout (T:=T) (y:=y) X s A w U.1; refine (norm_inner_le_norm (𝕜:=ℂ) (mateK N) (acts i a)).trans ?_; rw [(tickB N).2,one_mul]; have ht : ‖acts i‖ ≤ C:=(Matrix.l2_opNorm_toEuclideanCLM _).le.trans (c U.1); exact ((acts i).le_opNorm a).trans (mul_le_mul ht (k U) (norm_nonneg _) ((norm_nonneg _).trans ht)) -- tune
include t
theorem slate_integral (h:s.Nodup)(w:∀ i,i∈s) (r:∀ (x: Orbit N) (a:Mach (More N)), f (gird a x)= effectK (tradew _ a).val (f x)) :
   (∫ x, integrand (F.shows X s A) f x ∂city N)= ∫ U, (∑ i∈X.permit T y (X.tone U), F.stake X i (X.tone U) • (∫ x, encore (T:=T) (y:=y) X s A f i (X.tone U,x)∂depot N))∂prior group _:=by
 let g:= integrand (F.shows X s A) f; rw [X.freeze g (integrand_env (F.licensed_show X s A H t) p) (fun a b q=> integrand_turn a (F.show_turn X s A H t a b) (fun x=> r x a) q)] -- tune
 apply integral_congr_ae; apply Eventually.of_forall; intro x; dsimp only [g]; simp_rw [at_expansion X F s A f _ h w]; rw [integral_finsetSum _]; swap; · intro i _; exact (Env.integrableX (Env.along (encore_env X F s A H f p i) (g:=fun v:Ids N=>(X.tone x,v)) (measurable_const.prodMk measurable_id)) (depot N)).smul (F.stake X i (X.tone x))
 simp_rw [integral_smul]
end YM.CF.BPress.Net
