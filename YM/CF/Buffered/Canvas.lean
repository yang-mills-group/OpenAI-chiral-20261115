import YM.CF.Buffered.Decked
/-!
# Film price & power limits
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 540000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Fock NormedSpace Finset Filter MeasureTheory Lattice Reflect RG Push.SectorMeasure Cin
open Sector (grainB)
open Film (Leaf)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {X Y B I J:Type*} [TopologicalSpace X][TopologicalSpace Y][MeasurableSpace X][MeasurableSpace Y][LinearOrder I][Fintype I][LinearOrder J][Fintype J] [Nonempty X][Nonempty Y] [BorelSpace X][BorelSpace Y] [SecondCountableTopology X][SecondCountableTopology Y][CompactSpace X][CompactSpace Y]
variable {n:ℕ}[NeZero n] [Fintype B]
lemma full_wordE (F : ℕ→DeckIn n X Y→ FC I) (h:∀ i, Envelope (F i))(w:ℕ) : Envelope (fun x:DeckIn n X Y=> run (fun i=>F i x) w) := by
 induction w with | zero=> exact Girt.rite_c _ | succ v ih=> simp_rw [run_succ]; exact env_mult ih (h v)
namespace Batch
variable (F G:Film X Y B I) (L:Many n (Film X Y B I))(R:Batch n I J) (μ:Measure X)[IsFiniteMeasure μ] (ν:Measure Y)[IsFiniteMeasure ν]
local notation "D" => DeckIn n X Y
local notation "δ" => Measure.prod (piN n μ) (piN n ν)
def marked (S : DeckIn n X Y→FC J) (x:D) := wgt L x * (run (R.needle L x) n * S x * run (R.root L x) n) R.grade R.grade
noncomputable def finale (x:D) := exp (Trotter.ends (R.core L x) (R.feet L x) n)
def input := ∫ x:D,R.marked L (R.finale L) x∂δ
def pile (k:ℕ) := ∫ x:D, R.layerNum L x k∂δ
lemma support_wgt : Envelope (wgt L) := product_env _ _ (fun i _=> Env.along (L i).regularA (atCell_meas _))
lemma support_m : Envelope (fun x:D=> run (R.needle L x) n) := full_wordE (I:=J) (fun i x=> R.needle L x i) (fun i=> Env.along (g:=fun x:D=> atCell x i) (Girt.pole_w _ _ (into_cont (recur R.site i)) (recur L i).regularB) (atCell_meas _)) _
lemma support_s : Envelope (fun x:D=> run (R.root L x) n) := full_wordE (I:=J) (fun i x=> R.root L x i) (fun i=> Env.along (g:=fun x:D=> atCell x i) (Girt.pole_w _ _ (into_cont (recur R.site i)) (recur L i).regularC) (atCell_meas _)) _
lemma support_mark (f:D→FC J)(p:Envelope f): Envelope (R.marked L f) := env_mult (support_wgt L) (Girt.pole_w _ (fun A:FC J=> A R.grade R.grade) (continuous_id.matrix_elem _ _) (env_mult (env_mult (support_m ..) p) (support_s ..)))
lemma core_cont (i:ℕ) : Continuous fun x=> R.core L x i := (into_cont _).comp ((recur L i).regularD.comp (atCell_cont _))
lemma feet_cont (i:ℕ) : Continuous fun x=> R.feet L x i := by
 have h(i j k) : Continuous fun x=> R.leg L x i j k := (into_cont _).comp (((recur L i).regularE ..).comp (atCell_cont _))
 exact continuous_finsetSum _ fun x _=> ((h i true x).mul (h (i+1) false x)).const_smul (outer n i true)
private lemma layer_walk (x:D): Tendsto (fun i=> R.layerNum L x i) atTop (𝓝 (R.marked L (R.finale L) x)):= by
 let y (A:FC J):=wgt L x * (run (R.needle L x) n * A * run (R.root L x) n) R.grade R.grade
 let a:=R.core L x; let b:= R.feet L x
 -- remove defEq pressure
 change Tendsto (fun i=> y (Trotter.plays a b n i)) atTop (𝓝 (y (exp (Trotter.ends a b n))))
 have hp : Continuous y := by fun_prop -- error
 exact (hp.tendsto _).comp (Trotter.rises a b n)
lemma support_layer : Tendsto (R.pile L μ ν) atTop (𝓝 (R.input L μ ν)) := by
 let k(i:ℕ)(x:D):= Trotter.plays (R.core L x) (R.feet L x) n i
 obtain ⟨p,K,P⟩ := Trotter.bounded _ _ (core_cont L R) (feet_cont L R) n
 obtain ⟨c₁,h₁⟩:= (support_wgt L).cost; obtain ⟨c₂,h₂⟩:= (support_m L R).cost; obtain ⟨c₃,h₃⟩:= (support_s L R).cost
 let y (x:D) (A: FC J):= R.marked L (fun _=> A) x
 let v:D →ℝ:= fun _=> c₁*((c₂*K)*c₃)
 unfold pile input
 refine tendsto_integral_filter_of_dominated_convergence v (Eventually.of_forall fun i=>(support_mark L R (k i) (Env.compact (p i))).meas.aestronglyMeasurable) (Eventually.of_forall (fun i=>Eventually.of_forall (fun x=>?_))) (integrable_const _) (Eventually.of_forall (fun x=> ?_))
 · have h:‖run (R.needle L x) n * k i x‖≤ c₂*K:= (norm_mul_le ..).trans (mul_le_mul (h₂ x) (P i x) (norm_nonneg _) ((norm_nonneg _).trans (h₂ x)))
   unfold Batch.layerNum; rw [norm_mul]; exact mul_le_mul (h₁ x) ((norm_entry ..).trans ((norm_mul_le ..).trans (mul_le_mul h (h₃ x) (norm_nonneg _) ((norm_nonneg _).trans h)))) (norm_nonneg _) ((norm_nonneg _).trans (h₁ x))
 exact layer_walk L R _
lemma support_final : Envelope (R.marked L (R.finale L)) := by
 apply support_mark; apply Env.compact; letI : NormedAlgebra ℚ (FC J) := NormedAlgebra.restrictScalars ℚ ℝ _
 exact exp_continuous.comp (continuous_finsetSum _ fun i _=> (core_cont L R i).add (feet_cont L R i))
section kernel
variable [MeasurableSpace B][DiscreteMeasurableSpace B]
open Heat
local notation "cnt" => Measure.count
-- Option B measurable at counting; keep explicit
instance (k:ℕ) : MeasurableSpace (Leaf k B) := ⊤
instance (k:ℕ) : DiscreteMeasurableSpace (Leaf k B) := inferInstanceAs (@DiscreteMeasurableSpace _ ⊤)

def transfer (b:Finset I) (k:ℕ) : Kern (Measure.count.prod μ: Measure (Leaf (k+1) B × X)) where
 Q z:= F.closure (unitT k) ν b (k+1) z.1.1 z.2.1 (z.1.2,z.2.2)
 paid := by -- reuse bound from merger calculation
    let U := Leaf (k+1) B; let K t s:= F.closure (unitT k) ν b (k+1) t s
    let W (p:(Leaf (k+1) B × Leaf (k+1) B) × (X×X)):=K p.1.1 p.1.2 p.2
    have hp(t s:U): Envelope (K t s):= F.closureE ..
    choose C hC using fun j k=> (hp j k).cost
    refine ⟨(show Measurable W from measurable_from_prod_countable_right fun i=> (hp i.1 i.2).meas).comp (((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))), ∑ i, ∑ j, max 0 (C i j), fun x=> ?_⟩
    exact (hC _ _ _).trans <| (le_max_right ..).trans <| (single_le_sum (f:=fun j=> max 0 (C x.1.1 j)) (fun i _=> le_max_left ..) (mem_univ x.2.1)).trans (single_le_sum (fun i _=> sum_nonneg (fun _ _=> le_max_left ..)) (mem_univ x.1.1))
lemma is_reverse {U:UNI I}(h:Film.Reversed F G U)(b:Finset I)(v:twist U (cutM bᶜ)=cutM b)(k:ℕ):transfer G μ ν b k=star (transfer F μ ν b k):= by
 apply Kern.ext; funext x; exact (F.closure_star _ h ν b v _ x.2.1 x.1.1 (x.2.2,x.1.2)).symm

lemma is_total (k:ℕ)(p:2≤ n): R.pile L μ ν k = Kern.τ (Kern.roll (fun i=>transfer (recur L i) μ ν R.post k) n) := by
 let U := Leaf (k+1) B
 let Y' := MeasurableEquiv.arrowProdEquivProdArrow U X (Fin n); let T (b:Many n (Leaf (k+1) B))(x:D):= ∏ i:Fin n,(L i).evaluate (unitT k) R.post (k+1) (b i) (b (i+1)) (atCell x i.val)
 let Q := cyclic (fun i=>transfer (recur L i) μ ν R.post k) n
 have hp: ( piN n (cnt: Measure U))=cnt:= Measure.ext_of_singleton fun i=> by simp [piN]
 have hv(t):Envelope (T t) := product_env _ _ (fun i _=> Env.along ((L i).evalE ..) (atCell_meas ..))
 have hz:= measurePreserving_arrowProdEquivProdArrow U X (Fin n) (fun _=>cnt) (fun _=> μ)
 unfold pile; rw [←total,← ((measurePreserving_arrowProdEquivProdArrow U X (Fin n) (fun _=>cnt) (fun _=>μ)).symm).integral_comp' Q, integral_prod (fun z => Q (Y'.symm z))]; swap; · exact Env.integrableX (Env.along (g:=Y'.symm) (show Envelope Q from cyclic_env _) Y'.symm.measurable) _
 rw [show (Measure.pi fun _ : Fin n=> (cnt:Measure U))=cnt from hp,integral_count]
 simp_rw [R.read_layer L _ _ p]; rw [integral_finsetSum]; swap; · exact fun i _=>Env.integrableX (hv i) δ
 refine sum_congr rfl fun v _=>?_ ; change (∫ j,T v j∂δ)= ∫ j,Q (Y'.symm (v,j))∂piN n μ
 rw [integral_prod _ (Env.integrableX (hv v) δ)]; apply integral_congr_ae; refine Eventually.of_forall fun j=> ?_
 let W(i:Fin n)(y:Y):=(L i).evaluate (unitT k) R.post (k+1) (v i) (v (i+1)) ((j i,j (i+1)),y)
 have he(i:Fin n)(y:Many n Y): (L i).evaluate (unitT k) R.post (k+1) (v i) (v (i+1)) (atCell (j,y) i.val) = W i (y i):= by unfold W atCell; simp [recur]
 dsimp only; unfold T; simp_rw [he,integral_fintype_prod_eq_prod] -- check
 unfold Q cyclic; refine prod_congr rfl fun i _=> ?_; dsimp only; rw [recur_of]; rfl
lemma paired {U:UNI I}(h: ∀ i:Fin n,L i= if i.val%2=0 then F else G) (p:Film.Reversed F G U)(v:twist U (cutM R.postᶜ)=cutM R.post)(t:Even n) :
 Tendsto (fun k=> ((Kern.power (transfer F μ ν R.post k) (n/2):ℝ):ℂ)) atTop (𝓝 (R.input L μ ν)):= by
 refine (support_layer L R μ ν).congr ?_; intro k; have he:=NeZero.pos n; obtain ⟨k',b'⟩:= t
 rw [is_total]; swap; · omega -- get Even handle
 rw [Kern.roll_chain (F:=transfer F μ ν R.post k) _ he ?_]; swap
 · intro i t; unfold recur; rw [h, Fin.val_cast_of_lt t]; split; rfl; exact is_reverse F G μ ν p R.post v k -- tune
 conv_lhs => arg 1; arg 2; rw [show n=n/2*2 from by omega]
 exact Kern.power_τ _ (by omega)
end kernel
end Batch
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.Batch.paired
