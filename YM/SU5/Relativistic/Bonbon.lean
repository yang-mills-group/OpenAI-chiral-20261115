import YM.SU5.Relativistic.Satchel
/-! # kernels BEFORE occupancy. Full supports now also spatial. -/
set_option autoImplicit false
set_option synthInstance.maxSize 23000
set_option maxHeartbeats 630000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free Asymptotics
open Laurent Bloch Fir Jill Ember Shore UnitAddTorus Fock Lat UpStart Cube Skye Scroll Rush Dial Tulip Pannier.Chancel Buffered
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Σ_"=> Set.Icc (-π) π
-- integer square
abbrev stow(a:ℕ)(j:ℤ):= (box a).filter fun x:Cover=> x TA=j
def cork (x:Cover): WalkA:=fun i=> x i.castSucc
private lemma mail (x:Cover) : tack (cork x) (x TA) = x:=by
 funext i; induction i using Fin.lastCases <;> simp only [tack,Fin.lastCases_castSucc, Fin.lastCases_last] <;> rfl
private lemma earmark (a:ℕ): (TwistT a).biUnion (stow a) = box a:=by
 ext i; rw [Finset.mem_biUnion]; constructor; · intro ⟨_,_,h⟩; exact (mem_filter.mp h).1
 intro h; exact ⟨i TA,Finset.mem_Icc.mpr ⟨(box_test.mp h).1 _, (box_test.mp h).2 _⟩,mem_filter.mpr ⟨h,rfl⟩⟩

variable (v:Cover) (d A:ℕ)
private def buy (i:SpinIdx)(y:Cover):= chipPay (mintedK v d i) y
private abbrev Y(i:SpinIdx)(j:ℤ)(x:WalkA):= if tack x j∈ box A then buy v d i (tack x j) else 0
private def lunch :Waxy:= fun i j=> Finsupp.onFinset ((stow A j).image cork) (Y v d A i j) (by
    intro x h; unfold Y at h; split at h; next h'=> exact mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨h',tack_right ..⟩,funext (fun i=> tack_left ..)⟩
    contradiction) -- tune
abbrev Lilt (v:Cover) (d A:ℕ):=lunch v d A
local notation "F" => lunch v d A
lemma feast_s(i:SpinIdx)(j:ℤ)(x:WalkA): F i j x = if tack x j∈ box A then chipPay (mintedK v d i) (tack x j) else 0:=by rw [lunch,Finsupp.onFinset_apply]; rfl
lemma boxMeal (i:SpinIdx)(j:ℤ)(x:WalkA)(p:x∈(F i j).support): tack x j∈ box A:=by have he:= Finsupp.mem_support_iff.mp p; rw [feast_s] at he; exact of_not_not fun t=> he (if_neg t)
lemma firstStamp (i:SpinIdx)(k:Behind)(t:ℝ)(u:ℤ): (∑ x∈ stow A u,buy v d i x*mode (tmap (tack k t)) (-x))=array (F i u) k*soundT u t:=by
 -- enlarge right, then injective and simplify tags
 let Z:= stow A u; let H:= Z.image cork
 have hx(y:Cover)(e:y∈Z): tack (cork y) u=y:= by
    rw [← (Finset.mem_filter.mp e).2]; exact mail _
 have hf : (F i u).support ⊆ H := fun y h=>Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨boxMeal v d A i u y h,tack_right ..⟩,funext (fun i=> tack_left ..)⟩
 unfold array Finsupp.sum; rw [Finset.sum_mul, Finset.sum_subset hf (fun j _ h=>by simp only [Finsupp.notMem_support_iff.mp h,zero_mul,zero_mul]),show H=Z.image cork from rfl,sum_image]; swap; · intro x h y u g; nth_rw 1 [← hx x h]; nth_rw 1 [g]; exact hx y u
 apply Finset.sum_congr rfl; intro x z; rw [feast_s,hx x z, if_pos (mem_filter.mp z).1, show mode (tmap (tack k t)) (-x)= _ from (show mode (tmap (tack k t)) (-x)= spax (-cork x) k *soundT u t from Eq.trans (congrArg (fun x=>mode (tmap (tack k t)) (-x)) (hx x z).symm) (tagF ..))]; change _=buy _ _ _ _*_*_; rw [mul_assoc]
lemma equalsLunch (i:SpinIdx)(k:Behind)(t:ℝ): (timbre A F k t).ofLp i= ∑ y∈box A, buy v d i y * mode (tmap (tack k t)) (-y):=by
 rw [←earmark,Finset.sum_biUnion]; · simp_rw [firstStamp]; rfl
 intro i hi j hj w; exact Finset.disjoint_left.mpr (fun x h e=>w ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp e).2))
variable {v d A}
local notation "M□"=> Minty v d
lemma gala {k:ℕ}(p: 2*(1+(k+8))+2 ≤ 2*d):∃ C:ℝ, 0<C ∧ ∀ A:ℕ,∀ u:Behind,∀ t:ℝ, ‖M□ (tack u t)-timbre A (lunch v d A) u t‖≤C*boxOrder k A:=by
 choose C e h using (fun i:SpinIdx=>orcas (k:=k) (mintedMe (v:=v) (d:=d) i) (ferret i p))
 let Y:= ∑ i:SpinIdx,C i; have ht(i):C i ≤ Y:=Finset.single_le_sum (f:=C) (fun i _=>(e i).le) (Finset.mem_univ _); have hx:0<Y:=(e 0).trans_le (ht _)
 refine ⟨2*Y,by positivity,fun A u t=>?_⟩
 let D:= M□ (tack u t)-timbre A (lunch v d A) u t; let V:= boxOrder k A; have hh:0<V:=boxOrder_p ..; apply (sq_le_sq₀ (norm_nonneg D) (mul_nonneg (by positivity) hh.le)).mp; rw [EuclideanSpace.norm_sq_eq];
 have he (i:SpinIdx):‖D.ofLp i‖≤ Y*V:=by unfold D; rw [WithLp.ofLp_sub,Pi.sub_apply,equalsLunch]; exact (h i A (tack u t)).trans (mul_le_mul_of_nonneg_right (ht i) hh.le)
 apply le_trans (Finset.sum_le_sum (f:=fun i=> ‖D.ofLp i‖^2) (s:=univ) (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (he i) _)); simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; change ((4:ℕ):ℝ)* (Y*V)^2≤ (2*Y*V)^2; norm_num only [Nat.cast_ofNat]; apply le_of_eq; ring
lemma mint_smooth (v:Cover)(d:ℕ)(e:2≤d) : Continuous (Minty v d):=by
 have hc(i:SpinIdx):Continuous (mintedK v d i):=(ferret i (p:=show 2*(1+0)+2≤2*d by omega)).continuous
 rw [show Minty v d= fun x=> ∑ i:SpinIdx, mintedK v d i x • basisKet i from funext (fun i=> (basis_expand (Minty v d i)).symm)]; exact continuous_finsetSum _ fun i _=> (hc i).smul continuous_const
-- convergence test ALL corners now. 
private lemma within_b (x:Behind)(y:ℝ)(p:x∈backPane)(q:y∈Σ_):Bound Real.pi (tack x y):=by
 apply (pi_norm_le_iff_of_nonneg pi_pos.le).mpr; intro i; induction i using Fin.lastCases with
 | last => rw [show Fin.last 3=TA from rfl,tack_right]; exact abs_le.mpr q
 | cast i=> rw [tack_left]; exact abs_le.mpr (p i (Set.mem_univ _))
private lemma voyage {p:ℕ→ Behind×ℝ}{x:Behind×ℝ}{M:ℕ→ Jill.Male}(P:Tendsto p atTop (𝓝 x))(e:Tendsto (fun i=>(M i).val) atTop atTop)(l:∀ i,p i∈backPane×ˢΣ_)(w:x∈backPane×ˢΣ_)(z:2≤ d):
    Tendsto (fun i=>
       let Y:= Minty v d (tack (p i).1 (p i).2); acts (mana (M i) (p i).1 (p i).2) Y - Y) atTop (𝓝 0):=by
 let f(i):=tack (p i).1 (p i).2; let a:=tack x.1 x.2; let F₀:= Minty v d; let F':=F₀ ∘ f; let S(i):=mana (M i) (p i).1 (p i).2
 have hu0:Tendsto f atTop (𝓝 a):= (tack_c.tendsto x).comp P
 have hx:Tendsto F' atTop (𝓝 (F₀ a)):= ((mint_smooth v d z).tendsto a).comp hu0
 have hk(i):‖acts (S i)‖ ≤ 1:=spiritShrink _ _ (l i).1 (l i).2 _
 change Tendsto (fun i=>acts (S i) (F' i)- F' i) _ _
 by_cases g:a=0
 · rw [g,show F₀ 0=0 from ?_] at hx
   · have hp:Tendsto (fun i=>acts (S i) (F' i)) atTop (𝓝 0):= squeeze_zero_norm (fun i=> ((acts (S i)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hk i))) (by simpa using hx.norm)
     simpa only [sub_self] using (hp.sub hx)
   unfold F₀ Minty countMe sparrow; simp [zero_pow (show 2*d≠0 by omega)]
 let G(i):= mixL 4 (M i).val (tmap (f i)); have hv:Tendsto G atTop (𝓝 (tough a)):= tendsto_pi_nhds.mpr fun j=> Shore.gulch e (((show Continuous tmap by unfold tmap; fun_prop).tendsto _).comp hu0) (Eventually.of_forall (fun i=>(M i).property)) (within_b _ _ w.1 w.2) g j (Eventually.of_forall (fun i=> b_base (within_b _ _ (l i).1 (l i).2)))
 let V(i):= countMe v d (f i) • acts (1-zen (G i)) (basisKet 0)
 have he:Tendsto V atTop (𝓝 (F₀ a)):= (((show Continuous (countMe v d) from (continuous_const.mul (mode_smooth v).continuous).mul (sats d).continuous).tendsto a).comp hu0).smul ((Continuous.tendsto (f:=fun p:Momentum=>acts (1-zen p) (basisKet (0:SpinIdx))) (by unfold zen; fun_prop) _).comp hv)
 have ht:Tendsto (fun i=> F' i - V i) atTop (𝓝 0):=by simpa only [sub_self] using (hx.sub he)
 have hy:Tendsto (fun i=> acts (S i) (F' i-V i)) atTop (𝓝 0) := squeeze_zero_norm (fun i=> ((acts (S i)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hk _))) (by simpa using ht.norm)
 refine Tendsto.congr' ?_ (show Tendsto (fun i=>acts (S i) (F' i-V i)-(F' i-V i)) _ (𝓝 0) from by simpa only [sub_self] using (hy.sub ht))
 filter_upwards [hu0.eventually (eventually_ne_nhds g)] with i u; have hp:acts (S i) (V i)=V i:=by unfold V; rw [map_smul, show acts (S i) (acts (1-zen (G i)) (basisKet 0))=_ from scoreGraph 4 (M i).val (M i).property _ (within_b _ _ (l i).1 (l i).2) u]
 rw [map_sub,hp]; abel
lemma junebug (v:Cover)(d:ℕ)(e:2≤d)(ε:ℝ)(p:0<ε) : ∃ N:ℕ,∀ M:Jill.Male, N ≤ M.val.val→ ∀ k∈backPane,∀ t∈Σ_, let a:=Minty v d (tack k t); ‖acts (mana M k t) a - a‖ ≤ ε:=by
 by_contra! g
 choose M w x u t y z using g; let f(i:ℕ): Behind×ℝ:= (x i,t i)
 obtain ⟨a,hA,b,hb,P⟩:= ((isCompact_univ_pi (fun _:Fin 3=> isCompact_Icc)).prod (show IsCompact Σ_ from isCompact_Icc)).tendsto_subseq (fun i=> (show f i∈backPane×ˢΣ_ from ⟨u i,y i⟩))
 have he:=voyage (M:= M∘ b) (v:=v) P (tendsto_atTop.mpr (fun m=> (hb.tendsto_atTop.eventually_ge_atTop m.val).mono (fun i p=> (show m ≤ (M (b i)).val from p.trans (w _))))) (fun i=> ⟨u _,y _⟩) hA e
 have hp:= ge_of_tendsto he.norm (Eventually.of_forall (fun i=> (lt_of_not_ge (z (b i))).le))
 rw [norm_zero] at hp; exact p.not_ge hp
end YM.CF.Crest.Sleet.Sorcerer
#print axioms YM.CF.Crest.Sleet.Sorcerer.junebug
