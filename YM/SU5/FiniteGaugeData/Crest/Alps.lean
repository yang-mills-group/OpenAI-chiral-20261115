import YM.SU5.FiniteGaugeData.Crest.Haven
/-! # Frontier tariff on parallel aliases. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Crest.Shore
open Function Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
-- number loan. Shift argument avoid accidental periodic alias.
def income (v:Cover) :ℝ:= ((∏ i:Axis, (1+((v i).natAbs:ℝ)))^2)⁻¹
def slat (u:Bin)(v:Cover)(i:Axis):ℂ:= weave (u+ stem v)^8 * (2*((u+stem v) i:ℂ)/ (radius (u+stem v):ℝ))
variable {N:Side}(v:Cover)
lemma income_2 : 0< income v:=by unfold income; positivity
@[simp] lemma income_lift (i: Site N) : income (lift i)=decay 2 i:=rfl

lemma raising : ∀ᶠ N:Side in atTop,lift (wrap N v)=v:=by
 have he(i:Axis): ∀ᶠ x:Side in atTop, -((x.val:ℕ):ℤ)<2*v i∧2*v i≤x.val:=by
    filter_upwards [eventually_ge_atTop (⟨(v i).natAbs*2+1,by omega⟩: Side)] with x e
    change _+1 ≤ x.val at e; omega
 exact ((eventually_all).2 he).mono (fun i u=>lift_eq_iff.mpr ⟨rfl,u⟩)
lemma wallet : Summable income:=by
 obtain ⟨C,p,P⟩:= decay_cost; refine summable_of_sum_le (fun i=>(income_2 i).le) (c:=C) ?_; intro S
 obtain ⟨i,p⟩:= ((S.eventually_all).mpr (fun i _=>raising i)).exists
 have he: (∑ j∈S,income j)=∑ j∈ S.image (wrap i), decay 2 j:= by
    rw [sum_image]; · exact sum_congr rfl (fun j v=> (congrArg income (p j v).symm).trans (income_lift _))
    · intro x u y v h; exact (p x u).symm.trans ((congrArg (@lift i) h).trans (p y v))
 rw [he]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=> (decay_pos ..).le)).trans (P i)

variable {x:Bin}{M:Side}
local notation "K" a:max=> tmap a
-- term unit. splicing on cover. budget.lift
abbrev roofed (N: Side)(z:Momentum)(i:Site N)(a:Axis):ℂ:= muff 4 N (aliasAt z i)^2 * ((N.val:ℂ)⁻¹ * bGraph (aliasAt z i) a)
lemma terrain (a:Axis) : ∃ C:ℝ,0<C∧∀ N:Side, Odd N.val→∀ i:Site N,i≠0→ ∀ x:Momentum, x∈baseCube→‖roofed N x i a‖ ≤ C*decay 2 i:=by
 let X:= Σ (i:Jill.Male),{j:Site i.val // j≠0}; let U (x:X):=x.1.val; let V(x:X):Site (U x):= x.2.val;
 have he:= fun x:X=> x.1.property; obtain ⟨η,C,p,hC,h⟩:= (.mul (Moderate.pow (muff_pay 4 U he V) 2) (spicy U he V (fun x=>x.2.property) a): Moderate (fun x=> decay 4 (V x)^2*(grade (V x))⁻¹) (fun i z=>roofed (U i) z (V i) a)) -- arguments?
 refine ⟨C,hC,fun i k z h₀ Z P=>?_⟩; have H:= (h ⟨⟨i,k⟩,⟨z,h₀⟩⟩).bound Z (mem_cube_real (base_subset_realCube p P) p); change ‖roofed i Z z a‖ ≤ C*(decay 4 z^2 * _⁻¹) at H; apply H.trans; gcongr; exact (mul_le_of_le_one_right (sq_nonneg _) (inv_le_one_of_one_le₀ (grade_ge ..))).trans ((le_of_eq (by rw [sq,←decay_add])).trans (decay_anti z (by omega : 2≤4+4))) -- tune
-- `r` analog of look
private def glowC (N:Side)(v:Cover) (x:Momentum)(a:Axis) :ℂ:= if lift (wrap N v)=v then roofed N x (wrap N v) a else 0
lemma rolling (N:Side)(x:Momentum)(a:Axis): mixL 4 N x a=∑' i:Cover,glowC N i x a:=by
 rw [tsum_eq_sum (s:=univ.image (@lift N)),sum_image]; · unfold mixL; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply, glowC,wrap_lift,if_true,roofed, smul_eq_mul,Finset.mul_sum]; exact sum_congr rfl fun i _=>by ring
 · exact lift_inj.injOn
 intro j u; apply if_neg; intro l; exact u (mem_image.mpr ⟨_,mem_univ _,l⟩)

variable {ι:Type*}{l:Filter ι}{M':ι→Side}(f:Tendsto M' l atTop) {F:ι→Momentum}(e:Tendsto F l (𝓝 (tmap x)))(w:∀ᶠ i in l,Odd (M' i).val)(u:Bound π x)(p:x≠0)
include f e w u p
lemma delayMark(a:Axis): Tendsto (fun i=>glowC (M' i) v (F i) a) l (𝓝 (slat x v a)):=by
 let G:=fun i=> F i+reciprocal v
 have he:Tendsto G l (𝓝 (tmap (x+stem v))):= (map_stem x v).symm ▸ (e.add_const _)
 have hp: x+stem v≠0:=by
    exact norm_pos_iff.mp ((norm_pos_iff.mpr p).trans_le (peaks u (show peers x (x+ stem v) from ⟨v,rfl⟩)))
 unfold slat; rw [show weave _ ^ 8=(weave (x+stem v)^4)^2 from pow_mul _ 4 2]; refine (((decking f he w).pow 2).mul (wrapCost f he hp a)).congr' ?_; filter_upwards [f.eventually (raising v)] with i u; rw [glowC, if_pos u]; unfold roofed aliasAt mon narrow G; rw [u,smul_add]

-- estimates on limit away from x=0.
def tough (x:Bin) : Momentum:=fun i=>∑' l:Cover, slat x l i
omit f e w u p
lemma floor_s {C:ℝ}{a:Axis}(g: 0<C)(d:∀ N:Side,Odd N.val→∀ i:Site N,i≠0→∀ x:Momentum,x∈baseCube→ ‖roofed N x i a‖ ≤ C*decay 2 i) {x: Momentum}(p:x∈baseCube){k:Side}(w:Odd k.val)(v:Cover)(l:v≠0): ‖glowC k v x a‖ ≤ C*income v:=by
 unfold glowC; split
 next h=> exact (d k w (wrap k v) (fun u=> by rw [u,lift_origin] at h; exact l h.symm) x p).trans_eq (by congr 1; exact (income_lift _).symm.trans (congrArg income h))
 rw [norm_zero]; exact (mul_pos g (income_2 _)).le
-- none
-- bug floor_s above include previous f e etc! tune
lemma boundC(a: Axis): ∃ C:ℝ,0<C∧∀ (x:Bin), Bound π x→ x≠0→∀ v:Cover,v≠0→ ‖slat x v a‖≤ C*income v:=by
 obtain ⟨C,k,d⟩:= terrain a; let M:ℕ→Side:=fun i=> ⟨2*i+1,by omega⟩; have he:∀ i,Odd (M i).val:= fun i=> ⟨i,rfl⟩; have hp: StrictMono M:=fun i j t=> (by change 2*i+1<2*j+1; omega)
 refine ⟨C,k, fun x u p v h'=>?_⟩; apply le_of_tendsto_of_tendsto (delayMark (x:=x) (v:=v) (show Tendsto M atTop atTop from tendsto_atTop.mpr (fun (b:Side)=> (eventually_ge_atTop b.val).mono fun (i:ℕ) (v:b.val≤ i)=>show b.val≤2*i+1 from by omega)) tendsto_const_nhds (Eventually.of_forall he) u p a).norm tendsto_const_nhds; exact Eventually.of_forall (fun i=> floor_s k d (b_base u) (he i) v h')
include u p
lemma spending (a:Axis) : Summable (fun i:Cover=>‖slat x i a‖):=by
 obtain ⟨C,k,d⟩:= boundC a; refine Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (f:=fun i:Cover=> C*income i+(Pi.single (0:Cover) ‖slat x 0 a‖ : Cover→ℝ) i) (fun i=>?_) ((wallet.mul_left C).add (hasSum_pi_single (0:Cover) _).summable)
 by_cases l:i=0; · subst i; rw [Pi.single_eq_same]; exact le_add_of_nonneg_left ((mul_pos k (income_2 _)).le)
 rw [Pi.single_eq_of_ne l,add_zero]; exact d x u p i l
include f e w p u
lemma gulch (a:Axis)(P:∀ᶠ i in l,F i∈ baseCube) : Tendsto (fun i=>mixL 4 (M' i) (F i) a) l (𝓝 (tough x a)):=by
 obtain ⟨C,k,d⟩:= terrain a; let b:=‖slat x 0 a‖+1; let bounds (i:Cover):= C*income i+ (Pi.single (0:Cover) b:Cover→ℝ) i
 simp_rw [rolling]; apply tendsto_tsum_of_dominated_convergence (bound:=bounds) ((wallet.mul_left C).add (hasSum_pi_single ..).summable) (fun i=>delayMark i f e w u p a)
 filter_upwards [P,w, (delayMark 0 f e w u p a).norm.eventually (ge_mem_nhds (lt_add_one ‖slat x 0 a‖))] with i p w e; intro j; unfold bounds; by_cases v:j=0
 · subst j; rw [Pi.single_eq_same]; exact le_trans e (le_add_of_nonneg_left ((mul_pos k (income_2 _)).le))
 rw [Pi.single_eq_of_ne v,add_zero]; exact floor_s k d p w j v
end YM.CF.Crest.Shore
#print axioms YM.CF.Crest.Shore.gulch
#print axioms YM.CF.Crest.Shore.spending
