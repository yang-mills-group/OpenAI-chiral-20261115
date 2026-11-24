import YM.CF.Scroll.Coat

/-!
# `gaugeM` needs `cloth` with a *finite* stencil

Here is the key to obtaining it. This is not merely a bound or exponential
locality. Proof of laurent support uses the alias-block formula of brix
ON the torus; summing aliases of integer modes kills the non-multiples of L.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Aliases
open Function Fock Filter NormedSpace Lat Lattice Branch Finset Laurent Bloch Next.Free Fir Rush Scroll
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
attribute [local instance] opCStarAlgebra

-- all momenta (claim of physical agreement on baseCube for brix below)
private abbrev harmonics := Submodule.span ℂ (Set.range fun x:Cover => fun p:Momentum => mode p x)
private lemma pure_h (x : Cover) : (fun p:Momentum=> mode p x) ∈ harmonics := Submodule.subset_span ⟨_,rfl⟩
private lemma one_h : (1:Momentum → ℂ) ∈ harmonics := by
  rw [show (1:Momentum→ℂ)=(fun p:Momentum=>mode p 0) from funext fun p=> (mode_zero p).symm]; exact pure_h 0
private lemma const_h (c:ℂ) : (fun _:Momentum=> c) ∈ harmonics := by
  rw [show (fun _:Momentum=> c)= c • (1:Momentum → ℂ) from funext fun p => by simp]; exact harmonics.smul_mem _ one_h
private lemma mul_h {f g} (p : f ∈ harmonics) (q : g ∈ harmonics) : (f*g) ∈ harmonics := by
  induction p using Submodule.span_induction with
  | mem f h =>
    obtain ⟨x,rfl⟩ := h; induction q using Submodule.span_induction with
    | mem g h =>
      obtain ⟨y,rfl⟩:= h
      exact (show ((fun p:Momentum=> mode p (x+y)))=(fun p:Momentum=> mode p x)*(fun p=> mode p y) from funext fun p=> mode_shift ..) ▸ pure_h _
    | zero => rw [mul_zero]; exact harmonics.zero_mem
    | add a b _ _ h k=> rw [mul_add]; exact harmonics.add_mem h k
    | smul _ a _ ih=> rw [Algebra.mul_smul_comm]; exact harmonics.smul_mem _ ih
  | zero => rw [zero_mul]; exact harmonics.zero_mem
  | add a b _ _ h k=> rw [add_mul]; exact harmonics.add_mem h k
  | smul _ a _ ih => rw [Algebra.smul_mul_assoc]; exact harmonics.smul_mem _ ih
private lemma sum_h {ι:Type*} (s:Finset ι) {f:ι→ Momentum →ℂ} (h : ∀ i∈s,f i∈harmonics) : (fun p =>∑ i∈s,f i p)∈harmonics := by
  rw [show (fun p =>∑ i∈s,f i p)=(∑ i∈s,f i) from funext fun p=>(Finset.sum_apply ..).symm]; exact harmonics.sum_mem h
private lemma prod_h {ι:Type*} (s:Finset ι) {f:ι→ Momentum →ℂ} (h : ∀ i∈s,f i∈harmonics) : (fun p =>∏ i∈s,f i p)∈harmonics := by
  classical
  induction s using Finset.induction with
  | empty=> simp_rw [Finset.prod_empty]; exact one_h
  | @insert i s k ih =>
    simp_rw [prod_insert k]; exact mul_h (h i (mem_insert_self ..)) (ih fun i g=> h i (mem_insert_of_mem g))
private lemma twirl_h (i:Axis)(k:ℤ): (fun p:Momentum=> twirl (p i) k) ∈ harmonics := by
  rw [show (fun p:Momentum=> twirl (p i) k)=(fun p:Momentum=> mode p (Pi.single i k)) from ?_]; exact pure_h _
  funext p; unfold twirl mode; rw [sum_eq_single i]; · simp; congr 1; ring
  · intro b _ hb; simp [hb]
  simp
private lemma plank_h (L:Side) (i: Axis) : (fun p:Momentum=> plank L (p i)) ∈ harmonics := by
  simp_rw [plank_centers]; exact mul_h (const_h _) (sum_h _ (f:=fun k p=>_) (fun _ _=>twirl_h i _))
private lemma muff_h (L: Side) (j : ℕ) : (muff j L) ∈ harmonics := by
  have he:(fun p:Momentum =>∏ i, plank L (p i))∈harmonics:=prod_h _ (f:=fun i p=>_) (fun k _=>plank_h L k)
  induction j with
  | zero => rw [show muff 0 L=(1:Momentum→ℂ) from funext fun p=> by simp [muff]]; exact one_h
  | succ j ih=>
    have hp: muff (j+1) L=muff j L*(fun p:Momentum=> ∏ i,plank L (p i)):=funext fun p=>by simp [muff,pow_succ]
    rw [hp]; exact mul_h ih he

private lemma alias_h (L:Side) (f:Momentum→ℂ) (hf:f∈ harmonics) :
    (fun p:Momentum=>∑ l:Site L,f (aliasAt p l))∈harmonics := by
  induction hf using Submodule.span_induction with
  | mem f v=>
    obtain ⟨x,rfl⟩:=v
    by_cases h:wrap L x=0
    · obtain ⟨y,he⟩ := cover_of_eq (n:=L) 0 x (by rw [h,map_zero]); rw [zero_add] at he
      subst x; simp_rw [← mode_scale, alias_scale,mode_phase,mode_periodic,mul_one,sum_const,card_univ]
      exact harmonics.nsmul_mem (pure_h _) _
    have he(p:Momentum): (∑ l:Site L,mode (aliasAt p l) x)=0 := by
      unfold aliasAt; simp_rw [mode_phase,←cell_wrap,cell_duality _ (wrap L x), ←mul_sum,sum_cell h, mul_zero]
    simp_rw [he]; exact harmonics.zero_mem
  | zero => simp_rw [Pi.zero_apply,Finset.sum_const_zero]; exact harmonics.zero_mem
  | add a b _ _ h k=> simp_rw [Pi.add_apply,sum_add_distrib]; exact harmonics.add_mem h k
  | smul _ a _ ih=> simp_rw [Pi.smul_apply,← smul_sum]; exact harmonics.smul_mem _ ih

private lemma oneColumn_h (j:ℕ) (L:Side) (x:Cover) :
    (fun p:Momentum=>∑ l:Site L, ((L.val:ℂ)^2)⁻¹*mode (aliasAt p l) x*money j L l p) ∈ harmonics := by
  let t := ((L.val:ℂ)^2)⁻¹ * (((Real.sqrt L.val)⁻¹:ℝ):ℂ)
  let f := (fun p:Momentum=>t)*((fun p=>mode p x)*muff j L)
  have h : (fun p:Momentum=>∑ l:Site L, ((L.val:ℂ)^2)⁻¹*mode (aliasAt p l) x*money j L l p) = (fun p=>∑ l:Site L,f (aliasAt p l)) := by
    funext p; apply sum_congr rfl; intro i _; simp only [money, f,t, Pi.mul_apply]; ring
  rw [h]; exact alias_h L f (mul_h (const_h _) (mul_h (pure_h x) (muff_h L j)))

private lemma brix_support_formula (j:ℕ) (L: Side) (a k : St L) : ∃ f∈harmonics, ∀ p∈baseCube,brix j L p a k=f p := by
  let U(p:Momentum):=if k.1=0 then ∑ l:Site L,((L.val:ℂ)^2)⁻¹*mode (aliasAt p l) (lift a.1)*money j L l p else if a.1=k.1 then (1:ℂ) else 0
  have h: U ∈ harmonics := by unfold U; split; exact oneColumn_h j L (lift a.1); apply const_h
  refine ⟨U * fun _=>(1:Op SpinIdx) a.2 k.2,mul_h h (const_h _),?_⟩
  intro p hp; exact congr_fun (congr_fun (Scroll.tapeB L p j a.1 k.1 hp.1) a.2) k.2

private lemma harmonics_read {f: Momentum→ℂ} (g:f∈harmonics):
    ∃ c:Cover→ℂ, (Function.support c).Finite ∧ Laurent.read c=f := by
  classical
  have hh(p:Momentum)(c:Cover→ℂ)(f:(Function.support c).Finite) : Summable fun x=>mode p x • c x := by
    apply summable_of_ne_finset_zero (s:=f.toFinset); intro b h; rw [show c b=0 from Function.notMem_support.mp (fun i=> h (f.mem_toFinset.mpr i)),smul_zero]
  induction g using Submodule.span_induction with
  | mem f h=>
    obtain ⟨x,rfl⟩:=h; refine ⟨Pi.single x 1,?_,?_⟩
    · apply (Set.finite_singleton x).subset; intro y hy; by_contra h; exact hy (by simp only [Pi.single_eq_of_ne (show y≠x from h)])
    funext p; unfold Laurent.read; rw [tsum_eq_single x]; simp; intro b h; simp [h]
  | zero=> exact ⟨0,by simp,funext fun p=>by simp [Laurent.read]⟩
  | add a b _ _ h k=>
    obtain ⟨c,e,rfl⟩:=h; obtain ⟨d,h,rfl⟩:=k; refine ⟨c+d,(e.union h).subset (Function.support_add ..),funext fun p=>?_⟩
    unfold Laurent.read; simp_rw [Pi.add_apply,smul_add]; rw [(hh p c e).tsum_add (hh p d h)]
  | smul z f _ ih=>
    obtain ⟨c,h,rfl⟩:=ih; refine ⟨z • c,h.subset ?_,funext fun p=>?_⟩
    · exact Function.support_const_smul_subset ..
    unfold Laurent.read; simp only [Pi.smul_apply, smul_eq_mul]; simp_rw [mul_left_comm _ z (c _)]; rw [tsum_mul_left]

/-- Common to all tori for this block factor/patch. -/
theorem finite_brix (j : ℕ) (L : Side) (h : Odd L.val) : ∃ R:ℕ, ∀ x:Cover, R < Laurent.size x → tub (brix j L) x = 0 := by
  classical
  choose c hc he using fun a k:St L => let Q := brix_support_formula j L a k; harmonics_read Q.choose_spec.1
  let f (x:Cover): Op (St L) := Matrix.of (fun i j => c i j x)
  have heq : Reads f (brix j L) := by
    constructor
    · intro i k; exact summable_of_ne_finset_zero (s:=(hc i k).toFinset) (fun x g=>by
        change ‖c i k x‖ = 0; rw [show c i k x=0 from Function.notMem_support.mp (fun v=>g ((hc i k).mem_toFinset.mpr v)),norm_zero])
    intro p hp i k; exact (congr_fun (he i k) p).trans ((brix_support_formula j L i k).choose_spec.2 p hp).symm
  have hp := Scroll.Reads_u (brix j L) (tub (brix j L)) f (cBrix j L h) heq
  let S:Finset Cover:= univ.biUnion (fun v:St L × St L => (hc v.1 v.2).toFinset)
  rw [hp]; refine ⟨S.sup Laurent.size, fun x H=>?_⟩
  ext i k; by_contra g
  have he : x∈ S := mem_biUnion.mpr ⟨(i,k),mem_univ _,(hc i k).mem_toFinset.mpr (show c i k x≠0 from g)⟩
  exact H.not_ge (Finset.le_sup (f:=Laurent.size) he)
end YM.CF.Buffered.Aliases
