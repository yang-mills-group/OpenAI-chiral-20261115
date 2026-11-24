/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Braid.Forms
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r:ℕ}
lemma sized (i:α)(x:Shift α)(y:ℤ)(h:y.natAbs ≤ (x i).natAbs): size (update x i y) ≤ size x:=by
 unfold size; refine sum_le_sum (fun j _=>?_); by_cases H:j=i
 · rw [H,update_self]; exact h
 rw [update_of_ne H];
lemma leg_m (i:α)(x:Shift α)(h:size x ≤ M): Pond M M (seriesLeg i x):=by
 have he : (x i).natAbs ≤ M:= (single_le_sum (f:=fun j=>(x j).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans h
 let s:= Finset.range (x i).natAbs; have hz : ∑ j∈s,(1:ℝ) ≤ (M:ℝ):=by simp only [s, sum_const, card_range,nsmul_eq_mul,mul_one]; exact Nat.cast_le.mpr he
 have hf (q:ℕ→ℤ)(hp:∀ j∈s,(q j).natAbs ≤ (x i).natAbs): Pond M M (fun p:Phase α=> ∑ j∈s, mode p (update x i (q j))):=by
    apply (fundsF s _ (fun _=>1) (fun j hj=>?_)).mono hz le_rfl
    have hv:= Pond.modes (1:ℂ) (update x i (q j)); simp only [norm_one,mul_one] at hv; exact hv.mono le_rfl ((sized i x _ (hp j hj)).trans h)
 unfold seriesLeg; split
 · exact hf _ (fun i hi => by rw [Int.natAbs_natCast]; exact (mem_range.mp hi).le)
 exact (hf (fun i=>-(i+1:ℤ)) (fun i hi=>by have :=mem_range.mp hi; omega)).neg
lemma Pond.payB {f: Phase α→ℂ}(p:Pond M A f)(i:α):∃ g,Pond M (A*M) g∧∀ x, divZ i x*g x=f x-f (update x i 0):=by
 obtain ⟨S,v,hx,hv,h⟩:=p.there
 let g(x):= ∑ j∈S, seriesLeg i j x*v j; refine ⟨g, (fundsF S _ (fun j=> ‖v j‖*M) (fun j hj=>?_)).mono ?_ le_rfl,?_⟩
 · simp_rw [mul_comm _ (v _)]; exact (leg_m i j (hx j hj)).scal _
 · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hv (by positivity)
 intro x; rw [h,h]; unfold g; rw [←sum_sub_distrib,mul_sum]; apply sum_congr rfl; intro j _; rw [←mul_assoc, seriesLeg_exact, sub_mul]
lemma Pond.reset {f:Phase α→ℂ}(p:Pond M A f)(i:α): Pond M A (fun x=> f (update x i 0)):=by
 apply Pond.travel (N:=M) _ p; intro j he
 have hh(x:Phase α): mode (update x i 0) j=mode x (update j i 0)*1:=by rw [mul_one]; unfold mode; congr 2; exact sum_congr rfl fun j _=>by by_cases j=i <;> simp [*]
 simp_rw [hh]; exact (Pond.modes _ _).mono (norm_one.le) ((sized i j _ (by simp)).trans he)
lemma Board.add {f g:SheetLeg α ξ r}(h:Board M A f)(hp:Board M C g):Board M (A+C) (f+g):=fun i x=> (h i x).add (hp i x)
lemma Board.sub {f g:SheetLeg α ξ r}(h:Board M A f)(hp:Board M C g):Board M (A+C) (f-g):=fun i x=> (h i x).rest (hp i x)
lemma Board.mono {f:SheetLeg α ξ r}(h:Board M A f)(hp:A≤ C)(he:M ≤ N):Board N C f:=fun i x=> (h i x).mono hp he
variable (m':Axis↪α) (i:Axis)
private lemma comb_wall {f : SheetLeg α ξ r} {U : Corn α → Submodule ℂ (ξ → ℂ)} (hU : Uniforms ξ α m' U) (h : wall U f) : wall U (comb m' i f) := by
  have hv (p) : U p = U (update p (m' i) 0) := hU p _ (by
    intro a hn; by_cases he : a=m' i
    · exact False.elim (hn (he.symm ▸ Set.mem_range_self _))
    simp [he])
  intro p a
  by_cases hi : i∈a.val
  · rw [show comb m' i f (axes p) a=0 from funext fun _ => if_pos hi]; exact (U p).zero_mem
  rw [show comb m' i f (axes p) a=f (update (axes p) (m' i) 0) a from funext fun _ => if_neg hi]
  rw [hv p, show update (axes p) (m' i) 0=axes (update p (m' i) 0) by ext1 j; by_cases h : j=m' i <;> simp [h,axes]]
  exact h _ _

private lemma symbol_update (p : Corn α) : q (projected m' (axes p)) =
    q (projected m' (axes (update p (m' i) 0))) + divZ (m' i) (axes p) • Pi.single i 1 := by
  ext1 j
  by_cases h : i=j
  · subst j; simp [q,projected,axes,divZ]
  simp [Ne.symm h,q,projected,axes]

private lemma cob_comb_core {f : SheetLeg α ξ r} (hc : Cycles (projected m') r f) (p : Corn α)
    (hp : divZ (m' i) (axes p) ≠ 0) (D : TypeFace r → ℂ) (x : ξ)
    (hd : divZ (m' i) (axes p) • D =
        (fun A => f (axes p) A x) - (fun A => f (axes (update p (m' i) 0)) A x)) :
    (symbol r (projected m' (axes p))).transpose *ᵥ ((left ℂ r i) *ᵥ D) =
      (fun A => f (axes p) A x)-(fun A => comb m' i f (axes p) A x) := by
  let z := projected m' (axes p)
  let p₀ := update p (m' i) 0
  let z₀ := projected m' (axes p₀)
  let d := divZ (m' i) (axes p)
  have he : update (axes p) (m' i) 0 = axes p₀ := by
    ext1 b; by_cases h : b=m' i <;> simp [p₀,h,axes]
  conv_rhs => arg 2; intro A; unfold comb; rw [he]
  cases r with
  | zero =>
    rw [symbol,cartan_0, show q (projected m' (axes p)) i=d from rfl]; apply hd.trans; congr 1
    ext1 a; simp [show i∉a.val by rw [vac_only a]; exact notMem_empty _]; rfl
  | succ r =>
    let v := fun A => f (axes p) A x
    let u := fun A => f (axes p₀) A x
    have h1 : (wedge r (q z)).transpose *ᵥ v=0 := by
      funext a; exact congr_fun (congr_fun (hc p) a) x
    have h0 : (wedge r (q z₀)).transpose *ᵥ u=0 := by
      funext a; exact congr_fun (congr_fun (hc p₀) a) x
    have hh : wedge r (q z)=wedge r (q z₀)+d • left ℂ r i := by
      rw [show q z=_ from symbol_update m' i p]
      simp only [wedge,Pi.add_apply, add_smul, sum_add_distrib, Pi.smul_apply,Pi.single_apply]
      simp [ite_smul,z₀,d,p₀]
    have hD : d • D=v-u := hd
    have hp' : (left ℂ r i)*ᵥ ((wedge r (q z)).transpose *ᵥ D) = -((left ℂ r i)*ᵥ ((left ℂ r i).transpose *ᵥ u)) := by
      apply smul_right_injective (r:=d) _ hp
      dsimp only
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul,hD,Matrix.mulVec_sub,h1,zero_sub,hh,
        Matrix.transpose_add,Matrix.add_mulVec,h0,zero_add,Matrix.mulVec_neg,Matrix.transpose_smul,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_neg]
    have hy := cartan_remove D (q z) i; rw [hp',show q z i=d from rfl,hD] at hy
    have hV : _ = ((left ℂ r i)*ᵥ ((left ℂ r i).transpose *ᵥ u)) + (v-u) := eq_add_of_neg_add_eq hy
    apply hV.trans
    ext1 a
    rw [Pi.add_apply,cartan_project]
    by_cases H : i ∈ a.val <;> simp [p₀,u,v,H]



private lemma cob_step  (ha : 0 ≤ A) (f : SheetLeg α ξ r)
    {s : ℕ} (hf : Board M A f) (hv : Cycles (projected m') r f) (hk : JetWall s f)
    {U} (hU : Uniforms ξ α m' U) (hw : wall U f) :
    let g := comb m' i f
    Board M A g ∧ Cycles (projected m') r g ∧ JetWall s g ∧ wall U g ∧
    ∃ B : SheetLeg α ξ (r+1), Board M (A*M) B ∧ JetWall (s-1) B ∧
      wall U B ∧ ∀ p : Corn α, f (axes p)= (cob r (projected m') B) (axes p)+g (axes p) := by
  intro g
  have hg: Board M A (comb m' i f):=by
    intro a x; unfold comb; split; · exact Pond.zeros.mono ha le_rfl
    exact (hf a x).reset _
  choose D hD he using fun a x => (hf a x).payB _
  let B : SheetLeg α ξ (r+1) := fun p a x => (left ℂ r i *ᵥ (fun b => D b x p)) a
  have hB : Board M (A*M) B := by
    intro a x
    unfold B; simp_rw [eliminate]
    split; next h => exact ((hD (Exterior.remove i a h) x).scal (parity a.val i ℂ)).mono (by simp [parity]) le_rfl
    exact Pond.zeros.mono (mul_nonneg ha (Nat.cast_nonneg _)) le_rfl
  have hh b x p : divZ (m' i) (axes p) * D b x (axes p)=f (axes p) b x - f (axes (update p (m' i) 0)) b x := by
    rw [he b x _, show axes (update p (m' i) 0)= update (axes p) (m' i) 0 by
      ext1 a; by_cases h : a=m' i <;> simp [h,axes]]
  have hj : JetWall (s-1) B := by
    have heD b x := rays_div (f:=fun p => f p b x) (i:=m' i) (hD b x).analytic (hk b x)
      (fun p => he b x _)
    intro a x p
    unfold B; simp_rw [eliminate]; split
    next h => exact (heD (Exterior.remove i a h) x p).const_mul_left (parity a.val i ℂ)
    exact isBigO_zero ..
  have hy : ∀ p : Corn α, cob r (projected m') B (axes p)=f (axes p)-g (axes p) := by
    intro p; funext a x
    let l (p : Corn α) := cob r (projected m') B (axes p) a x
    have H : ContinuousAt l p := by
      suffices h : ∀ p, ContinuousAt l p from h p
      rw [← continuous_iff_continuousAt]
      unfold l cob Matrix.mulVec dotProduct
      refine continuous_finsetSum _ (fun j hj => ?_)
      refine Continuous.mul ?_ (continuous_iff_continuousAt.mpr fun v => ((hB j x).analytic.analytic_real v).continuousAt)
      simp only [symbol,q,wedge,projected,Function.comp_apply,Matrix.transpose_apply,Matrix.sum_apply, Matrix.smul_apply]
      apply continuous_finsetSum; intro i _; dsimp only [axes]; fun_prop
    have H' := ((hf a x).analytic.analytic_real p).continuousAt.sub ((hg a x).analytic.analytic_real p).continuousAt
    refine tendsto_nhds_unique_of_eventuallyEq (H.tendsto.comp (shadows p (m' i)))
      (H'.tendsto.comp (shadows p (m' i))) ?_
    filter_upwards [shadow_fee p (m' i)] with t ht
    let q := shadow p (m' i) t
    exact congr_fun (cob_comb_core m' i hv q ht (fun b => D b x (axes q)) _ (funext fun b => hh b x q)) a
  have hv' : Cycles (projected m') r g := by
    cases r with
    | zero => trivial
    | succ r =>
      intro p; funext a x
      let c := axes p
      have H := congr_fun (congr_fun (congr_fun (cob_zero r (projected m') B) c) a) x
      have z : cob r (projected m') (f-g) c a x=0 := by
        change ((symbol r _).transpose *ᵥ _) a=0
        rw [show (fun y => (f-g) c y x) = (fun y => cob (r+1) (projected m') B c y x) from
          funext fun b => (congr_fun (congr_fun (hy p) b) x).symm]; exact H
      rw [cob_sub] at z
      simp only [Pi.sub_apply] at z
      exact (sub_eq_zero.mp z).symm.trans (congr_fun (congr_fun (hv p) a) x)
  refine ⟨hg,hv',jet_comb m' i hk,comb_wall m' i hU hw,B,hB,hj,?_,fun p => by rw [hy]; abel⟩
  have hm (p : Corn α) (b) : (fun x => D b x (axes p))∈U p := by
    have hΔ a (k : ℝ) : U a = U (update a (m' i) k) := hU a _ (by
      intro v he; by_cases h : v=m' i
      · exact False.elim (he (h.symm ▸ Set.mem_range_self _))
      simp [h])
    have h (p : Corn α) : ContinuousAt (fun p => fun x => D b x (axes p)) p :=
      continuousAt_pi.mpr fun j => ((hD b j).analytic.analytic_real p).continuousAt
    apply (U p).closed_of_finiteDimensional.mem_of_tendsto ((h p).tendsto.comp (shadows p (m' i)))
    filter_upwards [shadow_fee p (m' i)] with t ht
    let q := shadow p (m' i) t
    rw [show U p=U q from hΔ p _]
    change (fun x => D b x (axes q)) ∈ _
    let R := divZ (m' i) (axes q) • (fun x => D b x (axes q))
    have hp : R∈U q := by rw [show R = _ - f (axes (update q (m' i) 0)) b from funext fun x => hh b x q]; apply (U q).sub_mem (hw q b); rw [hΔ q 0]; exact hw _ _
    exact ((U q).smul_mem_iff ht).mp hp
  intro p b
  by_cases H : i∈b.val
  · rw [show B (axes p) b=parity b.val i ℂ • fun x => D (Exterior.remove i b H) x (axes p) from funext fun x => by simp [B, eliminate,H]]
    exact (U p).smul_mem _ (hm ..)
  rw [show B (axes p) b=0 from funext fun x => by simp [B,eliminate,H]]
  exact (U p).zero_mem

private def purge (f : SheetLeg α ξ r) : List Axis → SheetLeg α ξ r
  | [] => f
  | i::l => purge (comb m' i f) l

private lemma allcombs  (ha : 0 ≤ A) (l : List Axis) (f : SheetLeg α ξ r) {s : ℕ} (hf : Board M A f)
    (hv : Cycles (projected m') r f) (hk : JetWall s f) {U} (hU : Uniforms ξ α m' U) (hw : wall U f) :
    ∃ B : SheetLeg α ξ (r+1), Board M (A*(l.length*(M:ℝ))) B ∧ JetWall (s-1) B ∧
      wall U B ∧ ∀ p : Corn α, f (axes p)=cob r (projected m') B (axes p)+purge m' f l (axes p) := by
  induction l generalizing f with
  | nil =>
    refine ⟨0,fun b x => ?_,fun b x p => isBigO_zero ..,fun p _ => (U p).zero_mem,fun p => ?_⟩
    · simp only [List.length_nil,Nat.cast_zero,zero_mul,mul_zero,Pi.zero_apply]; exact Pond.zeros
    funext i x; simp [cob,purge,Matrix.mulVec,dotProduct]
  | cons i l ih =>
    obtain ⟨ht,h1,h2,h3,X,hX,h4,h5,h6⟩ := cob_step m' i ha f hf hv hk hU hw
    obtain ⟨Y,hY,h7,h8,h9⟩ := ih _ ht h1 h2 h3
    refine ⟨X+Y, ?_,fun a x => Rays.add (h4 a x) (h7 a x),fun p i => (U p).add_mem (h5 p i) (h8 p i),fun p => ?_⟩
    · rw [List.length_cons,Nat.cast_add_one,show A*(((_ : ℝ)+1)*(M:ℝ))=A*((M:ℝ))+A*(l.length*(M:ℝ)) by ring]
      exact Board.add hX hY
    rw [h6 p,h9 p, cob_add,purge]; simp [add_assoc]

private lemma purge_hit (f : SheetLeg α ξ r) (l : List Axis) (a : TypeFace r) (p : Corn α) :
    ∃ q : Corn α, (∀ j ∈ l, q (m' j) = 0) ∧
        (∀ j ∉ l.map m', q j=p j) ∧
        purge m' f l (axes p) a = if ∀ i ∈ a.val,i ∉ l then f (axes q) a else 0 := by
  classical
  induction l generalizing f p with
  | nil => exact ⟨p,by simp, by simp,by simp [purge]⟩
  | cons i l IH =>
    obtain ⟨q,H,K,ht⟩ := IH (comb m' i f) p
    refine ⟨update q (m' i) 0, ?_, ?_,?_⟩
    · intro j hj; by_cases h : j=i; simp [h]
      rw [update_of_ne (m'.injective.ne h)]; exact H _ (by simpa [h] using hj)
    · intro j hj; simp only [List.map_cons,List.mem_cons,not_or] at hj
      rw [update_of_ne hj.1]; exact K _ hj.2
    rw [purge,ht]; by_cases h : i∈a.val
    · split <;> rename_i u <;> rw [if_neg (fun H => H i h (by simp))]
      exact funext fun _ => if_pos h
    have he : (∀ j∈a.val,j∉i::l) ↔ ∀ j∈a.val,j∉l := by
      constructor
      · intro hf j hj hn; exact hf j hj (by simp [hn])
      intro hf j hj hx; simp only [List.mem_cons] at hx
      exact hx.elim (fun H => h (H ▸ hj)) (hf j hj)
    simp only [he]
    split <;> rename_i hu; swap; rfl
    funext x
    unfold comb
    rw [if_neg h, show update (axes q) (m' i) 0=axes (update q (m' i) 0) by
      ext1 j; by_cases h : j=m' i <;> simp [*,axes]]

/-- The real analytic one-leg solve. Even degree zero, where its right
hypothesis is image-vanishing. Returns a width funded before any evaluation. -/
theorem wall_pull  (ha : 0 ≤ A) (f : SheetLeg α ξ r) {s : ℕ} (hf : Board M A f)
    (hv : Cycles (projected m') r f) (he : r≠0 ∨ ∀ p : Corn α, p ∘ m' = 0 → f (axes p)=0)
    (hk : JetWall s f) {U} (hU : Uniforms ξ α m' U) (hw : wall U f) :
    ∃ B : SheetLeg α ξ (r+1), Board M (A*(4*(M:ℝ))) B ∧ JetWall (s-1) B ∧
      wall U B ∧ ∀ p : Corn α, f (axes p)=cob r (projected m') B (axes p) := by
  obtain ⟨B,H,h1,h2,h3⟩ := allcombs m' ha (List.finRange 4) f hf hv hk hU hw
  refine ⟨B, ?_, h1,h2,fun p => ?_⟩
  · simpa only [List.length_finRange,Nat.cast_ofNat] using H
  rw [h3 p]; suffices hh : purge m' f (List.finRange 4) (axes p)=0 by rw [hh,add_zero]
  funext a
  obtain ⟨q,hq,-,hx⟩ := purge_hit m' f (List.finRange 4) a p
  apply hx.trans; split <;> rename_i hj; swap; rfl
  rcases he with he|he
  · have hv : a.val.Nonempty := card_pos.mp (a.property.symm ▸ Nat.pos_of_ne_zero he)
    obtain ⟨j,hj'⟩ := hv
    exact (hj j hj' (List.mem_finRange _)).elim
  exact congr_fun (he q (funext fun j => hq j (List.mem_finRange j))) a

end YM.CF.Braid
