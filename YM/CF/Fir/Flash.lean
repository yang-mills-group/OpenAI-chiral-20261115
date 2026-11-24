/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Fir.Beam
import YM.Next.FREE_KERNELS.Strands
/-! open end uniform strip and Laurent nuclear bounds -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (u:Bool)(j:ℕ)(L M:Side){p:Momentum}
lemma arm_w (l:Site L) (hp:p∈realCube zone)(hg:p≠0): arm u j L M l p=(((Real.sqrt L.val)⁻¹:ℝ):ℂ) • (muff j L (aliasAt p l) • ray u j L M p l) := by by_cases h:l=0 <;> simp [arm,h,chief_eq _ _ _ _ _ hp hg]
lemma warp (l:Site L) (hp:p∈ realCube zone)(x:Cover)(hx:p+reciprocal x∈realCube zone): arm u j L M l (p+reciprocal x)=arm u j L M (l+wrap L x) p:=by
  by_cases h:x=0
  · simp [h, show reciprocal (0:Cover)=0 from (funext fun i=> by simp [reciprocal])]
  obtain ⟨he,hg⟩:= overlap_regular h hp hx
  rw [arm_w _ _ _ _ _ hx hg,arm_w _ _ _ _ _ hp he]; obtain ⟨y,hy⟩:=alias_exchange p l x
  unfold ray bent; rw [hy,muff_period,mix_period,bar_overlap _ _ hp x hx]

/-- input residue surface, output to input normalizations L^-2. -/
def paint (r: Site L)(D:List Axis)(p:Momentum) := ∑ l:Site L,
     mode (aliasAt p l) (lift r) • ((listChip (aliasAt p l) D*toll L 2) • arm u j L M l p)
lemma spans (r:Site L) (D)(hp:p∈realCube zone)(x:Cover)(hx:p+reciprocal x∈realCube zone): paint u j L M r D (p+reciprocal x)=paint u j L M r D p:=by
  unfold paint
  rw [← Equiv.sum_comp (Equiv.addRight (wrap L x)) (fun l=> mode (aliasAt p l) (lift r) • ((listChip (aliasAt p l) D*toll L 2) • arm u j L M l p))]
  refine sum_congr rfl fun i _=>?_
  rw [warp _ _ _ _ _ hp _ hx]; obtain ⟨y,hy⟩:= alias_exchange p i x
  rw [hy,Secured.list_repeat]; simp only [mode_phase,mode_periodic,mul_one]; rfl
variable {ι : Type*}(L M:ι→Side)(h:∀ i,Odd (L i).val)(e:∀ i,Odd (M i).val)
include h in
lemma pen (l:∀ i,Site (L i))(D:List Axis)(a): Moderate (fun i=> (grade (l i))^D.length / ((L i).val:ℝ)^(D.length+a)) fun i p=> listChip (aliasAt p (l i)) D*toll (L i) a:=by
  induction D generalizing a with
  | nil=> simp only [List.length_nil,Nat.zero_add,pow_zero,listChip,List.map_nil,List.prod_nil,one_mul]; apply Moderate.bounded_const _ 1 one_pos; intro i; simp [toll,norm_pow,one_div]
  | cons d r ih=>
    have he:= (scaled_seed L (fun _=>1) h l (fun _=>d)).raise_price (u:=fun i=>grade (l i)) (fun _=> up_le ..)
    convert he.mul (ih (a+1)) using 2
    · simp only [List.length_cons, add_right_comm _ _ a]; ring
    ext1 p
    simp only [listChip, List.map_cons,List.prod_cons, toll,pow_succ,seedQ,narrow]; simp; field_simp
include h in
lemma peak (l r:∀ i,Site (L i)): Moderate (fun _:ι=>1) fun i p=> mode (aliasAt p (l i)) (lift (r i)):=by
  refine ⟨zone,Real.exp (4*zone),zone_pos,Real.exp_pos _,fun i=>⟨fun p hp=>?_,fun p hp=>?_⟩⟩
  · unfold mode aliasAt; fun_prop
  let n : Side := L i
  have hm := reward (aliasAt p (l i)) (lift (r i)) (zone/n.val)
    (fun x => ((alias_in_cube_precise hp (l i) (h i)).1 x).le)
  rw [mul_one]; apply hm.trans; apply Real.exp_le_exp.mpr
  have he : Laurent.size (lift (r i)) ≤ 4*n.val := by
    unfold Laurent.size
    have hh (x : Axis) : (lift (r i) x).natAbs≤n.val := by obtain hh := lift_centers (r i) x; unfold n; omega
    exact (Finset.sum_le_sum fun i _ => hh i).trans (le_of_eq (by simp [Axis]))
  rw [mul_comm,← mul_div_assoc,div_le_iff₀ (side_pos _)]
  have hh : (Laurent.size (lift (r i)):ℝ) ≤ 4*n.val := by exact_mod_cast he
  nlinarith [zone_pos]
include h e in
lemma portrait (r:∀ i, Site (L i))(D:List Axis)(hx:D.length+2≤j): Pay (fun i=> Real.sqrt (L i).val / ((L i).val:ℝ)^(D.length+2)) fun i =>paint u j (L i) (M i) (r i) D :=by
  refine ⟨fun i=>by positivity,fun a b=> ?_⟩; simp only [paint,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let f i:= Real.sqrt (L i).val / ((L i).val:ℝ)^(D.length+2)
  let s (i:ι) : Finset (Site (L i)):=univ
  obtain ⟨B,hB,H⟩:= decay_cost
  apply Moderate.sum_family s (fun i l=> f i*decay 2 l) ⟨B,hB,fun i=> by rw [← Finset.mul_sum,mul_comm B]; exact mul_le_mul_of_nonneg_left (H _) (by unfold f; positivity)⟩
  let W:= Σ i:ι, {l//l∈s i}; let q(w:W):ι:=w.1; let l(w:W):Site (L w.1):=w.2
  have he := (armPay u j (by omega) (L ∘ q) (M ∘ q) (fun i=>h _) (fun i=>e _) l).tap a b
  have hg:= (peak (L ∘ q) (fun i=>h _) l (fun i=>r _)).mul ((pen (L ∘ q) (fun i=>h _) l D 2).mul he)
  apply hg.raise_price; intro i; dsimp only [q,f,Function.comp_apply] at *; rw [one_mul]
  have hm := ((mul_le_mul_of_nonneg_left (decay_anti (l i) (show 2+D.length≤j by omega)) (pow_nonneg (grade_pos (l i)).le D.length)).trans (absorbs ..))
  calc
    _ = f i.1*((grade (l i))^D.length*decay j (l i)):= by dsimp only [f]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by unfold f; positivity)
end YM.CF.Fir
