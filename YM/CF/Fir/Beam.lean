import YM.CF.Fir.Prong
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (u:Bool)(j:ℕ)(hj:1≤j){ι: Type*}(L M:ι→Side)(h:∀ i, Odd (L i).val)(e:∀ i, Odd (M i).val)
include hj e in
lemma bent_budget : Pay (fun _:ι=>1) fun i p=> bent u j (M i) p:=by
  cases u; exact (Pay.const 1).sub (barBudget j hj _ e); exact barBudget j hj _ e
lemma Lrent : Moderate (fun i:ι=> ((L i).val:ℝ)) (fun i _=> ((L i).val:ℂ)):= Moderate.bounded_const _ 1 one_pos (fun i=>by simp)
lemma Lrent2 : 1≤ fun i:ι=> ((L i).val:ℝ):=fun i=>by change (1:ℝ)≤↑(L i).val; exact_mod_cast (L i).property
include hj h e in
lemma chiefPay : Pay (fun i => ((L i).val:ℝ)) fun i p=> chief u j (L i) (M i) p:=by
  let C i:= L i*M i; have hc : ∀ i, Odd (C i).val := fun i=> (h i).mul (e i)
  have hb : Pay (fun _:ι=>1) fun i p=> zen (extras j (M i) (narrow (L i) p)):=by simpa only [alias_zero_eq] using (zenBudget (fun _=>zero_le_one) _ (extras_pay j hj M e)).on_alias L h (fun _=>0)
  have hx := (((Pay.const 1).sub hb).times (Pay.const (angle u))).times (bent_budget u j hj C hc)
  have he1 : Moderate (fun _:ι=>1) fun i p=> bloom j (M i) (narrow (L i) p):=by simpa only [alias_zero_eq] using (bloomPay j M e).on_alias L h (fun _=>0)
  have he := ((Lrent L).mul he1).mul (invMass j hj C hc)
  have hy := ((zenBudget (fun _=>zero_le_one) _ (ds_cost C)).times (Pay.const (angle u))).times ((Pay.const 1).add (zenBudget (fun _=>zero_le_one) _ (extras_pay j hj C hc)))
  have hm := (Pay.const (1-angle u)).scale ((bloomPay j C hc).mul (C_cost _ hc))
  simp only [mul_one] at hx hy he hm; have hd:=(hy.sub hm).scale he; simp only [mul_one] at hd; exact (hx.raise (Lrent2 L)).sub hd

include hj h e in
lemma flarePay (l:∀ i,Site (L i))(hn:∀ i,l i ≠0) (a:Axis): Moderate (fun i=> ((L i).val:ℝ)) fun i p=> mixL j (M i) (aliasAt p (l i)) a:=by
  have hh:= (ink _ _ e h l).inv (lamp _ _ h l hn) (fun i=>pow_pos (grade_pos _) _)
  have he:= (bloomPay j M e).on_alias L h l
  have hy:= (ds_scaled M L h l a)
  have hz:= (((Lrent L).mul he).mul hh).mul hy
  let K (i:ι):= ((L i).val:ℂ)
  have hw: Moderate (fun i:ι=> ((L i).val:ℝ)) fun i p=> (bloom j (M i) (aliasAt p (l i))*(D (M i) (aliasAt p (l i)))⁻¹)*ds (M i) (aliasAt p (l i)) a:=by
    apply switchPay hz
    · intro i; dsimp only; rw [mul_one]; let k:=grade (l i); have hk:0<k:=grade_pos _; have hm:1 ≤ k:=grade_ge _; change (↑(L i).val:ℝ)* (k^2)⁻¹*k ≤ _
      rw [mul_assoc]; refine mul_le_of_le_one_right (side_pos _).le ?_; rw [inv_mul_eq_div, div_le_one (pow_pos hk _)]; nlinarith
    refine ⟨1,one_pos,fun i p _=>?_⟩; simp only [mul_inv,← inv_pow]; field_simp
  simp_rw [mix_com,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; exact (((extras_pay j hj M e a).on_alias L h l).raise_price (Lrent2 L)).add hw
include hj h e in
lemma rosePay (l:∀ i,Site (L i))(hn:∀ i,l i≠0) : Pay (fun i=> ((L i).val:ℝ)) fun i p=> ray u j (L i) (M i) p (l i) := by
  have he:= zenBudget (fun i=> (side_pos _).le) _ (flarePay j hj L M h e l hn)
  have hh:= ((((Pay.const (1:Op SpinIdx)).raise (Lrent2 L)).sub he).times (Pay.const (angle u))).times (bent_budget u j hj (fun i=> L i*M i) (fun i=> (h i).mul (e i)))
  simpa only [ray,mul_one] using hh
omit h e hj in
lemma stitch {Ω : ι→Prop}[DecidablePred Ω] {w:ι→ℝ}{f:ι→Momentum→Op SpinIdx} (hf: Pay (fun i : {i // Ω i}=> w i) fun i=> f i) (hg: Pay (fun i:{i // ¬Ω i}=> w i) fun i=> f i) : Pay w f:=by
  refine ⟨fun i=>?_,fun a b=>?_⟩
  · by_cases he:Ω i; exact hf.site ⟨i,he⟩; exact hg.site ⟨i,he⟩
  obtain ⟨η,C,hp,hC,H⟩:= hf.tap a b; obtain ⟨θ,B,hθ,hB,G⟩:= hg.tap a b
  refine ⟨min η θ,C+B,lt_min hp hθ,add_pos hC hB,fun i=>?_⟩
  by_cases he:Ω i
  · exact (H ⟨i,he⟩).mono (min_le_left ..) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (hf.site ⟨i,he⟩))
  exact (G ⟨i,he⟩).mono (min_le_right ..) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) (hg.site ⟨i,he⟩))

def arm (u:Bool)(j:ℕ)(L M:Side)(l:Site L)(p:Momentum) := (((Real.sqrt L.val)⁻¹:ℝ):ℂ) • (muff j L (aliasAt p l) • (if l=0 then chief u j L M p else ray u j L M p l))
include hj h e in
lemma armPay (l:∀ i,Site (L i)): Pay (fun i=> Real.sqrt (L i).val*decay j (l i)) fun i p=> arm u j (L i) (M i) (l i) p:=by
  let X (i:ι)(p:Momentum) := if l i=0 then chief u j (L i) (M i) p else ray u j (L i) (M i) p (l i)
  have hh : Pay (fun i=> ((L i).val:ℝ)) X := by
    apply stitch (Ω:=fun i=>l i=0)
    · have hx (i:{i//l i=0}): X i=(chief u j (L i) (M i)):=funext fun _=>if_pos i.property
      simp_rw [hx]; exact (chiefPay u j hj L M h e).reindex _
    let W:={i:ι // ¬ l i=0}
    have hx : ∀ (i:W), X i=fun p=> ray u j (L i) (M i) p (l i):=fun i=>funext fun _=>if_neg i.property
    simp_rw [hx]; apply rosePay u j hj (L:=fun i:W=>L i) (M:=fun i:W=> M i) (fun i=>h _) (fun i=>e _) (fun i:W=>l i) (fun i:W=>i.property)
  have he := Moderate.bounded_const (w:=fun i=> (Real.sqrt (L i).val)⁻¹) (fun i=>(((Real.sqrt (L i).val)⁻¹:ℝ):ℂ)) 1 one_pos (fun i=> by rw [one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]; positivity)
  convert (hh.scale (muff_pay j L h l)).scale he using 2
  next i=> have hL:=side_pos (L i); set k:= Real.sqrt (L i).val; have hp:0<k:=Real.sqrt_pos.mpr hL; have hx:k^2=((L i).val:ℝ):=Real.sq_sqrt hL.le; field_simp; linear_combination decay j (l i)*hx
  rfl
end YM.CF.Fir
