import Taffeta.Levy
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Drift Function Set MeasureTheory Finset
open scoped Classical
variable {I:Type}[Fintype I][LinearOrder I]
attribute [-instance] instDecidableEqLex
local notation "P"=>PairKey I
-- Fission into scalar.Browse.sert.
lemma divide_null (c:I→ℂ)(l:List I)(k:List I→ℂ)(e:∀l,k l=0):divide c l k=0:=by
 induction l generalizing k with
 | nil=> exact e _
 | cons i l h=> unfold divide; rw [h k e,h _ (fun _=>e _),smul_zero,zero_add]
lemma burn_all (c:I→ℂ)(l:List I)(ρ:ℂ)(p:l.Nodup): tipI (fun z:Key I=> abrupt c z * ρ) l= (l.map c).prod * ρ:=by
 have he:= tip_abrupt c (fun _=>ρ) (zeroR _) l p
 suffices τ:divide c l (tipI fun _=>ρ)= (l.map c).prod*ρ from he.trans τ
 induction l
 case nil=>simp [tipI,lance,divide]
 case cons i l h=>
    specialize h (List.nodup_cons.mp p).2 (tip_abrupt c (fun _=>ρ) (zeroR _) l (List.nodup_cons.mp p).2) -- h uses he? tactic inspect
    unfold divide; rw [divide_null c _ _ (fun _=>Roots.proper ..),h,add_zero,List.map_cons,List.prod_cons,smul_eq_mul,mul_assoc]
lemma levy_map (α β:P→ℂ)(s:List I→List I→ℂ)(L:List P)(d:ℂ): levy α β s L /d= levy α β (fun a b=>s a b/d) L:=by
 simp_rw [div_eq_inv_mul]; exact (levy_smul α β s L (d:ℂ)⁻¹).symm
variable {W:Type*}[MeasurableSpace W]{μ:Measure W}
lemma levy_integral (α β:P→ℂ)(s:List I→List I→W→ℂ)(L:List P)(h:∀a b,Integrable (s a b) μ): Integrable (fun v:W=>levy α β (fun a b=>s a b v) L) μ∧(∫ v,levy α β (fun a b=>s a b v) L∂μ)=levy α β (fun a b=> ∫ v,s a b v∂μ) L:=by
 induction L generalizing s with
 | nil=> exact ⟨h _ _,rfl⟩
 | cons i l ih=>
   let A(a b):=s (i.1::a) b; let B(a b):=s a (i.1::b)
   obtain ⟨e1,h1⟩:= ih A fun _ _=>h ..; obtain ⟨e2,h2⟩:= ih B fun _ _=>h ..
   simp only [levy]; refine ⟨(e1.smul (α i)).add (e2.smul (β i)),?_⟩
   refine Eq.trans (integral_add (e1.smul (α i)) (e2.smul (β i))) ?_; simp only [Pi.smul_apply,integral_smul]; exact congrArg₂ (·+·) (congrArg (α i • ·) h1) (congrArg (β i • ·) h2)
lemma levy_split (L:List P)(β:P→ℂ)(b:I→ℂ)(s:List I→ℂ): levy 1 (fun i=>b i.1*β i) (fun t _=>s t) L= levy 1 β (fun a t=> (t.map b).prod*s a) L:=by rw [levyMulR]; rfl
lemma berry (L:List I)(a:ℂ):(L.map (fun _=>a)).prod = a^L.length:=by induction L with|nil=>simp|cons i l ih=>rw [List.map_cons,List.prod_cons,List.length_cons, pow_succ', ih]
#print axioms levy_integral
#print axioms burn_all
end YM.CF.Mew
end
