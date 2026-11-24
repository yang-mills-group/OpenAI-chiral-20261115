import YM.CF.BProof.Grid.Smooth
import YM.CF.BProof.HealthyMood

/-! Construction of the N-mark face frames (formula on local variables, with support price).
Arithmetic allowance for the additional mesh count R. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Face
open Function SU Lattice Filter MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group

structure Design where
 k₀ : ℕ
 size : ℕ
 toll : ℝ
 K : ℝ
 positive : 0<toll
 budget : 0<K
 frames {c s : Side}(g:Ratio c s)(k:ℕ) : Sheet s → Frame s
 meas {c s : Side}(g: Ratio c s)(k:ℕ) : Measurable (frames g k)
 fixed {c s : Side}(g: Ratio c s)(k:ℕ)(U:Sheet s)(x:Space c) : 4≤ c.val→ g.count.val=2^k→k₀≤k→ frames g k U (Grid.grow g x)=1
 costs {c s:Side}(g:Ratio c s)(k:ℕ)(U:Sheet s) : 4≤ c.val→ g.count.val=2^k→k₀≤ k→ (∀ p i,group.chord (read U p i)≤ toll/(g.count.val:ℝ)^2) → ∀ p i,
    group.chord (react (frames g k U) U (p,i)) ≤ K/g.count.val
 reaches {c s : Side}(g:Ratio c s)(k:ℕ)(S:Finset (Space s)): 4≤c.val→g.count.val=2^k→k₀≤k→ S.Nonempty → Grid.Conn S 1 → ∃ T : Finset (Space s), S⊆ T∧ Grid.Conn T 1∧ T⊆ Grid.collar S (size*g.count.val)∧ T.card≤ size*(g.count.val+(1+k)*S.card)∧
    ∀ U V : Sheet s, Grid.Wire.Agrees G (T:Set _) U V → Set.EqOn (frames g k U) (frames g k V) S

variable {c s:Side}
@[simp] lemma slide_t (x : Space s)(i : TAxis) : Grid.slide x i=x+tstep i := by ext j; by_cases h:j=i; subst i; simp; simp [Grid.slide,h]
lemma square_price (U : Sheet s) (p : Space s)(i : Fin 3) : group.chord (read U p i)=cd G (U (p,Mag.f₂ i)*U (Grid.slide p (Mag.f₂ i),Mag.f₁ i)) (U (p, Mag.f₁ i)*U (Grid.slide p (Mag.f₁ i),Mag.f₂ i)) := by
 let a:=U (p,Mag.f₁ i)*U (Grid.slide p (Mag.f₁ i),Mag.f₂ i); let b:= U (p,Mag.f₂ i)*U (Grid.slide p (Mag.f₂ i),Mag.f₁ i)
 rw [show read U p i=a*b⁻¹ from by simp [read,Mag.curl,a,b,mul_assoc],← cd_one]; change _=cd G b a; rw [← cd_mul_right G b 1,one_mul]; group -- tune
lemma flat {U:Sheet s}{m:ℝ}(h:∀ p i, group.chord (read U p i)≤m) (hm:0≤m) : Grid.Wire.Flat G U Set.univ m:=by
 intro p i j _ _ _ _
 have he(i : Fin 3) := h p i; simp_rw [square_price] at he;
 have ht(i:Fin 3):= (cd_symm ..).trans_le (he i) -- tune orientation
 fin_cases i <;> fin_cases j
 · exact (cd_self ..).trans_le hm
 · exact ht 0
 · exact ht 1
 · exact he 0
 · exact (cd_self ..).trans_le hm
 · exact ht 2
 · exact he 1
 · exact he 2
 · exact (cd_self ..).trans_le hm

lemma available : Nonempty Design := by
 classical
 obtain ⟨b,K,d,u,hp,ht,h⟩:= Grid.Blend.frames
 choose! F hF he hh using (fun c s : Side=> (show ∀ g : Ratio c s,_ from @h c s))
 let R (c s:Side)(g:Ratio c s)(k:ℕ) : Prop := 4 ≤ c.val ∧ g.count.val=2^k ∧ b≤k
 let t (c s:Side) (g:Ratio c s)(k:ℕ) : Sheet s → Frame s:=fun U=> if R c s g k then @F c s g k (U,fun _=>1) else 1
 refine ⟨b,K,d,u,hp,ht,fun {c s}=>t c s,?_,?_,?_,?_⟩
 · intro c s g k; unfold t; split_ifs with a; exact ((@hF c s g a.1 k a.2.1 a.2.2)).comp (f:=fun U:Sheet s=>(U,(1:Grid.Floor E 3 c))) (by fun_prop); exact measurable_const
 · intro c s g k U x v w y; change t c s g k U _ = _; unfold t; rw [if_pos (show R c s g k from ⟨v,w,y⟩)]; exact (@he c s g v k w y (U,fun _=>1)).1 x
 · intro c s g k U v w y Z p i; unfold t; rw [if_pos (show R c s g k from ⟨v,w,y⟩)]
   have ht':=(@he c s g v k w y (U,fun _=>1)).2 (flat Z (by positivity)) p i
   let q:= @F c s g k (U,fun _=>1)
   unfold react; change group.chord (q p*U _*(q (p+tstep i))⁻¹)≤_
   rw [←cd_one,←cd_mul_right G (q (p+tstep i)) 1,one_mul,inv_mul_cancel_right,cd_symm]; rw [slide_t] at ht'; exact ht'
 · intro c s g k S v w y hn he; obtain ⟨T,H',h,d,b',H⟩:= @hh c s g v k w y S hn he
   refine ⟨T,H',h,d,b',fun U V v'=>?_⟩; unfold t; rw [if_pos (show R c s g k from ⟨v,w,y⟩), if_pos (show R c s g k from ⟨v,w,y⟩)]; exact H (U,fun _=>1) (V,fun _=>1) v' (fun x h=>rfl)

variable (K:Chart G)
/-- r_base dyadic choice of B-gate. price use coin for R scale (∝t^(-1/2)). -/
abbrev rY (y:ℝ) := coin y (1/4) (-1/2) 0
lemma rY_eq (y : ℝ) : rY y = (thresh y)^((-1:ℝ)/2):=by rw [coin_rpow]; unfold rY; ring_nf
structure Sized (v:ℝ)(g:Ratio c s)(y:ℝ)(k:ℕ) : Prop where
 fine : 4 ≤ c.val
 power : g.count.val=2^k
 lower : v*rY y ≤ g.count.val
 upper : (g.count.val:ℝ) < (2*v)*rY y
end YM.CF.BProof.Face
