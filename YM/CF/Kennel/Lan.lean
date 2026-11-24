import YM.CF.Kennel.Torus
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Hull
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side}{k:ℕ}{m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e}
-- first and second derivatives contract; independent clock
lemma natal (h:1≤k)(w:k≤2)(p:Even j)(z':2≤j)(s r:ℝ)(hs:0<s)(hr:0<r):∃ α C:ℝ,0<α ∧ 0<C∧ ∀ (L:Side),4≤L.val→ ∀ u τ:ℝ,0<u→u≤α→0≤τ→ ∃ W:ℕ,∀ {m A B:Side}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}{V:Grasp Y B e} {a b d:ℝ}{n:ℕ}, Hull j L ho a b d e n m A B G T F z Y V→ Gazes T F z s τ r→ W≤ (More (CSide m B)).val→ ∀ M:Male,∀ K:ℝ, 0≤K→∀ J:Toy k (CSide A B),Prints J→handy J→ (∀ i,balance u J i ≤K)→∀ U:Dress (CSide A B), relic U→ ∃ Q:Toy k (CSide m B),Prints Q ∧ handy Q ∧ Nacre.crystal k (emergence L j ho G F z M (U+ sumU (cavil J))-emergence L j ho G F z M U) (spurTx Q) ∧ ∀ i,balance u Q i ≤ K*C/(L.val:ℝ):=by
 obtain ⟨v,A,hv,hA,H⟩:=bluff j p z' true; obtain ⟨a,B,ha,hB,D⟩:=bluff j p z' false
 let x:=min s (min v (a/((k:ℝ)+1))); have hx:0<x:=lt_min hs (lt_min hv (by positivity))
 let F:= cashH x k; have hF:0<F:=mul_pos (nick_pos _ (by positivity)) (Iteration.momentPrice_pos _ (half_pos hx)); have hg:0<sugarK:=by unfold sugarK; positivity
 refine ⟨x/2,B*A*F*r^k*sugarK,half_pos hx,by positivity,fun L g u τ hu he hy =>?_⟩
 obtain ⟨W,U⟩:=rubrics r x τ hx hr hy k w L g u hu he
 refine ⟨W,?_⟩; intro m A' B' G T H' z ho Y e V a0 b d n t q f M K hk J hc hp hJ y hY
 obtain ⟨Λ,P,Hq⟩:=q.was
 choose Z hZ Hz using (fun (x:Single (CSide A' B')) (y:Single (CSide m B'))=> Hq (place_x x) (place_x y)); let O:= pine j L ho (Thread j) false M G 1; let L' := pine j L ho (Thread j) true M G 1; let U':= arch G O; let F':= arch G L'; let N:=tapH U' F' Z J; let T':= fderiv ℝ (Iteration.chartOf H' z) 0
 have heX(i: Vox m B'):pyre N i=gallery L j ho G M (pyre J (T' i)):= by unfold gallery; rw [vested]; exact tap_paid group _ _ _ (fun x y w=>Hz x y _ w) U' F' J -- tune
 have hz:= U G t.fromL f
 have h' : ((k:ℝ)+1)*x ≤ a:=by
    rw [mul_comm]; exact (le_div_iff₀ (show (0:ℝ)<k+1 by positivity)).mp ((min_le_right ..).trans (min_le_right ..): x ≤ _)
 have hd1 : BudH G U' _ B:=bud_inc (show BudH G U' a B from (by
    unfold U' O; have hg:=t.fromL; subst L; exact D G ho _ (canUse _ _ ho) M)) h'
 have hd2 : BudH G F' x A:=bud_inc (show BudH G F' v A from (by
    unfold F' L'; have hg:=t.fromL; subst L; exact H G ho _ (canUse _ _ ho) M)) ((min_le_right ..).trans (min_le_left ..))
 have ht0:=Rails_inc P (min_le_left s (min v (a/((k:ℝ)+1))))
 rw [t.alignT] at ht0
 have ht1:= tap_cost G (b:=u) hd1 hd2 hx hr (fun r t i j p=> hz Λ (Z r i) ht0 (hZ r i) r t i j p) J hB hA hk hJ
 obtain ⟨Q,G',v',q',hK⟩:= t.attica M y hY hp hc (by omega) heX ht1; refine ⟨Q,G',v',q',fun i=>?_⟩; apply (hK i).trans
 let l:ℝ:=L.val; have hl:0<l:=Nat.cast_pos.mpr L.property; have ht:spanV G = l:=congrArg (fun a:Side=>(a.val:ℝ)) t.fromL; have he:1≤l:=by unfold l; exact_mod_cast L.property
 have hp: l^2 ≤ (l^2)^k:= (by simpa only [pow_one] using (pow_le_pow_right₀ (one_le_pow₀ he:1≤l^2) h)); rw [spanV,t.fromL,div_pow]; change K* _* F *l*(r^k/(l^2)^k)* sugarK ≤ _* _/ l; calc
   _ ≤ K*(B*A)*F*l*(r^k/l^2)*sugarK:=by gcongr
   _ = _:=by field_simp -- tune
end YM.CF.Kennel
