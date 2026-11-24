import GaugeFieldConstruction.Rowick
import GaugeFieldConstruction.Olla
set_option autoImplicit false
noncomputable section
namespace YM.CF.Roots
open GJ Function Set Metric Mew MeasureTheory Filter Finset NormedSpace
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F X N M : Type}[Fintype I][LinearOrder I][NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable [NormedCommRing M][NormedAlgebra ℂ M][CompleteSpace M]
variable (J:Type)[DecidableEq J](σ:I→J)
variable (f g:Key I→ N)(p:River f)(t:River g)
variable [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F][NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
variable (B:E →L[ℂ] F →L[ℂ] X)
-- powerset product tip.E X.Asset.
lemma distrD {f:Key I→E}{g:Key I→F}(p:River f)(t:River g)(L:List I)(q:L.Nodup): tipI (pulseV B f g) L=∑ j∈L.toFinset.powerset, B (tipI f (wingX L j)) (tipI g (wingR L j)):=by
 induction L generalizing f g with
 | nil=> simp only [List.toFinset_nil, Finset.powerset_empty,sum_singleton]; rfl
 | cons i L ih=>
    have hx:= List.nodup_cons.mp q; have hv:i∉L.toFinset:=by simpa using hx.1
    rw [prodTip B p t,ih (p.flow i) (t.stay i) hx.2, ih (p.stay i) (t.flow i) hx.2,List.toFinset_cons,Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
    · rw [add_comm]; apply congrArg₂ (· + ·) ?_ ?_
      · apply sum_congr rfl; intro j g; have he:i∉j:=fun p=>hv (mem_powerset.mp g p); rw [tip_V i (wingX L j) (fun p=>hx.1 ((wing_sub _ _).subset p)),show wingX (i::L) j=wingX L j from (by simp [wingX,he]),show wingR (i::L) j=i::wingR L j from (by simp [wingR,wingX,he])]; rfl
      apply sum_congr rfl; intro j g; rw [tip_V i (wingR L j) (fun p=>hx.1 ((wing_sub _ _).subset p)),show wingX (i::L) (insert i j)=i::wingX L j from (show wingX (i::L) _=_ from (by
            rw [show wingX (i::L) (insert i j)=i::wingX L (insert i j) from (by simp [wingX]),wingπ _ _ _ hx.1])),show wingR (i::L) (insert i j)=wingR L j from ?_]; rfl
      rw [show wingR _ _=wingR L (insert i j) from (by simp [wingX,wingR]),wingRπ _ _ _ hx.1]
    · intro a₁ h₁ b₁ h₂ w; have ha:i∉ a₁:=fun v=> hv (mem_powerset.mp h₁ v); have hb:i∉ b₁:= fun v=>hv (mem_powerset.mp h₂ v); simpa [ha,hb] using congrArg (fun s:Finset I=>s.erase i) w
    apply Finset.disjoint_left.mpr; intro j v w; obtain ⟨k,t,rfl⟩:=mem_image.mp w; exact hv (mem_powerset.mp v (mem_insert_self ..))
-- linear exponent
abbrev rideN(w:I→ℂ)(i:Key I):ℂ:=∑ j:I, i j*w j
variable (w:I→ℂ)
lemma rideFlow : River (rideN w):=(tip_bank _ (fun j z=>z j*w j) (fun j _=>by
   have h :River fun z:Key I=> z j:=by refine ⟨(continuous_apply j).continuousOn,?_⟩; intro i v x u g; by_cases p:j=x <;> simp [p]; -- tune
   exact h.mul_T (zeroR (w j)))).1
lemma rideCut (x:I): Set.EqOn (cutI (rideN w) x) (fun _=> w x) (hill I):=by
 intro i u; have h:= (mitt (rideFlow w) u x).deriv.symm
 -- mitt.comp updates
 refine h.trans ?_; -- goal
 let s:=univ.erase x; let A:=∑ j∈s,i j*w j
 have ht : (fun p:ℂ=> rideN w (update i x p))=fun p=> p*w x + A:=by
    funext p; unfold rideN; rw[← Finset.add_sum_erase _ (fun j=>(update i x p) j*w j) (mem_univ x), Function.update_self]; exact congrArg (p*w x+ ·) (sum_congr rfl (fun j g=>congrArg (·* w j) (Function.update_of_ne (ne_of_mem_erase g) _ _))) -- ne_?
 rw [ht, deriv_add_const]; simp -- tune
lemma tipFire (L:List I)(p:L.Nodup): tipI (Complex.exp ∘ (rideN w)) L=(L.map w).prod:=by
 let f:=rideN w
 have h:=rideFlow w
 rw [Complex.exp_eq_exp_ℂ]
 induction L with
 | nil=>change exp _=1; rw [show rideN w 0=0 from (by unfold rideN; simp),exp_zero]
 | cons i s ih=>
   have hp : ψS id (i::s):=by simp only [ψS,List.map_id_fun]; exact p
   rw [ζexp _ h i hp,List.map_cons,List.prod_cons,←ih (List.nodup_cons.mp p).2]
   have he:Set.EqOn (cutI f i * (exp∘ f)) (fun z=> w i • (exp ∘ f) z) (hill I):= fun z p=> congrArg (·*(exp∘f) z) (rideCut w i p)
   exact (lace_C s he roots).trans (tip_C h.exp_V _ _)
#print axioms distrD
#print axioms tipFire
#check mitt
end YM.CF.Roots
end
