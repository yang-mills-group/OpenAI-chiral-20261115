import YM.CF.Fir.Side
import YM.CF.Lattice.Anti
import YM.Next.STATIONARY.OneLoop.MomentumIntegral
/- Four-torus with even sampling side. Budget below tracks a shared massless sector at the least external periodic height. Fermion loop modes half shifted. Constants uniform in volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Lat Lattice Metric MeasureTheory Finset Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal
variable {N : Side}
def pinch (N: Side) : ℝ:=Real.pi/N.val
lemma pinch_pos (N): 0<pinch N:=div_pos Real.pi_pos (nPos N)
lemma payH: Real.pi=N.val*pinch N:=by unfold pinch; field_simp
lemma tone (k:Per N): winding k=(2*k.val+1)*pinch N:=by unfold Lat.winding pinch; ring
def chert (k:Per N):ℤ:=if winding k≤Real.pi then k.val else (k.val:ℤ)-N.val
lemma ch_price (k:Per N): principal k=(2*chert k+1)*pinch N:=by
 unfold Lat.principal chert; split_ifs; · push_cast; rw [tone]
 push_cast; rw [tone,payH (N:=N)]; ring
lemma shelf (k: Per N)(h:Even N.val): -Real.pi≤principal k-pinch N ∧ principal k+pinch N ≤ Real.pi:=by
 have hx:= inZone k; rw [ch_price,payH (N:=N),← neg_mul] at hx
 rw [ch_price,payH (N:=N),← neg_mul]
 obtain ⟨a,e⟩:=h; have H:=pinch_pos N; have hp:=lt_of_mul_lt_mul_right hx.1 H.le; have he:=le_of_mul_le_mul_right hx.2 H
 push_cast [e] at hp he ⊢; -- replaces N.val?
 have ha : -((a:ℤ)+a)<2*chert k+1:=by exact_mod_cast hp
 have hb : 2*chert k+1≤(a:ℤ)+a:=by exact_mod_cast he
 have hr : -((a:ℤ)+a) ≤2*chert k:=by omega
 have hz : 2*chert k+2≤(a:ℤ)+a:=by omega
 have hr' : -((a:ℝ)+a) ≤2*chert k:=by exact_mod_cast hr
 have hz' : 2*(chert k:ℝ)+2 ≤ (a:ℝ)+a:=by exact_mod_cast hz
 constructor <;> nlinarith [mul_le_mul_of_nonneg_right hr' H.le,mul_le_mul_of_nonneg_right hz' H.le]
lemma cohere (k:Per N): pinch N≤|principal k|:=by
 rw [ch_price,abs_mul,abs_of_pos (pinch_pos _)]; have h : (1:ℝ) ≤|2*(chert k:ℝ)+1|:=by
   have hx: (1:ℤ) ≤ |2*chert k+1|:=by
     by_cases h : 0≤ chert k; · rw [abs_of_nonneg] <;> omega
     rw [abs_of_neg] <;> omega
   exact_mod_cast hx
 exact le_mul_of_one_le_left (pinch_pos _).le h
def bark (k:Site N):Gaia:= exileE.symm (pm k)
lemma branch (k:Site N)(i:Axis): bark k i=principal (k i):=rfl
lemma torch (k:Site N):pinch N≤‖bark k‖:=by
 have hx:=orbit_at (exileE (bark k)); refine (cohere (k 0)).trans (le_trans ?_ hx)
 simpa only [Real.norm_eq_abs,bark,MeasurableEquiv.apply_symm_apply,pm,Function.comp_apply] using norm_le_pi_norm (exileE (bark k)) 0

def hue (k:Per N) := Set.Ioc (principal k-pinch N) (principal k+pinch N)
def fir (k:Site N) : Set Track:= {x|∀ i,x i∈ hue (k i)}
def cellH (k:Site N) := exileE ⁻¹' fir k
lemma fir_meas (k:Site N) : MeasurableSet (fir k):=MeasurableSet.univ_pi' fun i=> measurableSet_Ioc
lemma cell_meas (k:Site N) : MeasurableSet (cellH k) := (fir_meas k).preimage exileE.measurable
lemma forest (k:Site N)(h:Even N.val): cellH k⊆boundsEarth:=fun p hp i=>
 ⟨lt_of_le_of_lt (shelf _ h).1 (hp i).1, (hp i).2.trans (shelf _ h).2⟩
lemma proximity (k:Site N) {p:Gaia}(hp:p∈cellH k) : ‖bark k-p‖ ≤2*pinch N:=by
 have hx:(‖bark k-p‖)^2≤∑ _:Axis,pinch N^2:=by
    rw [← geode_sum]; refine sum_le_sum ?_; intro a _; obtain ⟨u,v⟩:= hp a
    change (_-_ < p a) at u; change p a≤ _+ _ at v; change ((bark k a)-p a)^2≤_
    rw [branch]; nlinarith
 simp at hx
 have ht:=pinch_pos N; nlinarith
lemma overlaps {a b:Per N}{x:ℝ}(h:x∈ hue a)(e:x∈hue b):a=b:=by
 obtain ⟨l,r⟩:=h; obtain ⟨i,j⟩:=e; rw [ch_price] at l r i j
 have H:=pinch_pos N
 have ht:2*(chert a:ℝ)*pinch N < (2*(chert b:ℝ)+2)*pinch N := by linarith
 have hr:2*(chert b:ℝ)*pinch N < (2*(chert a:ℝ)+2)*pinch N := by linarith
 have h1:=lt_of_mul_lt_mul_right ht H.le; have h2:=lt_of_mul_lt_mul_right hr H.le
 have h3:2*chert a<2*chert b+2:=by exact_mod_cast h1
 have h4:2*chert b<2*chert a+2:=by exact_mod_cast h2
 apply prin_inj; rw [ch_price,ch_price,show chert a=chert b by omega]
lemma clears : Pairwise (Function.onFun Disjoint (cellH (N:=N))) :=by
 intro k l h; exact Set.disjoint_left.mpr fun x hk hl=> h (funext (fun i=> overlaps (hk i) (hl i)))
end YM.CF.Ember
