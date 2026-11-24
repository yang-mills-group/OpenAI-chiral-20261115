import ZecaTrout
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

variable {h q T E e R α D:ℝ}{t k:ℕ}

lemma marlinCost (hp:0<h)(eq:0<e) (a:0<T) (qa:0<q)
 (t:ℕ)(tp:T*t < R) (k:ℕ)
 (z:(Real.exp (-E*t)*(h*q)^k*e)^2 ≤ (2*k).factorial*D/R^(2*k)*h^(2*k)):
  (q*T*(t:ℝ))^(2*k)/(Nat.factorial (2*k))≤ D/e^2 * Real.exp (2*E*t):=by
 have u:0<R:= (mul_nonneg a.le t.cast_nonneg).trans_lt tp
 calc
  _ ≤ (q*R)^(2*k)/(Nat.factorial (2*k)):=by
    rw [mul_assoc q]
    gcongr
  _ ≤ _:=by

    have y:Real.exp (-E*t)^2=(Real.exp (2*E*t))⁻¹:=by
      rw [sq,← Real.exp_add,← Real.exp_neg];ring_nf
    rw [mul_pow,mul_pow,y,←pow_mul,Nat.mul_comm k,mul_pow] at z
    have s: (Real.exp (2*E*t))⁻¹*q^(2*k)*e^2 ≤
          (2*k).factorial*D/R^(2*k):=
         le_of_mul_le_mul_right (by
           calc
            _ = (Real.exp (2*E*t))⁻¹*(h^(2*k)*q^(2*k))*e^2:=by ring
            _ ≤ _ := z) (pow_pos hp (2*k))
    have p:0<((Nat.factorial (2*k)):ℝ):=by exact_mod_cast Nat.factorial_pos _
    rw [mul_pow]
    field_simp at s ⊢
    linarith only [s]

variable {H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H]
/-- t runs ℕ including zero, frequency pressure. -/
def fishing (x:ℕ→ℕ→ℤ→H) (h:ℝ):Prop:=
  0<h ∧ ∀T:ℝ,0<T → T<2 → ∃ D:ℝ, ∀ t:ℕ, ∃R:ℝ,_root_.LT.lt (T*(t:ℝ)) R ∧
    ∃f:ℂ→ℂ, fishNet f R D ∧ knocks (fun n=>x n t) h (fun y=>f y)
theorem marlin (a:0≤E)(w:E<q)(eq:0<e)
 {x:ℕ→ℕ→ℤ→H} (u:fishing x h) :
   ∃ t k:ℕ, ∀ᶠ n in atTop, ‖splashing (x n t) k 0‖
       < Real.exp (-E*t)*(h*q)^k*e:=by
 have qa:=a.trans_lt w
 obtain ⟨b,v,j⟩:=exists_between (show 2*E<2*q from by linarith)
 have bp:0<b:=by linarith
 obtain ⟨D,y⟩:=u.2 (b/q) (by positivity) ((div_lt_iff₀ qa).2 j)
 by_contra m
 apply lamprey (q*(b/q)) (2*E) (by positivity)
    (by rw [show q*(b/q)=b from by field_simp] <;>linarith) (D/e^2)
 intro t k
 obtain ⟨R,l,f,B,N⟩:=y t
 apply marlinCost u.1 eq (by positivity) qa t l k
 apply le_trans _ (finray h u.1.le f R D B (2*k) (-(k:ℝ)*h))
 by_contra! err
 have n:= (troutSq _ _ _ N k).eventually (gt_mem_nhds err)
 refine m ⟨t,k,?_⟩
 have hp:=u.1
 filter_upwards [n] with i hi
 by_contra! g
 exact hi.not_ge (pow_le_pow_left₀ (by positivity) g 2)
#print axioms marlin
