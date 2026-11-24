import YM.SU5.FiniteGaugeData.Signal.Platinum
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 14000
noncomputable section
namespace YM.CF.Signal.Sparkle
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b u v:ℝ}{i j d k:ℕ}
namespace OrbitPort
local notation "A"=> Axis→Fin d -- k=offset, d width

def breadth (N:Side)(k d:ℕ): (Axis→Fin d)→Site N:= fun x i=> ((k+(x i).val:ℕ):ZMod N.val)
variable (p:k+d≤ N.val)
include p
lemma register (x:Axis→Fin d)(i:Axis): ZMod.val (breadth N k d x i)=k+(x i).val:= (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt (by have ht:=(x i).isLt; omega))
def grid : (Axis→ Fin d) ↪ Site N:= ⟨breadth N k d,fun x y h=> funext fun i=> Fin.ext (Nat.add_left_cancel (by rw [←register p,←register p,h]))⟩ -- include p? statement
lemma house : Fintype.card (Axis→ Fin d)=d^4:=by simp [Axis]
omit p
lemma high(k:Per N)(h:2*k.val+1 ≤ N.val):principal k=(2*k.val+1)/N.val*Real.pi:=by
 unfold Lat.principal; rw [if_pos]; swap; unfold Lat.winding; nth_rw 2 [←one_mul Real.pi]; have h2:2*(k.val:ℝ)+1≤N.val:= (by exact_mod_cast h); exact mul_le_mul_of_nonneg_right ((div_le_one (nPos N)).2 (h2)) Real.pi_pos.le
 rfl

lemma frame_low (h:4*d ≤ N.val)(x:Axis→Fin d): ‖pm (breadth N 0 d x)‖ ≤ (2*d)/ N.val *Real.pi:=by
 refine (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ)≤_)).2 (fun i=>?_); let y:= breadth N 0 d x; change ‖principal (y i)‖ ≤ _; have h₁: ZMod.val (y i)=(x i).val:=by simpa [y] using register (show 0+d ≤N.val by omega) x i
 have hx:=(x i).isLt
 rw [high (y i) (by omega),Real.norm_of_nonneg (by positivity : (0:ℝ)≤_)]; have he:(2*((y i).val:ℝ)+1)≤(2:ℝ)*d:=(by exact_mod_cast (show 2*((y i).val)+1≤2*d by omega)); gcongr
lemma frame_high (h:8*d ≤ N.val) (hp:16≤ N.val)(x:Axis→ Fin d): Real.pi/4 ≤ ‖pm (breadth N (N.val/4) d x)‖ := by
 let l:=N.val/4; let y:= breadth N l d x; let z:= y (0:Axis); let v:= x (0:Axis); have ht: z.val=l+v.val:=register (show l+d≤ N.val by unfold l; omega) x 0
 have hz:=(norm_le_pi_norm (pm y) 0); change _ ≤ ‖pm y‖; apply hz.trans'; change _≤ ‖principal z‖; rw [high z (by unfold l at ht; omega),Real.norm_of_nonneg (by positivity : (0:ℝ) ≤_)]; have hv:1/4 ≤ (2*(z.val:ℝ)+1)/N.val:=by apply (le_div_iff₀ (nPos N)).2; have hx : (N.val:ℝ) ≤4*(2*z.val+1):=(by exact_mod_cast (show N.val ≤4*(2*z.val+1) from (by unfold l at ht; omega))); linarith
 linarith only [mul_le_mul_of_nonneg_right hv Real.pi_pos.le]

lemma funded (e:ℝ)(p:0<e):∃ C:ℝ,0<C∧ ∀ᶠ n:Side in atTop, ∃ d:ℕ, 8*d≤ n.val∧ ((2*(d:ℝ))/n.val)*Real.pi≤ e ∧ (n.val:ℝ) ≤ C*d:=by -- lexical→ whitespace
 obtain ⟨k,hk⟩:= exists_nat_gt (2*Real.pi/e); let a:=8+k; let u:ℝ:=2*a; have hu:0≤(k:ℝ):=(by positivity); have ha:0<a:=(by omega); refine ⟨u,by unfold u; positivity,?_⟩
 filter_upwards [eventually_ge_atTop (⟨a,ha⟩:Side)] with n h; change a≤ n.val at h; let d:= n.val/a; have hd:1≤d:= (Nat.one_le_div_iff (by omega : 0 < a)).2 h; have ht:= Nat.div_mul_le_self n.val a; change d * a≤ n.val at ht; have he: n.val < (d+1)*a:=by rw [mul_comm]; exact Nat.lt_mul_div_succ _ ha -- tune order
 refine ⟨d, le_trans (Nat.mul_le_mul_right d (show 8≤a by omega)) (mul_comm d a ▸ ht), ?_,?_⟩
 · have he: 2*Real.pi ≤ a*e:= ((div_lt_iff₀ p).1 hk).le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show k≤a by omega)) p.le); calc
      _ = (2*d*Real.pi:ℝ)/n.val:=by ring
      _ ≤ _:=by apply (div_le_iff₀ (nPos n)).2; have hv:d*a≤ n.val:=ht; have hy:(d:ℝ)*a≤ n.val:=(by exact_mod_cast ht); linarith only [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg d), mul_le_mul_of_nonneg_left hy p.le] -- binder
 unfold u; have hp:n.val≤(2*d)*a:=he.le.trans (Nat.mul_le_mul_right a (by omega)); exact_mod_cast le_trans hp (le_of_eq (by ring : 2*d*a=2*a*d))
end OrbitPort
end YM.CF.Signal.Sparkle
