import YM.CF.Gall.Limb
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gall
open YM.CF.Onyx YM.CF.Emu
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {j:ℕ}{r C:ℝ}
variable {N:Side}{d:Candle}
lemma rime (F:Stag N→Peb)(s:Slide N d)(a:Slot): (∑ i : Site N,‖F (i,a)‖^2)=∑ i:Site N,‖trackF s F a i‖^2:=by
 rw [←Equiv.sum_comp (Equiv.addRight (wrap N (s.z a))) (fun i=>‖trackF s F a i‖^2) ]; apply sum_congr rfl; intro i _; unfold trackF Emu.rake; simp
lemma wave (F:Stag N→Peb)(x: Single N) : ‖acts (Dofu N F) (basisKet x)‖^2 ≤ (∑ i:Site N,‖F (i,x.2)‖^2)/(N.val:ℝ)^4:=by
 let A:=Dofu N F; let u:=basisKet x; have hp := act_inner (star A) u (acts A u); rw [star_star,inner_self_eq_norm_sq_to_K, ←act_mul] at hp; unfold u A at hp; rw [basis_inner, basis_act, ←Dofu_s, ←map_mul,dent x x, if_pos rfl] at hp
 have ht(x y:Site N) : ‖Fourier N x y‖= 1/(N.val:ℝ)^2:=by
    have hv:= congrArg norm (frequency_unit y x); simp only [norm_mul,norm_star,norm_one] at hv; simp only [Fourier,Matrix.of_apply,norm_div,normF,norm_pow,Complex.norm_natCast]; rw [show ‖frequency y x‖=1 from ?_]; nlinarith only [hv,norm_nonneg (frequency y x)] -- tune
 change (↑‖acts (Dofu N F) (basisKet x)‖:ℂ)^2=_ at hp
 have hx:‖acts (Dofu N F) (basisKet x)‖=‖(↑‖acts A u‖:ℂ)‖:=by rw [Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
 unfold A u at hx; nth_rw 1 [hx]
 rw [← norm_pow,hp]; refine (norm_sum_le ..).trans ?_; rw [sum_div]; refine sum_le_sum fun i _=> ?_; let v:=F (i,x.2)
 rw [norm_mul,norm_mul,norm_star,ht]; change _*(‖(star v*v) _ _‖) *_ ≤ _; refine le_trans ?_ (le_of_eq (a:=(1/(N.val:ℝ)^2 * ‖v‖^2)*(1/(N.val:ℝ)^2)) ?_); gcongr; exact (norm_entry (star v*v) _ _).trans_eq (CStarRing.norm_star_mul_self.trans (sq _).symm); ring -- tune
lemma fame(H:1≤j)(p:0<r)(u:0<C):∃ V:ℝ,0<V ∧∀ {N:Side}{d:Candle}(A:Stag N→Peb){M:Jill.Male}(s:Slide N d),Even N.val→ (∀ x:Slot,FormU (s.u x) j M r C (trackF s A x))→∀ i:Single N, ‖acts (Dofu N A) (basisKet i)‖≤ V ∧ ‖acts (star (Dofu N A)) (basisKet i)‖≤ V:=by
 obtain ⟨c,g,P⟩:= Gall.tad H p u; refine ⟨Real.sqrt c,by positivity,fun {N} {d} A {M} s h v i=>?_⟩; have hz:= Real.sq_sqrt g.le; have ht:=nPos N
 have he:(∑ j:Site N,‖A (j,i.2)‖^2)/(N.val:ℝ)^4 ≤ c:=by rw [rime A s i.2,div_le_iff₀ (by positivity)]; exact P _ _ h (v i.2)
 constructor
 · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp; rw [hz]; exact (wave _ _).trans he
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp; rw [hz,←Dofu_s]; refine le_trans (wave _ _) ?_; simp_rw [Pi.star_apply,norm_star]; exact he
end YM.CF.Gall
