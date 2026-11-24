import YM.SU5.Relativistic.Nashi
/-! # static cell thermodynamics on reconstructed lattice. parity orientation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Stationary (Gaia cartWeight boundsEarth exileE)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
local notation "Ω"=> angle true
local notation "Q" => Op SpinIdx
variable {N:Side}{M:Tulip.Male}(x y:Cover)(i j:SpinIdx)(a b:Slot)
lemma price_C(s:Staff) : s.stem (tickA N) (spar 4 M (1:Pane N))=lens (fun p=>s.stem Ω (bent true 4 M.val p)) N:=by
 induction s with
 | one=> exact l_one.symm
 | gauge=> exact (t_comp N).symm.trans (t_lamp N true)
 | pay=> exact nativeP N true 4 M (by decide)
 | neg s h=> unfold Staff.stem; rw [h,←neg_one_smul ℝ,l_scale]; simp
 | add s t h k=> unfold Staff.stem; rw [h,k,l_plus]
 | mul s t h k=> unfold Staff.stem; rw [h,k,l_mul]
lemma stamper (K:Momentum→ Op SpinIdx) : inner ℂ (Lifted.basisC N x i a) (acts (lens K N) (Lifted.basisC N y j b)) = if a=b then ((N.val:ℂ)^4)⁻¹ *∑ z: Site N, star (mode (mel z) (-x))*mode (mel z) (-y)*K (mel z) i j else 0:=by
 unfold Lifted.basisC; rw [map_smul,inner_smul_right,inner_smul_left,basis_inner,basis_act]; unfold BPress.Spin.Blank.lens scalarP Lifted.index; simp only [Matrix.kronecker_apply]
 by_cases h:a=b; swap; · simp [h]
 rw [h]; simp only [Matrix.one_apply_eq,mul_one,if_true]; rw [Rush.price]; simp only [mul_sum]; apply sum_congr rfl; intro z _; rw [←windWave,←windWave]
 unfold Lat.Fourier normF; simp only [Matrix.of_apply, star_div₀,star_pow,star_natCast, star_mul,star_star]; change Lifted.winding _ _*(star (Lifted.winding _ _)*_)=_; ring -- tune normH
-- uniform norm across staff on wings
lemma shapeQ(s:Staff): ∃ C:ℝ,0<C ∧ ∀ (X:Op SpinIdx),IsStarProjection X → ‖s.stem Ω X‖ ≤ C:=by
 induction s with
 | one=> exact ⟨1,zero_lt_one,fun _ _=> norm_one.le⟩
 | gauge=>exact ⟨1,zero_lt_one,fun P _=> strip_ge.norm_le _⟩
 | pay=> exact ⟨1,zero_lt_one,fun _ h=> h.norm_le _⟩
 | add a b ih ih'=> obtain ⟨P,p,h⟩:=ih; obtain ⟨Q0,q,h'⟩:=ih'; exact ⟨P+Q0,add_pos p q,fun X t=>(norm_add_le ..).trans (add_le_add (h X t) (h' X t))⟩
 | neg a ih=> obtain ⟨P,p,h⟩:=ih; exact ⟨P,p,fun X t=> (norm_neg _).trans_le (h X t)⟩
 | mul a b ih ih'=> obtain ⟨P,p,h⟩:=ih; obtain ⟨Q0,q,h'⟩:=ih'; exact ⟨P*Q0,mul_pos p q,fun X t=>(norm_mul_le ..).trans (mul_le_mul (h X t) (h' X t) (norm_nonneg _) p.le)⟩
lemma sox(s:Staff) : Continuous (fun X:Op SpinIdx=> s.stem Ω X):=by induction s <;> unfold Staff.stem <;> fun_prop
def zCost(s:Staff) :ℂ:= if a=b then (cartWeight:ℂ)*∫ g in boundsEarth, star (mode (cn g) (-x))*mode (cn g) (-y)*(s.stem Ω (noon g)) i j else 0
variable {N':ℕ→Side}{W:ℕ→Tulip.Male}(h:Tendsto (fun i=>(N' i).val) atTop atTop)(v:Tendsto (fun i=>(W i).val.val) atTop atTop)(e:∀ i, Even (N' i).val)
include h
lemma feasts (k:∀ i,Site (N' i))(x: Gaia)(p:∀ i,x∈ cellH (k i)): Tendsto (fun i=>bark (k i)) atTop (𝓝 x):=by
 rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero (fun i=>norm_nonneg _) (fun i=>proximity _ (p i))
 have hg:Tendsto (fun i:ℕ=> (((N' i).val:ℝ))⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h)
 simpa only [pinch,Function.comp_def,div_eq_mul_inv,mul_zero] using ((hg.const_mul Real.pi).const_mul 2)
omit h in
lemma lafetite {s:ℕ→Side} (h:Tendsto (fun i=>(s i).val) atTop atTop): Tendsto s atTop atTop:=tendsto_atTop.mpr fun n=> h.eventually_ge_atTop n.val
include v e
lemma supplier (s:Staff)(p:∀ i,IsStarProjection (spar 4 (W i) (1:Pane (N' i)))): Tendsto (fun k=> inner ℂ (Lifted.basisC (N' k) x i a) (acts (s.stem (tickA _) (spar 4 (W k) (1:Pane (N' k)))) (Lifted.basisC (N' k) y j b))) atTop (𝓝 (zCost x y i j a b s)):=by
 unfold zCost; simp_rw [price_C,stamper]; by_cases t:a=b; swap; · simp only [t, ↓reduceIte]; exact tendsto_const_nhds
 simp only [t,↓reduceIte]; obtain ⟨C,D,P⟩:= shapeQ s; have he':Tendsto N' atTop atTop:=lafetite h -- tune
 apply registry he' e _ _ C _
 · intro g gs ha y w; have hx:=feasts h y g w; have ht:= mill y hx; have hy:= (Continuous.tendsto (f:=fun X:Op SpinIdx=> X i j) (by fun_prop) _).comp ((sox s).continuousAt.tendsto.comp (chute (lafetite v) y gs ha hx))
   exact Tendsto.mul (Tendsto.mul (Tendsto.star ((Continuous.tendsto (f:=fun p:Momentum=>mode p (-x)) (by unfold mode; fun_prop) _).comp ht)) ((Continuous.tendsto (f:=fun p:Momentum=>mode p _) (by unfold mode; fun_prop) _).comp ht)) hy
 intro k n; rw [norm_mul,norm_mul,norm_star,mode_real _ _ (mel_h _).1,mode_real _ _ (mel_h _).1,mul_one,one_mul]; exact le_trans (norm_entry ..) (P _ (f_native (by decide :1 ≤ 4) (p k) n))
end YM.CF.Papyrus.Franc.Loaves
#print axioms YM.CF.Papyrus.Franc.Loaves.supplier
