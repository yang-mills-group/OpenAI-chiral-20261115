import YM.SU5.Relativistic.PulseT
/-! # spatial splitting of observation probe. Exact Fourier winding. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "ω"=> 2 * Real.pi

abbrev RearA := Fin 3
abbrev Behind:= Fin 3 → ℝ
abbrev WalkA:= Fin 3 → ℤ
-- last-main coordinate
abbrev TA:Axis:= Fin.last 3
def tack {M:Type*}(k:Fin 3→M)(w:M): Fin 4→ M:= Fin.lastCases w k
lemma tack_equiv (M:Type*) : ∃ e: (Fin 3→ M) × M ≃ (Axis→M), ∀ i j,e (i,j)=tack i j:=by
 refine ⟨ {toFun:= fun u=> tack u.1 u.2
           invFun:= fun u=> (fun i=>u i.castSucc,u TA)
           left_inv:= fun ⟨i,j⟩=> ?_
           right_inv:=fun i=>?_ }, fun i j=> rfl⟩ -- tune lambda parsing & structure alignment
 · refine Prod.ext ?_ ?_
   · funext k; change tack i j k.castSucc=i k; rw [tack]; exact Fin.lastCases_castSucc ..
   change tack i j (Fin.last 3)=j; rw [tack]; exact Fin.lastCases_last ..
 funext j; cases j using Fin.lastCases <;> change tack (fun k=>i k.castSucc) (i (Fin.last 3)) _=_ <;> simp only [tack, Fin.lastCases_last,Fin.lastCases_castSucc]
@[simp] lemma tack_right {M:Type*}(k:Fin 3→M) (w:M) : tack k w TA=w:=by rw [tack,TA]; exact Fin.lastCases_last ..
@[simp] lemma tack_left {M:Type*}(k:Fin 3→M)(w:M)(a:Fin 3) : tack k w a.castSucc=k a:= by rw [tack]; exact Fin.lastCases_castSucc ..
lemma tack_c : Continuous (fun i:Behind × ℝ=> tack i.1 i.2):= by
 apply continuous_pi; intro j; induction j using Fin.lastCases <;> simp only [tack, Fin.lastCases_last,Fin.lastCases_castSucc] <;> fun_prop

-- limit graph tangential m-coordinate; use Ioc for fundamental slab.
def levelx (k:Behind)(j:WalkA): Behind:=fun i=> k i + ω * j i
@[fun_prop] lemma levelx_c (j:WalkA):Continuous (fun i=>levelx i j):= continuous_pi (fun i=> (continuous_apply _).add continuous_const)
def amp (k:Behind)(j:WalkA):ℝ:=Real.sqrt (∑ a:Fin 3,(levelx k j a)^2)
@[fun_prop] lemma amp_c (j:WalkA):Continuous (fun i=>amp i j):= by unfold amp; fun_prop
lemma amp_sq (k:Behind)(j:WalkA) : amp k j ^2= ∑ a:Fin 3,(levelx k j a)^2:=by unfold amp; rw [Real.sq_sqrt (by positivity)]
lemma amp_ge (k:Behind)(j:WalkA)(a:Fin 3): |levelx k j a|≤ amp k j:= by
 apply (sq_le_sq₀ (by positivity) ((show 0 ≤ amp k j from Real.sqrt_nonneg _))).mp; rw [amp_sq,sq_abs]; exact Finset.single_le_sum (f:=fun i:Fin 3=>_) (fun a _=> sq_nonneg (levelx k j a)) (mem_univ a)
-- use strictly positive K band
abbrev sunshine : Set Behind:=Set.pi Set.univ (fun _=>Set.Ioo 0 π)
lemma whirlV {k:Behind}(p:k∈sunshine)(j:WalkA)(a:Fin 3):levelx k j a≠0:=by
 have h:k a ∈ Ioo 0 π:=p a (Set.mem_univ _); by_cases t:0≤j a
 · exact (add_pos_of_pos_of_nonneg h.1 (mul_nonneg (by positivity) (by exact_mod_cast t))).ne'
 apply ne_of_lt; change k a+_ < _; have hv: (j a:ℝ) ≤ -1:= by exact_mod_cast (show j a ≤ -1 by omega)
 nlinarith only [hv,h.1,h.2, pi_pos, mul_le_mul_of_nonneg_left hv pi_pos.le]
lemma amp_pos {k:Behind}(p:k∈sunshine)(j:WalkA):0<amp k j:= (amp_ge k j 0).trans_lt' (abs_pos.mpr (whirlV p j 0))
lemma spectrum_b (k:Behind)(p:k∈ sunshine)(t:ℝ)(h:t∈ Icc (-π) π):Bound π (tack k t) := (pi_norm_le_iff_of_nonneg pi_pos.le).mpr (fun i=>by
 induction i using Fin.lastCases with
 | last => exact (tack_right k t).symm ▸ (show ‖t‖≤π from abs_le.mpr h) -- mismatch Fin
 | cast a => have hp:=p a (Set.mem_univ _); rw [tack_left,Real.norm_of_nonneg hp.1.le]; exact hp.2.le) -- case name
lemma tac_nz{t:ℝ}{k:Behind}(p:k∈sunshine): tack k t≠0:=by
 intro h; have he:=congrFun h ((0:Fin 3).castSucc); rw [tack_left] at he; exact (p 0 (Set.mem_univ _)).1.ne' he
def heatLine (k:Behind)(t:ℝ)(i:Axis):ℂ:= tough (tack k t) i

def bleat (k:Behind)(j:WalkA):ℂ:=2*(∏ a:Fin 3,skirt (levelx k j a))^8
def shortLap (k:Behind)(j:WalkA)(u:ℝ):= bleat k j * smoothZip (amp k j) 8 u
lemma short_exact(k:Behind)(t:ℝ)(j:WalkA)(q:ℤ)(i:Axis) :
  let u:=t+ω*q
  slat (tack k t) (tack j q) i= ↑(tack (levelx k j) u i)*shortLap k j u:=by
 intro u; have he:tack k t+ stem (tack j q)= tack (levelx k j) u:= by funext i; induction i using Fin.lastCases <;> simp only [tack, Pi.add_apply,Fin.lastCases_last,Fin.lastCases_castSucc, stem,levelx,u]
 rw [slat,he]; unfold shortLap radius weave smoothZip zip bleat -- order tune dynamic
 simp only [Axis, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc,tack, Fin.lastCases_last,Fin.lastCases_castSucc] -- name/order & expansions
 rw [amp_sq]; simp only [Fin.sum_univ_castSucc]; push_cast; ring
end YM.CF.Crest.Sleet
