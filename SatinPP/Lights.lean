
import SatinPP.Program
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]

lemma sheath_closure :sheath ⊆ closure inside:=by
 intro z h
 have t:Tendsto (fun x:ℝ=>z+x) (𝓝[>] 0) (𝓝 z):=by
    simpa only [ofReal_zero,add_zero] using (continuous_ofReal.tendsto 0).const_add z|>.mono_left nhdsWithin_le_nhds
 exact mem_closure_of_tendsto t (Eventually.mono self_mem_nhdsWithin (fun x hx=>show 0<(z+x).re from add_pos_of_nonneg_of_pos h.1 hx))

theorem Harbor.beacons {f g:ℂ→X}(p:Harbor f)(q:Harbor g)
    (eq:∀t:ℝ,0<t→f (t:ℂ)=g t): EqOn f g sheath:=by
  have t:Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝[>] 1) (𝓝[≠] 1):=by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
         (by rw[←ofReal_one]; exact (continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with i (hi:1 < i); change _≠1; simpa using hi.ne'
  have r:∃ᶠ z:ℂ in 𝓝[≠] 1,f z=g z:=by
    intro a
    obtain ⟨i,v,(t:1 < i)⟩:=((t.eventually a).and self_mem_nhdsWithin).exists
    exact v (eq i (lt_trans zero_lt_one t))
  exact (p.free.eqOn_of_preconnected_of_frequently_eq q.free (convex_halfSpace_re_gt 0).isPreconnected eu r).of_subset_closure p.keep q.keep inside_subset_sheath sheath_closure


namespace Harbor
lemma mul {f g:ℂ→ℂ}(p:Harbor f)(q:Harbor g):Harbor (fun z=> f z*g z):=p.smul q
lemma sum {I:Type*} (s:Finset I){f:I→ℂ→X}(p:∀i,Harbor (f i)):
   Harbor (fun z=>∑i∈s,f i z):=by
 classical
 induction s using Finset.induction with
 | empty=>simpa using Harbor.const (0:X)
 | insert i s g h=> simpa [g] using (p i).add h
lemma prod {I:Type*}(s:Finset I){f:I→ℂ→ℂ}(p:∀i,Harbor (f i)):
 Harbor (fun z=>∏ i∈s,f i z):=by
 classical
 induction s using Finset.induction with
 | empty=>simpa using Harbor.const (1:ℂ)
 | insert i s g h=>simpa [g] using (p i).mul h

variable {I:Type*}[Fintype I][DecidableEq I]
lemma det {M:ℂ→Matrix I I ℂ}
   (p:∀i j,Harbor (fun z=>M z i j)):
   Harbor (fun z=>(M z).det):=by
 simp_rw [Matrix.det_apply']


 refine sum _ (f:=fun σ z=> (( (Equiv.Perm.sign σ:ℤ):ℂ)*∏ i,M z (σ i) i))
    fun σ=> (Harbor.const _).mul (prod _ (f:=fun i z=> M z (σ i) i) fun i=>p ..)

def Flash (B:Matrix I I ℂ):Prop:= B.det≠0 ∧ ∀i,B i i≠0
lemma flare {M:ℂ→Matrix I I ℂ}
  (p:∀i j,Harbor (fun z=> M z i j))(h:Flash (M 1)) {a b:ℝ}(v:0≤a)(u:a<b):
  ∃t∈Ioo a b, Flash (M (sideways t)):=by
 let f(z):=(M z).det * ∏ i, M z i i
 have hf :Harbor f:= (det p).mul (prod _ (f:=fun i z=>M z i i) (fun i=>p i i))
 have e(z): f z≠0 ↔ Flash (M z) := by
   simp [Flash,f,Finset.prod_ne_zero_iff]
 by_contra! H
 exact (e 1 |>.mpr h)
   ((vanish_seam hf v u (fun x t=> not_not.mp (mt ((e _).mp) (H x t)))) (inside_subset_sheath eu))

end Harbor
#print axioms Harbor.flare
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

