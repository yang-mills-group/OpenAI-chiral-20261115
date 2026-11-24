import YM.SU5.FiniteGaugeData.Chrono.Strobel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
variable (A:Repertory Y h R L a) (x:Decko Y h a)(w:Vect Y h a 0)
local notation "G" i:max=> store Y h i R L a A
local notation "V"=> Vect Y h a 0
local notation "H"=> A.space
open scoped NNReal
abbrev StripS := ℕ→₀ ℂ
section
open OS.Semigroup
variable {H':Hilbert}{a':Axis}(S':OS.Semigroup H' a')
def team (c:StripS):H'.Op:= Finsupp.linearCombination ℂ (fun k:ℕ=> (S'.E 1)^k) c
private lemma budgetH (z:ℂ)(ε:ℝ)(p:0<ε): ∃ c:StripS, ‖S'.F z - team S' c‖ < ε:=by
 let X:= S'.E 1
 have he:S'.F z∈ closure (StarAlgebra.adjoin ℂ {S'.E 1}:Set H'.Op) := cfcHom_mem_elemental (S'.stare 1).isStarNormal (S'.roots z)
 obtain ⟨y,p,a⟩:= Metric.mem_closure_iff.mp he ε p
 change y∈ Subalgebra.toSubmodule (StarAlgebra.adjoin ℂ ({X}:Set H'.Op)).toSubalgebra at p
 rw [StarAlgebra.adjoin_eq_span, show (({X}:Set H'.Op)∪ star {X})={X} from ?_, ← Submonoid.powers_eq_closure] at p -- pointwise
 · change y∈ Submodule.span ℂ (Set.range fun k:ℕ=> X^k) at p
   obtain ⟨c,rfl⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp p
   rw [dist_eq_norm] at a; exact ⟨c,a⟩
 ext t; have ht:star X=X:= S'.sym 1; simp [ht]; constructor; exact fun h=> (star_star t).symm.trans ((congrArg star h).trans ht); exact fun h=> h.symm ▸ h.symm ▸ ht

def reachH (t:ℝ)(p:ℝ≥0) : H'.Op:= (S'.edge t).comp (S'.E p)
lemma reachH_seed (K: Finset H'.space)(t:ℝ)(u:ℝ≥0)(ε:ℝ)(p:0<ε): ∃ c:StripS, ‖team S' c‖ ≤ 1+ε ∧ ∀ x∈ K,dist (team S' c x) (reachH S' t u x) < ε:=by
 classical
 let W':= 1+ ∑ x∈ K, ‖x‖; have he: 0≤ (∑ x∈ K, ‖x‖):=sum_nonneg fun i _=>norm_nonneg _; have hV:0<W':=by unfold W'; linarith
 have hr:∀ᶠ v:ℝ≥0 in 𝓝[>] u,∀ x∈K,dist (reachH S' t v x) (reachH S' t u x)<ε/2:=by
   rw [eventually_all_finset]; intro x g; exact (Metric.tendsto_nhds.mp ((S'.edge t).continuous.continuousAt.tendsto.comp ((S'.continuousE x).tendsto u)) _ (show 0<ε/2 from by positivity)).filter_mono nhdsWithin_le_nhds
 obtain ⟨r,h,u'⟩:= (hr.and self_mem_nhdsWithin).exists; have hx:0<r:= lt_of_le_of_lt u.property u'; let z:= OS.Semigroup.duration r+sideways t
 obtain ⟨c,g⟩:= budgetH S' z (ε/2/W') (by positivity)
 have e:reachH S' t r=S'.F z:= by unfold reachH; rw [←S'.roots_heat hx]; exact S'.along (OS.Semigroup.dur.mpr hx) t
 refine ⟨c,?_,fun i a=>?_⟩
 · have v:= S'.norm_row (z:=z) (OS.Semigroup.length.mpr hx); have hw:‖team S' c-S'.F z‖≤ε:=by rw [norm_sub_rev]; refine g.le.trans ((div_le_iff₀ hV).mpr ?_); unfold W'; nlinarith
   exact by linarith [norm_le_norm_sub_add (team S' c) (S'.F z)]
 apply lt_of_le_of_lt (dist_triangle _ (reachH S' t r i) _)
 specialize h i a
 have hb: ‖i‖ ≤ W':= le_trans (le_trans (le_rfl : ‖i‖ ≤ ‖i‖) (single_le_sum (f:=fun x:H'=>‖x‖) (fun _ _=> norm_nonneg _) a)) (le_add_of_nonneg_left zero_le_one)
 have hp: dist (team S' c i) (reachH S' t r i)≤ ε/2:=by
    rw [e,dist_comm,dist_eq_norm]; change ‖(S'.F z-team S' c) i‖ ≤ _; exact ((S'.F z-team S' c).le_opNorm i).trans ((mul_le_mul g.le hb (norm_nonneg _) ((norm_nonneg _).trans g.le)).trans_eq (div_mul_cancel₀ _ hV.ne'))
 linarith

end
-- born from weighted POSITIVE-DIRECTION translations in the real step units. not purchase arbitrary constant on descendants. Each term actual both and legs reflected on positive plane. Sum as ONE.
local notation "C"=> tempo_aux Y h R L a A
variable (x y: Decko Y h a)(c:StripS)
def bat (x:Decko Y h a): Decko Y h a:= Finsupp.linearCombination ℂ (fun k:ℕ=> vectorT Y h a x (tassel Λ s*k)) c -- arg order tune
def browser (x y:Decko Y h a) : W (tent Y h):= helve Kₜ a x.val (bat Y h s a c y).val
lemma groups (d:ℕ): thetaX Λ s (tassel Λ s*d)= (d:ℝ≥0):=by
 have he:0<((tassel Λ s):ℝ≥0):=by exact_mod_cast tassel_pos (Λ:=Λ) s -- tune
 unfold thetaX; push_cast; field_simp
lemma gather_B : store Y h s R L a A (bat Y h s a c y) = team (tempo_aux Y h R L a A) c ((G s) y):=by
 have h1 (k:ℕ) : ((C).E 1)^k = rail Y h R L a A (thetaX Λ s (tassel Λ s*k)):=by rw [← OS.Semigroup.clock_mul,groups,nsmul_eq_mul,mul_one]; rfl
 unfold bat team; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,h1, map_sum]; rw [ContinuousLinearMap.sum_apply]; exact sum_congr rfl fun i _=> by rw [rail_actual,ContinuousLinearMap.smul_apply,map_smul,clock_own]
lemma browser_e : E s (browser Y h s a c x y).val= inner ℂ ((G s) x) (team (tempo_aux Y h R L a A) c ((G s) y)):= by rw [←gather_B]; exact (lawStore ..).symm
#print axioms reachH_seed
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
