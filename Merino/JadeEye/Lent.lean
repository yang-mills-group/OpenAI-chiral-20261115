import Merino.JadeEye.Give
import Merino.JadeEye.Sap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

open Dial BProof Brooch
open TreasuryFog Paige Vault
attribute [local instance] loreM loreN
open Roots

variable {n:Side}{P:BudgetPoint}{K:Scree.Loom n}{F:SOp n}{o:Seat n}
variable {d v r C R a b:ℝ}

def wage (F:SOp n)(b C:ℝ)(P:BudgetPoint)(R:ℝ):ℝ:=
 ‖(F (profile 1)).trace‖+b*C*lime P R^2

lemma shadeD {m:ℕ}{G:Cuff.Bows n→ℂ}{S:ℝ} (h:Jet.Allows m G 0 S)
    (b:Bool):Jet.Allows m (fun x=>cSignX b (G x)) 0 S:=by
 cases b;exact h
 let L:=Complex.conjCLE.toContinuousLinearMap
 change Jet.Allows _ (fun u=> L (G u)) _ _
 simpa [one_mul] using h.linear L (show ‖L‖≤1 from L.opNorm_le_bound zero_le_one fun x=> by
     simp [L])


open Forge Cuff
lemma tilt (P:BudgetPoint)(i: Support (More n))(V:Pane n):
 ∃ L:Bows n→L[ℝ]Bows n, ‖L‖≤P.threshold ∧ pressQ P i V=increment V ∘ L:=by
 let L:Bows n→L[ℝ]Bows n:=(wakeB (Rill.unrest i P.B)).comp (P.threshold • ContinuousLinearMap.id ℝ _)
 refine ⟨L,L.opNorm_le_bound P.threshold_pos.le ?_,rfl⟩
 have u:=P.threshold_pos
 intro x
 rw [pi_norm_le_iff_of_nonneg (by positivity)]
 intro t
 change ‖wakeB _ (P.threshold • x) t‖≤_
 rw [steadyB]
 split; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg u.le];exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x t) u.le
 rw [norm_zero];positivity

abbrev pearl (p:BudgetPoint)(o:Seat n)(K:Scree.Loom n)(F:SOp n)(j:Bool):=
 fun x=>cSignX j (traceCost K p o F x)

open Window Buffered
lemma streak (q:Potion P n d v r C R)(h: Skylit P d K)
   (j:Trunk o F (P.B/10) a b d)(ha:0≤a)(hb:0≤b)
   (k:Bool)(o₁:Site n)(u: separation (node o₁) o ≤ P.B)(g:12≤P.B)
   (ord:P.order=6):
   Exhibit P o₁ (pearl P o K F k) (7 * wage F b C P R):=by


 let A:= wage F b C P R
 have hc:=q.ride.price
 have hp:0≤A:=by unfold A wage; positivity
 have hi: casing P o ⊆ sleeve P o₁:=by
    intro i w
    obtain ⟨r',g',s'⟩:=halo_spec.mp w
    rw [mem_singleton.mp g'] at s'
    exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle _ o i).trans (by omega)⟩
 refine ⟨by positivity,?_,?_, fun x y=>congrArg (cSignX k) (sheen_gauge h ha j _ _),?_⟩
 · have e:Continuous fun p:Op (Single n)=> cSignX k p.trace:=by
      cases k
      · exact continuous_id.matrix_trace
      exact continuous_id.matrix_trace.star
   exact e.measurable.comp (mask_meas h j.pay)
 · intro x y t; unfold pearl traceCost
   rw [mask_local h ha j x y (agrees_mono t hi)]
 intro Y f D Z V p
 rw [ord]
 have hg: Allows 6 (fun x=> traceCost K P o F (pressQ P Z V.1 x)) (0:tangD n) A:=by
    by_cases e:V.1∈pass P o
    · obtain ⟨T,r',t'⟩:=tilt P Z V.1
      rw [t']
      exact spend q h j ha V.1 e T r'
    have w:purse P.B o⊆Y.val:=(Corona.halo_mono (by exact Nat.le_add_right P.B 12) le_rfl).trans (hi.trans f)
    refine (Jet.allows_const (v:=(0:ℂ)) (n:=6) (x:=(0:tangD n)) (by simpa using hp)).germ ?_
    filter_upwards [whileLit (Z:=Z) p] with y d1
    let z:Orbit n:=(pressQ P Z V.1 y,V.2)
    have ez:z.1∉pass P o:=mt ((pingFix (i:=z) w d1).mp) (mt ((pingFix w p).mpr) e)
    change 0=traceCost K P o F z.1
    simp only [traceCost,masked, Set.indicator_of_notMem ez,Matrix.trace_zero]

 exact (show ((↑(6:ℕ):ℝ)+1:ℝ)=7 from by norm_num) ▸ bare_p _ _ (shadeD hg k)

