import Anomaly.Ward.Masked
import YM.CF.Char.Gel
import YM.SU5.Exchange.Pilot.Marquet
/-! W_era estimate on scalar with the (130) actor mask.
    Uses project dilation budgets.Newt on all-Pulse. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Rank.Spindle LampP Exterior Precision Wilson
open Pressure Vow
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "G"=> SU.group
-- promoted costs on BCH.L
structure FlowPrice (v f:ℝ) (j:ℕ) :Prop where
 cost : 0<v
 size : 0<f
 flies : ∀ {N:Side} {w:tangD N→ SU.group.Color}{b:ℝ}(x:SU.group.Color), 0<b → b ≤ v → ‖x‖≤ b → Allows j w 0 b → Allows j (fun y=> Char.mount (w y,x)) 0 (f*b)∧ ∀ᶠ y in 𝓝 0, SU.group.lieExp (Char.mount (w y,x))= SU.group.lieExp (w y)*SU.group.lieExp x

lemma flown (j:ℕ)(v:1 ≤ j):∃ f g:ℝ, FlowPrice f g j:=by
 obtain ⟨f,g,p,w,e⟩:= Char.pass_n G j v; exact ⟨_,_,p,w,fun x u h t b=> e _ _ _ u h b x t⟩
variable {N:Side}{j c:ℕ}{B:BudgetPoint}{Y:SOp N}{q:ℕ}{K:Scree.Loom N}{o:Site N}{v f α C M d a w s:ℝ} {T:tableQ SU.group (More N) ℂ}
local notation "Q"=>tangD N
local notation "V_"=>node o
local notation "U_"=>traceMeter B K o Y
local notation "P_"=>halo q {node o}
local notation "H_"=>halo B.B {node o}
variable (R:Knit Y (node o) q d α M C w B.order T)(L:mintQ α C d B.order)(G':FlowPrice v f B.order)
variable (r:Rules SU.group) (c':2*(q+1)<(More N).val)(t:4*(q:ℝ)*B.threshold≤r.c)
local notation "s_"=> ((8*(q:ℝ)+1)*B.threshold)
include G'
lemma conjugateJet {S:Support (More N)}{A:Pane N}{κ:Seat N→ SU.group.El}(u:Q)(b:0<a) (h:a ≤ v)(hv:‖u‖ ≤ a)(z:Agrees S (Lattice.gauge κ A) (increment 1 u))(g:B.threshold ≤ a)(D:Support (More N)):∃ F: Q→Q, Allows B.order F 0 (f*a) ∧ ∀ᶠ y in 𝓝 (0:Q),Agrees S (Lattice.gauge κ (pressQ B D A y)) (increment 1 (F y)):=by
 -- p(e):G adj
 let τ:=B.threshold; let R:= unrest D B.B
 let U(i:Bond (More N)):Q→L[ℝ] SU.group.Color:= if i∈R then (SU.group.adjoint (κ i.1)).toContinuousLinearMap ∘L (τ • ContinuousLinearMap.proj i) else 0
 let F(y:Q)(i:Bond (More N)):= Char.mount (U i y,u i)
 have hu(i:Bond (More N)): Allows B.order (fun y:Q=> U i y) 0 a:=by
    apply Jet.allows_linear; swap; · rw [map_zero,norm_zero]; exact b.le
    apply ContinuousLinearMap.opNorm_le_bound _ b.le; intro x; unfold U; split
    · rw [ContinuousLinearMap.comp_apply]; change ‖SU.group.adjoint _ (τ • x i)‖ ≤ _;  unfold τ; rw [SU.group.norm_adjoint,norm_smul,Real.norm_of_nonneg B.threshold_pos.le]; exact mul_le_mul g (norm_le_pi_norm x i) (norm_nonneg _) b.le
    rw [ContinuousLinearMap.zero_apply,norm_zero]; exact mul_nonneg b.le (norm_nonneg _)
 have h(i:Bond (More N)):=G'.flies (u i) b h ((norm_le_pi_norm ..).trans hv) (hu i)
 refine ⟨F, Jet.allows_pi (mul_nonneg G'.size.le b.le) (fun i=> (h i).1),?_⟩
 filter_upwards [eventually_all.mpr fun i=> (h i).2] with y hy
 intro i p q
 rw [show increment 1 (F y) i= _ from mul_one (SU.group.lieExp (F y i)),show SU.group.lieExp (F y i)= _ from hy i]
 have ha:=z i p q; unfold increment Lattice.gauge at ha; unfold pressQ Forge.gyrate Function.comp increment Lattice.gauge -- tune namespaces
 change κ i.1 * (SU.group.lieExp _ * A i)*_ = SU.group.lieExp (U i y)*_
 unfold U; split_ifs with hp
 · rw [Forge.steadyB,if_pos hp]; change κ i.1 * (SU.group.lieExp (τ • y i)*A i)*_ = SU.group.lieExp (SU.group.adjoint (κ i.1) _)*_
   rw [Next.SectorChange.exp_adjoint]; simp only [Pi.one_apply,mul_one] at ha; rw [←ha]; group; rfl
 rw [ContinuousLinearMap.zero_apply,SU.group.mat_lieExp_zero,one_mul,Forge.steadyB,if_neg hp]; simpa using ha

local notation "Ωx"=>2*C*M
local notation "S_"=> Jet.composeCost B.order (2*(2*C*M)*(f*s_)^2) 1
include R L
lemma smallPose (F:Q→Q)(e:Allows B.order F 0 a)(b:0<a)(x:a<α)(Z:0≤2*C*M):Allows B.order (fun i=> rawQ Y (increment 1 (F i))) 0 (Jet.composeCost B.order (2*(2*C*M)*a^2) 1+‖rawQ Y 1‖):=by
 let V:Q→Q:= fun i=> a⁻¹ • F i
 have ht:Allows B.order V 0 1:= by simpa only [abs_of_pos (inv_pos.mpr b),inv_mul_cancel₀ b.ne'] using e.smul a⁻¹
 have hv: PhysicalNext.JointLoad.Heir.Portrait (stepQ Y) 0 B.order a a (2*C*M):=by
    refine ⟨fun i t=> ⟨(R.circle i (t.trans_lt x)).smooth,(R.circle i (t.trans_lt x)).norm_le⟩,step_idle _,?_⟩; rw [R.roles,sub_zero,norm_zero]; exact mul_nonneg Z b.le
 have hP:= Newt.portrait ((by decide: 2≤6)|>.trans B.order_ge) hv b.le le_rfl (x.le.trans L.2.1) ht.value
 refine ((hP.comp (f:=V) ht).add (allows_const 0 (le_refl ‖rawQ Y 1‖))).germ (Eventually.of_forall fun i=>?_)
 change stepQ Y (a • (a⁻¹ • F i))+rawQ Y 1=_; rw [smul_inv_smul₀ b.ne',stepQ,sub_add_cancel]
include r c' t
variable {j₀:ℕ} (J:Roof N s d j₀ K)(u:B.threshold ≤ s)(g:q+j₀+10≤ B.B)
include J u g
lemma hiresQ (h: (8*(q:ℝ)+1)*B.threshold ≤ v)(p:f*((8*(q:ℝ)+1)*B.threshold)<α)(Y':Orbit N)(Z:Aura N)(D W:Support (More N))(x:H_⊆ Z.val)(y:Y'.1∈Sour.σX B Z D): Allows B.order (fun i:Q=> traceMeter B K o Y (pressQ B W Y'.1 i)) 0 (Jet.composeCost B.order (2*(2*C*M)*(f*s_)^2) 1+‖rawQ Y 1‖):=by
 have hp:= G'.size; have ht:= B.threshold_pos; have hz:0 ≤2*C*M:= (R.circle (0:Q) (by rw [norm_zero]; exact L.1)).nonneg; have hf:0< s_:=by positivity
 by_cases w':Disjoint H_ D
 · let A:= Y'.1; have e:pingS B.threshold H_ A:= (pingFix x y).mpr w'
   let f':= fingers A (node o)
   obtain ⟨y',v',T'⟩:= treeCost (node o) r B.threshold_pos t c' (ping_le (Vow.grow_b (Corona.halo_mono (by omega:q≤B.B) le_rfl) e))
   obtain ⟨F,E,Z'⟩:=conjugateJet G' y' hf h (v'.trans (mul_le_mul_of_nonneg_right (by linarith) ht.le)) (show Agrees P_ (Lattice.gauge f' A) (increment 1 y') from fun i q v=> (T' i q v).symm) (by nlinarith [mul_nonneg (Nat.cast_nonneg q) ht.le]) W
   apply (smallPose R L G' F E (mul_pos hp hf) p hz).germ
   filter_upwards [E.smooth.continuousAt.norm.eventually (gt_mem_nhds (E.value.trans_lt p)), Z',whileLit (Z:=W) y] with i w hl u'
   let K:Orbit N:=(pressQ B W Y'.1 i,Y'.2); exact (template_pass R J g u ((pingFix (i:=K) x u').mpr w') f' hl (L.2.2.2.1 (F i) w)).symm
 refine (Jet.allows_const (0:Q) (v:=(0:ℂ)) ?_).germ ?_
 · rw [norm_zero]; apply add_nonneg _ (norm_nonneg _); unfold Jet.composeCost; positivity
 filter_upwards [whileLit (Z:=W) y] with i w
 let K:Orbit N:=(pressQ B W Y'.1 i,Y'.2); unfold traceMeter pinMatrix; rw [Set.indicator_of_notMem (show K.1 ∉ {z|pingS B.threshold H_ z} from mt (pingFix (i:=K) x w).mp w'),Matrix.trace_zero] -- tunes
end YM.CF.Swell.Sonar
