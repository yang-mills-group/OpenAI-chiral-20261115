import YM.CF.Chaff.Temp
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
abbrev sailX(P:BudgetPoint)(X:Support N):= Lattice.halo (2*P.B) X
abbrev taleX(P:BudgetPoint)(X:Support N):= Lattice.halo (3*P.B) X
lemma arms_e (S:Support N) : sailX P S⊆ taleX P S:=Corona.halo_mono (by omega) le_rfl
lemma link_l (S:Support N)(v:12 ≤P.B): RG.inspected (sailX P S)⊆ taleX P S:= Subset.trans (Yaw.touchK _) (by
 unfold sailX taleX; intro i hi; obtain ⟨u,h,g⟩:=halo_spec.mp hi; obtain ⟨q,f,t⟩:=halo_spec.mp h; exact halo_spec.mpr ⟨q,f,(separation_triangle _ u _).trans (by omega)⟩)
lemma fenceW (S:Support N){U W:Wilson.Config SU.group N}(p: Agrees (inspected S) U W) (z:ℝ): pingS z S U ↔ pingS z S W:=by -- U bind
 have he(i:Face (Per N))(l:¬ Disjoint S (touched i)):faceValue U i=faceValue W i:=by
    apply travel_local _ _ U W; apply agrees_mono p; intro y g; refine mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩); rw [if_neg l]; exact List.mem_toFinset.mpr g
 exact ⟨fun v i w=> he i w ▸ v i w,fun v i w=> (he i w).symm ▸ v i w⟩
include A pH l
lemma fare_H (T:Stamp m B)(X:Pane Λ)(g:pingS P.threshold (sailX P T) X)(y: Ids Λ) : Agrees T (R (X,y)) X:=by
 intro i hv hx; apply A.lamp; let f:= Lattice.halo (2*P.B) T; have he:pingS a f X:= fun b u=>(g b u).trans_le pH; apply Disjoint.mono_right _ (show Disjoint (flags a X) f from (show Disjoint f _ from ping_le he).symm) -- tune
 apply Corona.halo_mono (show c ≤2*P.B by omega); exact insert_subset hv (singleton_subset_iff.mpr hx)
def pulseQ (p:0≤e)(R:Scree.Loom Λ)(F:Briar m B e→ Cipher Λ)(P:BudgetPoint)(S:Stamp m B):InkD Λ:=
 let U(x:Pane Λ):= polarU m B p (R (x,Classical.arbitrary _)); let b:= hollow (n:=Dwell Λ) (Pastry.pane (F (floorP m B p)))
 Set.indicator {x:Pane Λ|pingS P.threshold (sailX P S) x} fun x:Pane Λ=> F (U x)-b -- unused S' issue
include v h
lemma base_P {y:Briar m B e}(i:Pane Λ)(f:pingS P.threshold (sailX P S) i)(u: Agrees S i y.val): pulseQ p R D P S i= D y-hollow (Pastry.pane (D (floorP m B p))):=by
 unfold pulseQ; rw [Set.indicator_of_mem (show i∈ _ from f)]; let Z:=Classical.arbitrary (Ids Λ); let X:= R (i,Z); have he:= A.paid (i,Z); change D (polarU m B p X)-_= _; rw [show polarU m B p X= _ from claw p X (he.shrink v.le)]; apply congrArg (fun w=> w-hollow (n:=Dwell Λ) _)
 exact h.locality _ _ (fun j t k=> (fare_H A pH l S i f Z j t k).trans (u j t k)) -- tune
local notation "Φ" => pulseQ p R D P S
lemma currentX (v':12 ≤ P.B):LocalOn (taleX P S) Φ:=by
 intro x y k; let Z:= sailX P S
 have he:= fenceW Z (agrees_mono k (Finset.coe_subset.mpr (link_l _ v'))) P.threshold -- tune
 by_cases q:pingS P.threshold Z x
 · have hy:= he.mp q; let t:=Classical.arbitrary (Ids Λ); let X:=R (x,t); let w:Briar m B e:=⟨X,(A.paid _).shrink v.le⟩; have hu:Agrees S x w.val:=fun j ht hx=>(fare_H A pH l S x q t j ht hx).symm
   rw [base_P p h A pH v l x q hu]; exact Eq.symm (base_P p h A pH v l y hy (fun i hi ht=> (k _ (halo_subset _ S hi) (halo_subset _ S ht)).symm.trans (hu _ hi ht)))
 simp only [pulseQ]; rw [Set.indicator_of_notMem (show x∉_ from q),Set.indicator_of_notMem (show y∉_ from fun y'=>q (he.mpr y'))]
lemma φs_b (i:Pane Λ) : Flour (camp S) (Φ i).val:=by
 unfold pulseQ; by_cases z:i ∈ {x:Pane Λ|pingS P.threshold (sailX P S) x}; swap; · rw [Set.indicator_of_notMem z]; exact Flour.trivial
 rw [Set.indicator_of_mem z]; exact (Pastry.stretch (camp S)).sub_mem (h.grammar _) ((stretch_ok (hollow _)).2 (Flour.grainE.smul _))
lemma φs_g (i: Pane Λ)(u:Court m B) : Φ (Lattice.gauge u i)=paintR false false (tradew Λ u) (Φ i):=by
 have hv:=pingB (X:=sailX P S) (e:=P.threshold) i u; by_cases z:pingS P.threshold (sailX P S) i; swap; · unfold pulseQ; rw [Set.indicator_of_notMem (show i∉_ from z),Set.indicator_of_notMem (show Lattice.gauge u i∉_ from mt hv.mp z)]; exact Eq.symm (map_zero _)
 let t:=Classical.arbitrary (Ids Λ); let y:Briar m B e:=⟨R (i,t),(A.paid _).shrink v.le⟩; have hu:Agrees S i y.val:=fun j h t'=> (fare_H A pH l S i z t j h t').symm
 have he:Agrees S (Lattice.gauge u i) (routeS u y).val:=fun j t v=>by change _* _ * _= _* _* _; exact congrArg (fun x'=> u _ * x' * (u _)⁻¹) (hu j t v)
 rw [base_P p h A pH v l (gauge u i) (hv.mpr z) he, base_P p h A pH v l i z hu,h.gauge,map_sub,show paintR false false (tradew Λ u) (hollow _)=_ from Pastry.fold_hollow ..] -- tune
lemma pulse_m : Measurable Φ:=by
 let z:=Classical.arbitrary (Ids Λ); let X(x:Pane Λ):= R (x,z); have he:Measurable X:= A.bill.comp (measurable_id.prodMk measurable_const)
 let f(x:Pane Λ):= polarU m B p (X x); have hq:Measurable f := by
    apply Measurable.subtype_mk; change Measurable fun i=> (polarU m B p (X i)).val; simp_rw [claw p (X _) ((A.paid _).shrink v.le)]; exact he
 exact (Measurable.indicator ((h.continuous_T.measurable.comp hq).sub measurable_const) (ping_o (e:=P.threshold) (X:= sailX P S)).measurableSet)
end YM.CF.Chaff
