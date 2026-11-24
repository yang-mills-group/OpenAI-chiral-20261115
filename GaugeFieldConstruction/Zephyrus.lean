import GaugeFieldConstruction.Navet
import GaugeFieldConstruction.Loomcost
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical
open FlightFlux Fluxim
open Tulip Lat Spire Phase Cube
open AnalyticBridge VerifiedReset Taxi Push.Uniform
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
variable {n:Side}{p:BudgetPoint}{o:Skye.Seat n}
-- nearest paths
lemma PathS(x:Cover):∃ w:Walk,w.length ≤ lateral x ∧ ∀ (n:Side)(o:Site n),stop o w=o+wrap _ x:=by
 apply climb (fun x: Cover=>∃ w:Walk,w.length ≤ lateral x ∧ ∀ (n:Side)(o:Site n),stop o w=o+wrap _ x) x
 · exact ⟨[],Nat.zero_le _,fun _ _=>by simp [stop]⟩
 intro i j h ⟨w,v,u⟩ y p q; rcases q with q|q
 · refine ⟨w++[negDir i],by simpa [p] using Nat.add_le_add_right v 1,?_⟩; intro n o; rw [stop_append,u,q]; change o+ wrap n (y+(step i:Cover))+(-(step i:Site n))=o+wrap _ y; rw [map_add,wrap_step]; abel
 refine ⟨w++[posDir i],by simpa [p] using Nat.add_le_add_right v 1,?_⟩; intro n o; rw [stop_append, u,q]; change o+wrap n j+(step i:Site n)=o+wrap _ (j+(step i:Cover)); rw [map_add,wrap_step]; abel
abbrev PathB(x:Cover):Walk:= (PathS x).choose
def TarA (o:Skye.Seat n)(x:Cover) :Pane n→ SU.E:=fun i=> travel i o (PathB (spotSize o x))
lemma tare (x:Cover)(U:Pane n)(g:Skye.Seat n→ SU.E): TarA o x (Lattice.gauge g U)= g o* TarA o x U * (g (node (parked o x)))⁻¹:=by unfold TarA; rw [travel_gauge,mark_node,(PathS _).choose_spec.2]
lemma TarOne(x:Cover): TarA o x 1=1:=by
 have he(w:Walk)(p:Skye.Seat n): travel (1:Pane n) p w=1:=by induction w generalizing p with | nil=>rfl | cons i l ih=> simp only [travel,ih,mul_one]; simp [Step.read]
 apply he
abbrev vSpace := SU.F→SU.F→ℂ
section
open scoped Matrix.Norms.Frobenius
private def TFund: SU.group.Mat→L[ℝ] vSpace:= LinearMap.toContinuousLinearMap ⟨⟨(fun i x y=> i x y),fun a b=>rfl⟩,fun a b=>rfl⟩
lemma stan_1(k m:ℕ): ∃ C:ℝ,1≤C∧∀ n:Side,∀ (p:Site n)(V:Config SU.group n)(w:Walk),w.length ≤ m → Allows k (fun a:Directions SU.group n=> fun x y:SU.F=> SU.fund (travel (increment V a) p w) x y) 0 C:=by
 obtain ⟨C,c,H⟩:= linkage_v SU.group k; let A:=tautF TFund*travelCost SU.group k m C; refine ⟨max 1 A,le_max_left ..,fun n p V w h=> Allows.mono ?_ (le_max_right ..)⟩
 exact Allows.linear TFund (travel_jets (G:=SU.group) (fun j=>H n j V) p h) (le_refl _) -- name
end
open scoped Matrix.Norms.L2Operator
open Fock
attribute [local instance] opCStarAlgebra
private def WitJ (u:vSpace):Pal:= (1:Op SpinIdx)⊗ₖ SU.triple (Matrix.of u)
private lemma WitC : ContDiff ℝ ω WitJ:=by
 let H:=WitJ; let A(x:vSpace):Hove.Kt→Hove.Kt→ℂ:=fun i j=> WitJ x i j
 let K: (Hove.Kt→Hove.Kt→ℂ)→L[ℝ] Pal:= LinearMap.toContinuousLinearMap ⟨⟨(fun a=> Matrix.of a),fun a b=>rfl⟩,fun a b=>rfl⟩
 suffices h:ContDiff ℝ ω A by exact K.contDiff.comp h
 have hex(a b:SU.F):ContDiff ℝ ω (fun x:vSpace=>star (x a b)):=Complex.conjCLE.toContinuousLinearMap.contDiff.comp (show ContDiff ℝ ω (fun x:vSpace=> x a b) from by fun_prop)
 apply contDiff_pi.mpr; rintro ⟨i,j,a|a⟩ <;> apply contDiff_pi.mpr <;> rintro ⟨u,v,b|b⟩ <;> unfold A WitJ SU.triple SU.each <;> simp only [Join.both,Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.kronecker_apply, cc_apply,ExTwo.wedge_entry,Matrix.of_apply]
 all_goals refine contDiff_const.mul (contDiff_const.mul ?_)
 all_goals first| exact contDiff_const| exact hex ..| fun_prop -- norm TC
lemma Kin_1(k m:ℕ) : ∃ C:ℝ,1≤C∧∀ n:Side,∀ (p:Site n)(V:Config SU.group n)(w:Walk),w.length ≤ m → Allows k (fun a:Directions SU.group n=> KinX (travel (increment V a) p w)) 0 C:=by
 obtain ⟨C,c,H⟩:=stan_1 k m; let S:=closedBall (0:vSpace) C; obtain ⟨K,z,h⟩:=exists_allows (isCompact_closedBall (0:vSpace) C) (fun i _=>WitC.contDiffAt (x:=i)) k
 refine ⟨max 1 (composeCost k K C),le_max_left ..,fun n p V w t=>?_⟩; let F(x:Directions SU.group n):=travel (increment V x) p w; let Z(x):vSpace:= fun i j:SU.F=> SU.fund (F x) i j; have he: Z 0∈ S:=by rw [show Z 0∈ S↔ dist (Z 0) 0≤ C from mem_closedBall]; exact (dist_zero_right ..).le.trans (H n p V w t|>.value)
 -- definitional arrow Eta? Matrix.of
 exact Allows.mono ((h (Z 0) he).comp (H n p V w t)) (le_max_right ..)
abbrev LedgeK(x:Cover)(o:Skye.Seat n):Pane n→ Pal:= KinX∘ TarA o x
lemma Ledge_o(x:Cover)(p:lateral x ≤4): LocalOn (Pax o) (LedgeK x o):=by
 let W:=PathB (spotSize o x); intro U V i; apply congrArg KinX; apply travel_local (K:=SU.E) o W U V; apply agrees_mono i; intro y h; apply halo_spec.mpr; have ht:W.length≤12:=(PathS _).choose_spec.1.trans (spot_price o x p); exact ⟨o,mem_singleton_self _,(Extra.Iteration.Shapes.visits_dist o y W h).trans (ht.trans (by decide))⟩
lemma KinC : Continuous KinX:=by
 apply continuous_matrix; rintro ⟨i,j⟩ ⟨u,v⟩; unfold KinX; simp only [Matrix.kronecker_apply]; exact continuous_const.mul (SU.matter_cont.matrix_elem j v)
lemma Ledge_Pay : ∃ M:ℝ,0<M ∧∀ (n:Side)(o:Skye.Seat n)(x:Cover)(p:BudgetPoint), lateral x ≤ 4→ p.order ≤6 → p.power≤3→ Housing.Haw p o (Pax o) (LedgeK x o) M:=by
 obtain ⟨C,h,H⟩:=Kin_1 6 12; have hp:=lt_of_lt_of_le zero_lt_one h; refine ⟨C*((25:ℝ)^3)^6,by positivity,fun n o x p v k u=>?_⟩; have hx:= Ledge_o (o:=o) x v; refine ⟨hx,KinC.comp (by unfold TarA; fun_prop),fun i w=>?_⟩ -- we don't need ping
 exact Housing.trophy (Y:=LedgeK x o) ((H (More n) o i (PathB _) ((PathS _).choose_spec.1.trans (spot_price o x v))).order k) u k (Finset.Subset.refl _) hx
end Layout
end Lenten
end YM.CF.TableF
end
