import YM.CF.BPress.Sugar.Tool
import YM.CF.BPress.Mount.True
/- $R_M$ design. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Sugar
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
namespace Crew
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage Wealth Weave Pressure Mount.Silhouette Awards
variable {X:Stage N}{Y:Driver N} {H:Crew A}{e c d:ℝ}{k:ℕ}{x:mState N A}
lemma aut (X: Crew A)(x:mState N A): autograph A X.Z X.tile (layout x) (X.harborT x) (Lily.interest A (X.tape x)):= by intro i g h; rw [Lily.invoice A (X.tape x) _ h]; rfl
variable (F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)(p:H.Role x)
local notation "ψ_"=> α F Q x p
include F Q p
lemma deep_glow (i:A.Index) : Along (deep A i X.W.M) (readingX A H.Z H.tile i (clueT (T:=H.T) (y:=H.y) A (H.harborT x) (layout x) i)) (ψ_).val:=by
 let t:=(F.pay x p).licence; let y:= clueT (T:=H.T) (y:=H.y) A (H.harborT x) (layout x) i; let b:= readingX A H.Z H.tile i y; let T:= deep A i X.W.M
 have ht:T⊆ safe A R X.W (H.unsea R x):= fun y v=> mem_compl.mpr fun e=> (mem_filter.mp v).2 (hurt F.dusk (halo_subset X.W.T.val _ e)|>.1)
 let X₁:= tape H x; let C:=spline A H.Z H.tile i y; let C':= H.fury R X x; have he (z:Site (More N))(h:z∈T): (b.X z= (ψ_).val.X z) ∧ ∀ v,C v z=C' v z:=
   ⟨(t.progress.desert (deep_sub A i _ h) (mem_filter.mp h).2).1.symm,fun v=>((t.progress.desert (deep_sub A i _ h) (mem_filter.mp h).2).2 v).symm⟩
 refine ⟨?_,fun _ g=>(he _ g).1, fun i' h=>?_, fun z v K=> ?_⟩
 · intro i j g; exact (F.calm x p i (inside_cov ht ((inside_iff ..).2 ⟨j,g⟩))).symm
 · have ht':i'∉ Picks A R (H.unsea R x):=fun u=> (mem_filter.mp u).2.1 ⟨i,deep_sub A i _ h⟩; change decide (i' ∈ (∅:Support N))= decide (i'∈_); rw [decide_eq_false (notMem_empty _), decide_eq_false ht'] -- tune
 have hf:= (he z v).2; apply ContinuousMap.ext; intro w; cases K; exact hf w.val; exact congrArg (fun f=> deriv f w.val) (funext hf)
variable (V:Scree.GramM N) (u:ℝ) (a:V.p.threshold=temp H.y)
open Engine.Shot Vesper Store
include a
lemma bleak (i:A.Index) (S: Support (More N))(v: ActY N)(z:Rod N)(h:S ⊆ deep A i X.W.M) : barren V (ShotZ A u (H.harborT x) (Lily.interest A (H.tape x)) (areaC R H X x) v z) S:=by
 let f:= H.flag x; refine ⟨fun t' g=>?_, disjoint_left.mpr (fun i' h' v=>?_ )⟩
 · exact if_neg fun t=> (mem_filter.mp (h g)).2 ((mem_filter.mp t).2.2) -- tune yKick simp def
 obtain ⟨j,H,z⟩:= (F.pay x p).blaze i' (show i' ∈ RG.flags (temp H.y) (H.port x) from a ▸ (show i' ∈ RG.flags V.p.threshold (H.port x) from h')); exact (mem_filter.mp (h v)).2 (near_gap (halo_subset _ _ H))
end Crew
end YM.CF.BPress.Sugar
