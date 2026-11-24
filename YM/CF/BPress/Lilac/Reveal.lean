import YM.CF.BPress.Lilac.Evil
/- $reference bias windows. Radius uniform w/ g,width pre data. Node uses ONE center per gap. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger
variable {N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
variable {X: Sugar.Stage N}{Y:Driver N}
open Bias Bias.Sails Born Shale
structure ShineZ (p:Born A R X Y)(r:ℕ)(c:ℝ) (z:Fin 5): Prop where
 star (i:A.Index)(u:Tri N): ∃ t∈gazeSet A i r,p.BiasQ z (node (BPress.event t u)) ≤ -c
structure Supply (j:ℕ)(P:Pledge)(D:Side)(ε:ℝ)(r n:ℕ)(c:ℝ)(z:Fin 5) : Prop where
 right :0<c
 power {N: Side}(h:n≤N.val){B:BandWidth}(v:B.D=D.val)(f:r≤B.marked.val){A:Bands (More N) B}{R:Hangar (More N)}{X:Sugar.Stage N}{Y:Driver N}(p:Born A R X Y)(hk:Y.j=j)(κ:Y.ε=ε)(P: Shelf N Y.d j P): ShineZ p r c z -- tune shadow
namespace Supply
variable {j u r n l k:ℕ}{P:Pledge}{ε c b:ℝ}{D:Side}{z:Fin 5} (p:Supply j P D ε r n c z)
include p
lemma mono (g:r≤u)(h:n≤k)(t:b≤c)(a:0<b): Supply j P D ε u k b z:=by refine ⟨a,?_⟩; intro N t' B v f H U V Y P h' k' D'; constructor; intro i l; obtain ⟨j,p,t0⟩:= (p.power (h.trans t') v (g.trans f) P h' k' D').star i l; obtain ⟨x,p,h⟩:=(mem_filter.mp p).2; exact ⟨j,mem_filter.mpr ⟨mem_univ _,x,p,h.trans g⟩, by linarith⟩
omit p
lemma supplyZ (h:1≤j)(P:Pledge)(D:Side)(u:0<ε)(z:Fin 5)(p:z≠0) : ∃ (r n:ℕ)(c:ℝ), Supply j P D ε r n c z:=by
 obtain ⟨T,A⟩:=screen_appear j h P ε u; obtain ⟨r,m,c,u,Y⟩:= B_bias (d:=D) T h Lute.Music.basis (Lute.Music.wave z) (Lute.Music.disallowed p); refine ⟨r,m,c,u,?_⟩; intro N g B v f A' R' X' U F hk κ P; let M:=U.M;  -- tune name replace
 let K:= Rosetta z A' X'.W R' X'.tile; obtain ⟨H,V⟩:=F.sees z; have hp:=Hazel.vacuum A' R'; rw [κ,hk,hp] at H; rw [hk,hp] at V; let w:=A F.zeroG N P M (Bias.vacant0 A') H
 constructor; intro i l; obtain ⟨u,v,g,h⟩:=Y M N g B v A' f (K 2) (refplane z A' X'.tile (F.ideal z) 2) (signed_ref z A' X'.tile (F.ideal z)) H V w i l; refine ⟨u,v,?_⟩; unfold BiasQ; rw [ash_atNode, tileF,hk,hp,F.readK]; exact h
-- coalesce finite family price minima explicit.Mana choose list. keep before H
end Supply
end YM.CF.BPress.Lilac
