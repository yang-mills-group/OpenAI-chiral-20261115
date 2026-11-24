import YM.SU5.Reconstruction.Based.Routes
import YM.SU5.FiniteGaugeData.Tapestry.Neutral

set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
noncomputable def fromRoot(x:Cover)(U:LinksC):SU.E:= travel U (R.base x) (R.path x)
/-- Obtain the SU holonomies for ALL edges in S, second uses one auxiliary link read,
only in `wide`. Values on edges outside S arbitrary (anchor/path functions total).
Neither arg is a gauge-fixed law. -/
noncomputable def collect(U V:LinksC) : LinksC := gauge (fun x=> fromRoot R x U) V
noncomputable def loopData (U:PairsC) : PairsC := (collect R U.1 U.1, collect R U.1 U.2)
noncomputable def ask(f:PairsC→ℂ) : PairsC→ℂ := f ∘ loopData R
noncomputable def circuitWalk(x:Cover)(i:Axis): Walk := R.path x ++ posDir i :: reverse (R.path (x+step i))

variable (i:Axis)(x:Cover)(h:x∈S)(k:x+step i∈ S)
include h k
lemma circuit_in : Joins S (R.base x) (R.base x) (circuitWalk R x i):=by
 let y:Cover:= x+step i; let h':Joins S y (R.base x) (Lattice.reverse (R.path y)) := (R.edge x i h k).symm ▸ (R.toSite y k).turn
 exact (R.toSite x h).paste (Joins.cons h (posDir i) h')
lemma circuit_value (U:LinksC): travel U (R.base x) (circuitWalk R x i)=collect R U U (x,i):=by
 unfold circuitWalk; rw [travel_append,(show stop (R.base x) _= x from (R.toSite x h).1)]; let y:= x+step i; let a:= R.path y; let r:= R.base y; have he:travel U y (Lattice.reverse a)= (travel U r a)⁻¹:=
    (congrArg (travel U · (Lattice.reverse a)) (R.toSite y k).1.symm).trans (travel_reverse ..)
 change fromRoot R x U * (U (x,i)*travel U y (Lattice.reverse a))= (fromRoot R x U * U (x,i))*(fromRoot R y U)⁻¹
 rw [he, mul_assoc]; rfl
lemma auxiliary_circuit_value (U V:LinksC): travel U (R.base x) (R.path x)*V (x,i)*travel U (x+step i) (Lattice.reverse (R.path (x+step i)))=collect R U V (x,i):= by
 let y:= x+step i; let a:= R.path y; let r:= R.base y; have he:travel U y (Lattice.reverse a)= (travel U r a)⁻¹:=
    (congrArg (travel U · (Lattice.reverse a)) (R.toSite y k).1.symm).trans (travel_reverse ..)
 change _ * travel U y (Lattice.reverse a)= (fromRoot R x U * _)*(fromRoot R y U)⁻¹; rw [he]; rfl
omit k h
variable {x}
lemma route_local (h:x∈S): LocalOn (S:Set _) (fromRoot R x):= fun A B u=> travel_local _ _ A B (fun i hx hy=> u i ((R.toSite x h).2 _ hx) ((R.toSite x h).2 _ hy))
lemma collect_support {U V U' V':LinksC}(a:Agrees S U U')(b: Agrees S V V') : Agrees S (collect R U V) (collect R U' V') :=by
 intro i hx hy; unfold collect Lattice.gauge; dsimp only; rw [route_local R hx _ _ a,route_local R hy _ _ a,b _ hx hy]
@[fun_prop] lemma fromRoot_cont(x:Cover): Continuous (fromRoot R x):= continuous_travel ..
@[fun_prop] lemma collect_cont : Continuous (fun z:PairsC=> collect R z.1 z.2):=by
 apply continuous_pi; intro e; unfold collect Lattice.gauge; fun_prop
@[fun_prop] lemma loops_cont : Continuous (loopData R) := by
 refine (collect_cont R|>.comp (continuous_fst.prodMk (continuous_fst (X:=LinksC) (Y:=LinksC)))).prodMk (collect_cont R)
lemma certified {wide:Bool}{f:PairsC→ℂ}(p:Coeff wide S f): Coeff wide S (ask R f):=
 ⟨fun e=>by
    obtain ⟨g,a,rfl⟩:=p.narrow e
    exact ⟨fun X=>g (collect R X X), a.comp (f:=fun x=> collect R x x) (show Continuous (fun x=> collect R x x) from (collect_cont R).comp (f:=fun x=>(x,x)) (continuous_id.prodMk continuous_id)), rfl⟩,
 Env.along p.env (loops_cont R).measurable,fun x y p' q=> p.locus _ _ (collect_support R p' p') (collect_support R p' q)⟩

/-- for ACTUAL powers in that cell, change gauge at end with inverse (cover), even if torus
winds in many directions. Closed loops only conjugate by root. -/
lemma turning (U:LinksC)(t:Cover→ SU.E)(h:x∈ S): fromRoot R x (gauge t U)= t (R.base x)*fromRoot R x U*(t x)⁻¹:=
  (travel_gauge ..).trans (by rw [(R.toSite x h).1]; rfl)
lemma turning_circuit (U V:LinksC)(t:Cover→ SU.E)(e:Edge Cover)(h:e.1∈ S)(k:e.1+step e.2 ∈ S) : collect R (gauge t U) (gauge t V) e=t (R.base e.1)*collect R U V e*(t (R.base e.1))⁻¹:=by
 change fromRoot _ _ _*gauge _ _ e*(fromRoot _ _ _)⁻¹=t (R.base _)*(fromRoot _ _ _*_*_) *_
 rw [turning R U t h,turning R U t k,← R.edge _ _ h k]; unfold Lattice.gauge; group
end YM.CF.Buffered.Afterglow.Rooted
