import YM.CF.BPress.Primary.Dust
import YM.CF.BPress.Primary.Night
import Mathlib.MeasureTheory.Function.FactorsThrough
/-! Borel extension from standard Borel producers. Avoid needing any claim that image of (Borel) producer, or projection of Pose constraint domains are Borel. This argument includes gauge orbits of all needed data, not a.e. Choose versions *before* using supports again. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree
variable {N:Side}{U:Driver N}{A B C K:Pledge}{F:Scree.GramM N}{g:ℝ}
namespace Extensor
variable {X Y T :Type*} [MeasurableSpace X][m:MeasurableSpace Y][MeasurableSpace T][StandardBorelSpace X][MeasurableSpace.CountablySeparated Y]
open Set
-- disjoint analytic sets specialized to fibers projected by masker
lemma paid (f:X→Y)(v:X→T)(p:Measurable f)(q:Measurable v)(e: ∀ x y,f x=f y→ v x=v y):@Measurable X T (m.comap f) _ v:=by
 intro s h; let Z:=v ⁻¹' s; let W:=f '' Z; have ht: Z=f ⁻¹' W:=by
    ext i; unfold W; simp only [Set.mem_preimage,Set.mem_image]; constructor; · exact fun h=>⟨i,h,rfl⟩
    rintro ⟨j,h,g⟩; change v i∈s; exact e j i g ▸ (show v j∈s from h) -- tune
 haveI : MeasurableSpace.CountablySeparated (Set.range f):= MeasurableSpace.Subtype.countablySeparated; have he: MeasurableSet ((↑) ⁻¹' W : Set (Set.range f)):= p.measurableSet_preimage_iff_preimage_val.mp (ht ▸ (show MeasurableSet Z from q h)); obtain ⟨s',b,l⟩:=he; refine ⟨s',b,?_⟩; refine Eq.trans ?_ ht.symm; ext i; exact Set.ext_iff.mp l (⟨f i, mem_range_self ..⟩:Set.range f)
lemma produces [Nonempty T][StandardBorelSpace T] (f:X→Y)(v:X→T)(p:Measurable f)(q:Measurable v)(e: ∀ x y,f x=f y→ v x=v y): ∃ u:Y→T,Measurable u ∧ v=u ∘ f:= (paid f v p q e).exists_eq_measurable_comp
structure Pack (k:ℝ)(u:Y→ℂ) :Prop where
 cost(x:Y): ‖u x‖≤ k
 meas: Measurable u
-- same for variable threshold
lemma expendV (f:X→ Y)(v:X→ℂ)(c:Y→ℝ)(t:∀i,0≤c i)(r:Measurable c)(p:Measurable f)(q:Measurable v)(e:∀ x,‖v x‖ ≤ c (f x))(h:∀ x y, f x=f y→v x=v y) : ∃ u:Y→ℂ, (∀i,‖u i‖≤c i)∧Measurable u ∧ ∀ x, v x= u (f x):=by
 obtain ⟨u,g,a⟩:= produces f v p q h; let P(i:Y): Prop:= ‖u i‖≤c i; let k(i:Y):=if P i then u i else 0; refine ⟨k,fun i=>?_, Measurable.ite (measurableSet_le g.norm r) g measurable_const,fun i=>?_⟩; · unfold k; split; assumption; simpa only [norm_zero] using t i
 unfold k; have hx:v i=u (f i):= congrFun a i; rw [if_pos (show P (f i) from (show ‖u (f i)‖≤c (f i) from hx ▸ e i)), ←hx] -- tune rewrite hx changes P expansion?
lemma expend (f:X→Y)(v:X→ℂ)(c:ℝ)(t:0≤c)(p:Measurable f)(q:Measurable v)(e:∀ x,‖v x‖ ≤ c)(h:∀ x y, f x=f y→v x=v y):∃ u:Y→ℂ, Pack c u∧∀ x,v x=u (f x):=by obtain ⟨u,p,l,r⟩:=expendV f v (fun _=>c) (fun _=>t) measurable_const p q e h; exact ⟨u,⟨p,l⟩,r⟩
local notation "χ"=> U.Pose
local instance pbM : StandardBorelSpace (Mach (More N)):=by haveI:PolishSpace (Mach (More N)):=inferInstance; infer_instance
private lemma scnt : SecondCountableTopology (Upled SU.Slot):=inferInstance
private lemma lcnt : SecondCountableTopology (Lamp (More N)):=by haveI:= scnt; infer_instance
local instance pbL : MeasurableSpace.CountablySeparated (Plain N):=by
 letI : SecondCountableTopology (Lamp (More N)) := lcnt
 letI : SecondCountableTopology (Plain N):=inferInstance
 letI : BorelSpace (Plain N):=bore_p; letI: OpensMeasurableSpace (Plain N):=@BorelSpace.opensMeasurable _ _ _ (bore_p (N:=N)); letI:MeasurableSpace.CountablyGenerated (Plain N):= BorelSpace.countablyGenerated; letI : MeasurableSingletonClass (Plain N):= ⟨fun x=>(isClosed_singleton (X:=Plain N)).measurableSet⟩; exact MeasurableSpace.countablySeparated_of_separatesPoints
variable (V:U.Wish A B C)(S: Support (More N))(u:U.Pose→ℂ)(p:Measurable u)(t:∀i,‖u i‖≤ g)(v:X→U.Pose)(gV:Measurable v)
structure Extends (B:ℝ)(s:Support (More N))(f:Plain N→ℂ):Prop where
 pay: Pack B f
 local0:∀ x y:Plain N,Along s x y→ f x=f y
 gauge (p: Mach (More N))(x:Plain N): f (τ x p)= f x
abbrev spin_P (π:Mach (More N))(u: Plain N): Plain N:= τ u π
private lemma rot_meas {D G:Type}[MeasurableSpace G][TopologicalSpace G][SecondCountableTopology G][BorelSpace G][MeasurableSpace D][TopologicalSpace D][BorelSpace D]{f:G×D→ D}(p:Continuous f):Measurable (f ∘ Prod.swap):= p.measurable.comp measurable_swap
lemma spin_W : Worker (spin_P (N:=N)):=by
 refine ⟨fun p g x=> τ_ρ ..,?_⟩; have h := ambiance (N:=N); letI : BorelSpace (Plain N):=bore_p; letI : OpensMeasurableSpace (Mach (More N) × Plain N):= by haveI : SecondCountableTopologyEither (Mach (More N)) (Plain N):=⟨Or.inl inferInstance⟩; letI : OpensMeasurableSpace (Plain N):=@BorelSpace.opensMeasurable _ _ _ (bore_p (N:=N)); exact Prod.opensMeasurableSpace
 exact rot_meas h
include p t gV
lemma thick (H: 0≤g)(q:∀ x y:χ, Along S x.val y.val→ u x=u y)(K:∀ p: Mach (More N),∀ x,u (moveW x V p)=u x): ∃ f, Extends g S f∧∀ (x:X) (g: Mach (More N)), let y:=moveW (v x) V g; f y.val=u y:=by
 let w:= Machine.μ_worker V; let f(x:X × Mach (More N)):= moveW (v x.1) V x.2; let S0:= v; let T: χ→Plain N:=fun x=> mask S x.val; have ht:Measurable f := w.meas.comp (f:=fun x:X × Mach (More N)=> (v x.1, x.2)) ((gV.comp measurable_fst).prodMk measurable_snd)
 obtain ⟨Z,r,E⟩:= expend (T ∘ f) (u ∘ f) g H ((mask_meas S|>.comp measurable_subtype_coe).comp ht) (p.comp ht) (fun x=> t (f x)) (fun i j l=> q _ _ ((mask_iff ..).1 l)); let g':Plain N→ℂ:=fun x=> Z (mask S x); have h:Measurable g':= r.meas.comp (mask_meas _); let G:= spin_W (N:=N); have hh(i):‖g' i‖≤g:=r.cost _; refine ⟨average spin_P g',⟨⟨G.price_A _ h hh, G.meas_A _ h hh⟩,fun x y l=> G.align _ _ _ (fun i=> congrArg Z (maskEq S _ _ (l.move i))), fun p i=> G.move_avg _ h hh p i⟩,?_⟩
 intro x g; let Y:=moveW (v x) V g; have ht(p:Mach (More N)): g' (spin_P p Y.val)= u Y:=by
    have hp: (moveW Y V p)= f (x,p*g):= pose_seq ..; rw [show spin_P p Y.val=(f (x,p*g)).val from congrArg Subtype.val hp]; exact (E (x,p*g)).symm.trans (by rw [Function.comp_apply,←hp,K]) -- tune needs congrArg before E
 change (∫ p:Mach (More N),g' (spin_P p Y.val)∂machines (More N)) = u Y; simp_rw [ht]; simp
end Extensor
end YM.CF.BPress.Primary
