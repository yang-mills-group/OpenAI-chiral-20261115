import WakeRoad.Amberjack
/-! # Oriented comparisons and deck legality. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Buffered Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Skye Precision Tree Fock
attribute [local instance] opCStarAlgebra
open PhysicalNext.JointLoad.Heir
open YM.WakeRoad CF.Pannier.Chancel Rous Pressure Papal EmberWind Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open CF.Gingham.Ruff
local notation "G₅"=> SU.group
open CF.Gingham.Ruff
namespace ArborJet
variable {N:Side}{m d s:ℕ}{S:Support (More N)}
local notation "M"=> Signed.mirror (3:Axis)
local notation "Z" w:max=> Lattice.wrap (More N) (2 • ((w:ℤ) • Lattice.step (3:Axis)))
local notation "T" w:max=> affine (Signed.mirror (3:Axis)) (Z w)
local notation "t*"=> (3:Axis)
local notation "o₀"=> bouton (0:Site N)
variable (w:ℤ)(b:Bool)
def attire : Pane N → Pane N:= if b then fling 3 w N else fun x=>x
abbrev encasing (S:Support (More N)) : Support (More N):= if b then S.image (T w) else S
lemma centered (p:ℕ): encasing w b (BlockP p (0:Seat N)) = BlockP p (homebase w b):=by
 cases b; · rfl
 change (halo p {0}).image (T w)= halo p {Z w}
 rw [← Tye.dignify,image_singleton,turf]
lemma tiny_mono {r:ℝ}{V:Pane N}{S':Support (More N)}(v:Tiny S V r)(t:S'⊆S) : Tiny S' V r:= fun i x y=> v i (t x) (t y)
lemma outfit {U:Pane N}{α t:ℝ}(h:Tiny (encasing w b S) U t)(q:ordinary (possession (n:=N) (encasing w b S)) α U): Tiny S (attire w b U) t ∧ ordinary (possession (n:=N) S) α (attire w b U):=by
 cases b; · exact ⟨h,q⟩
 unfold attire; rw [if_pos rfl,fling_eq]; exact ⟨tugTiny U M _ h,tugSmall U M _ q⟩

abbrev stamp (i:Postcard m):ℝ:= if b then frigid (anis m i) else (1:ℝ)
abbrev going(m:ℕ):=BlockP (m+debt+12) (homebase (N:=N) w b)
lemma cleared (h: m+2≤d) (q:going w b d (N:=N)⊆ S)(j:Postcard m):BlockP (debt+4) (taking m w b j) ⊆ S:=by
 intro i t; apply q; rw [blocks_test] at * -- expands going?
 have H:= separation_triangle (homebase (N:=N) w b) (taking m w b j) i
 have e:=estate (N:=N) m w b j; omega
lemma signature (h: m+2 ≤ d) (q:going w b d (N:=N)⊆ S) (p:debt ≤ s): (elector m w b (N:=N)).Ship S s:= wood _ p (fun _=>cleared w b h q _)
lemma passage {F:Support (More N)} (p:Lattice.halo 8 F ⊆ S) {x:Pane N}{α t:ℝ}(q:ordinary (possession (n:=N) S) α x)(a:α<t): pingS t F x:=by
 intro i p'; obtain ⟨z,h,g⟩ := not_disjoint_iff.mp p'
 refine (q i (mem_filter.mpr ⟨mem_univ _,fun j k=>p (halo_spec.mpr ⟨z,h,?_⟩)⟩)).trans_lt a
 have hz:= Work.E01.sep_touched i j k; have h':= Work.E01.sep_touched i z g
 have t':= separation_triangle z i.1 j; rw [separation_comm z i.1] at t'; omega -- rewrite applies lhs too
lemma attiring {U:Pane N}{t α:ℝ}(h:Tiny S U t)(q:ordinary (possession (n:=N) S) α U)(ℓ:going w b d⊆ S)(p:m+2≤d)(j:Postcard m):
 let V:=elector m w b (N:=N); let A:=SU.group.curvature (faceValue U (V.ua j));
 ‖A‖ ≤ α ∧ |fault (N:=N) m (0:Seat N) (attire w b U) j - stamp b j * A (V.lens j)| ≤ 2* SU.group.colorScale * t * α:=by
 -- notation .curvature on G
 intro F A
 let x:=birthplace m j (N:=N); let s0:=anis m j; let z:=town w x s0
 let v₀:=taking m w b (N:=N) j
 have e:v₀∈ S:=cleared w b p ℓ j (blocks_test.mpr (by rw [separation_self]; omega))
 have e1(i:Axis): v₀+step i∈ S:= cleared w b p ℓ j (blocks_test.mpr ((Work.E01.sep_step_le ..).trans (by omega)))
 have ey(i)(t:i∈touched (F.ua j)): i∈S:=cleared w b p ℓ j (blocks_test.mpr ((Work.E01.sep_touched (F.ua j) _ t).trans (by omega)))
 have H: ‖A‖ ≤ α:=(Gauge.curvature_norm ..).trans (q _ (mem_filter.mpr ⟨mem_univ _,ey⟩))
 have ht:0≤t:= (SU.group.chord_nonneg _).trans (h (v₀,t*) e (e1 t*))
 have hv:= (norm_nonneg _).trans H; have hg:=SU.group.colorScale_pos
 refine ⟨H,?_⟩
 -- cases b: false. general conversion planeFace
 rcases hb: b with - | -
 · unfold A F fault attire stamp -- V not actual F var
   subst b; simp [elector,taking,Boom.port,birthplace,anis]; positivity
 have hz:v₀=z:=by simp [v₀,taking,hb,z,s0,x]
 have t0: SU.group.chord (U (z,t*)) ≤ t:=hz ▸ (show SU.group.chord (U (v₀,t*)) ≤ t from h _ e (e1 t*))
 have t1:=planeFace U w x s0; let k:=U (z,t*)
 have hx: Boom.port (0:Seat N) j.1.1.val=x:=by simp [Boom.port,x,birthplace]
 have ha:A= SU.group.curvature (faceValue U (z,s0)):=by change SU.group.curvature (faceValue U (v₀,s0))= _;rw [hz]
 change |(SU.group.curvature (faceValue (fling t* w _ U) (Boom.port (0:Seat N) j.1.1.val,s0))) j.2 - (frigid s0:ℝ)*A j.2| ≤ _
 rw [hx,fling_eq,t1]; unfold frigid; by_cases v:s0.val.2=t*; swap; · rw [if_neg v,if_neg v, ←ha]; simp; positivity
 rw [if_pos v,if_pos v,Int.cast_neg,Int.cast_one]; change |(SU.group.curvature (k⁻¹ * (faceValue U (z,s0))⁻¹ * k)) j.2-(-1:ℝ) * A j.2| ≤ _
 rw [show k⁻¹*(faceValue U (z,s0))⁻¹*k=k⁻¹*(faceValue U (z,s0))⁻¹*(k⁻¹)⁻¹ by rw [inv_inv], Gauge.curvature_conjugate, Gauge.curvature_inv, ←ha, neg_one_mul]
 let X':= SU.group.adjoint k⁻¹ (-A) - (-A)
 have he : (SU.group.adjoint k⁻¹ (-A)) j.2- - A j.2=X' j.2:=rfl; rw [he]
 exact (PiLp.norm_apply_le (p:=2) X' j.2).trans ((Next.Fluctuations.adjoint_norm_sub ..).trans (by rw [Gauge.chord_inv,norm_neg]; gcongr))
#print axioms attiring
