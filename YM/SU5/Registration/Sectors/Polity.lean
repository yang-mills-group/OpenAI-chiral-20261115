import YM.SU5.Registration.Sectors.Panoramic
/-
 # One dense algebraic domain on the actual projected sector.
 Don't need to assume full reconstruction for future comparison work.
 Inspiration `YM/Fields/System, Next/BOUNDARY/Core`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Filter MeasureTheory Measure Set Complex Submodule SatinRegistration
open Boundary Probe Mink Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet Analysis
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H: Hilbert}{S: OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
local notation "D"=> radial S
local notation "T"=> S.E
variable (B:Carton S V)
local notation "Q"=> B.pointShelf
local notation "R"=> B.station
namespace Carton
noncomputable abbrev engaged (p:MarkWords V): B.station:= ⟨(B.row p).val,B.writes p⟩ -- field notation
noncomputable def citizen : Submodule ℂ B.station:= Submodule.span ℂ (Set.range B.engaged)
local notation "F'"=> B.citizen
private lemma allspan : (F').map (Q).subtype=B.inH:=by
 unfold citizen; rw [Submodule.map_span,B.true_words,← Set.range_comp]; rfl
lemma castspan (x:R): x∈B.citizen ↔ x.1∈ B.inH:=by
 rw [← allspan B]; exact ⟨fun p=>mem_map_of_mem p,fun ⟨a,p,h⟩=> (Subtype.ext h : a=x) ▸ p⟩
lemma populous : Dense (B.citizen:Set B.station):=by
 intro x
 -- closure in subtype. use metric.
 apply Metric.mem_closure_iff.mpr; intro ε h
 obtain ⟨p,v,e⟩:= Metric.mem_closure_iff.mp (show x.val ∈ _root_.closure (B.inH:Set H) from x.prop) ε h
 exact ⟨⟨p,B.inH.le_topologicalClosure v⟩,(B.castspan _).2 v,e⟩
lemma printed (x:H)(p:x∈ B.inH): x∈ D:=by obtain ⟨a,g,rfl⟩:=p; exact a.prop
noncomputable def live : B.citizen →ₗ[ℂ] radial S := {
 toFun x:= ⟨x.val.val,B.printed x.val.val ((B.castspan _).1 x.prop)⟩
 map_add' a b:=rfl
 map_smul' c a:=rfl }
@[simp] lemma live_cast (x:B.citizen): (B.live x).val=x.val.val:=rfl
lemma lives (x:B.citizen): B.live x∈B.words:=by
 let h:= (B.castspan _).1 x.prop; obtain ⟨a,p,k⟩:=h; exact (Subtype.ext k : a=B.live x) ▸ p
noncomputable def owns (x:D)(h:x∈B.words): B.citizen:=
  ⟨⟨x.val,B.inH.le_topologicalClosure (mem_map_of_mem h)⟩,(B.castspan _).2 (mem_map_of_mem h)⟩
lemma cast_after (x:B.citizen): B.owns (B.live x) (B.lives x)=x:=rfl
lemma live_after (x:D)(p:x∈B.words): B.live (B.owns x p)=x:=rfl
lemma alive : Injective B.live:=fun _ _ h=> Subtype.ext (Subtype.ext (congrArg (fun x : D => x.val) h))
-- all fields back on projected system but with THIS linear algebra domain
noncomputable def oneOp (t:MarkType V) : (F')→ₗ[ℂ] (F'):= {
 toFun x:= B.owns (B.activate t (B.live x)) (B.written t (B.live x) (B.lives x))
 map_add' x y:= by apply Subtype.ext; apply Subtype.ext; simp only [map_add]; rfl -- dependent '_mem'
 map_smul' c x:= by apply Subtype.ext; apply Subtype.ext; simp only [map_smul]; rfl }
@[simp] lemma issued (t:MarkType V)(x:B.citizen): B.live (B.oneOp t x) = B.activate t (B.live x):=rfl
noncomputable def pointMap: V →ₗ[ℂ] Test4 →ₗ[ℂ] ((F')→ₗ[ℂ](F')):= {
 toFun t:= {
   toFun f:= B.oneOp (t,f)
   map_add' f g:= by ext1 x; apply B.alive; rw [LinearMap.add_apply,map_add,issued, issued, issued]; exact DFunLike.congr_fun (map_add (B.operator t) f g) _
   map_smul' c f:=by ext1 x; apply B.alive; rw [LinearMap.smul_apply,map_smul, issued,issued]; exact DFunLike.congr_fun (map_smul (B.operator t) c f) _ }
 map_add' t v:= by ext1 f; ext1 x; apply B.alive; change B.live (B.oneOp (t+v,f) x)=B.live (B.oneOp (t,f) x+B.oneOp (v,f) x); rw [map_add,issued,issued,issued]; exact DFunLike.congr_fun (DFunLike.congr_fun (map_add B.operator t v) f) (B.live x)
 map_smul' c t:=by ext1 f; ext1 x; apply B.alive; change B.live (B.oneOp (c • t, f) x)= B.live (c • B.oneOp (t,f) x); rw [map_smul,issued,issued]; exact DFunLike.congr_fun (DFunLike.congr_fun (map_smul B.operator c t) f) (B.live x) }
noncomputable def evaluate (p:MarkWords V) : B.citizen:= ⟨B.engaged p,Submodule.subset_span (mem_range_self _)⟩
lemma eval (v:V)(f:Test4)(p:MarkWords V): B.evaluate ((v,f)::p) = B.pointMap v f (B.evaluate p):= rfl
lemma outputs (x:B.citizen)(t:V) : Continuous (fun f=> (B.pointMap t f x).1):= Continuous.subtype_mk (B.black_con t (B.live x)) _ -- map point reduces.
noncomputable def read (v:V)(f:Test4): R →ₗ.[ℂ] R:= ⟨F', B.citizen.subtype.comp (B.pointMap v f)⟩
def exportTime (u:E4)(x:B.citizen):B.citizen:= B.owns (SatinRegistration.shift S u (B.live x)) (B.shift_write u (B.live x) (B.lives x))
lemma passport (u:E4)(x:B.citizen): (B.exportTime u x).1=B.joinT.translation u x.val:= rfl
lemma transport_t (u:E4)(t:V)(f:Test4)(x:B.citizen): B.exportTime u (B.pointMap t f x)= B.pointMap t (ahead u f) (B.exportTime u x):= B.alive (SatinRegistration.field_translate S _ (B.coherent t) (B.price t) f u (B.live x))
variable (J:JMap V)(z: Remembers B J)
include z
lemma FormalSharp (t:MarkType V): (B.read t.1 t.2).IsFormalAdjoint (B.read (J t.1) (Probe.bar t.2)) := fun x y=> B.sharp J z t (B.live x) (B.live y)
lemma meets_adj (t:MarkType V) : B.read (J t.1) (Probe.bar t.2) ≤ (B.read t.1 t.2).adjoint:= LinearPMap.IsFormalAdjoint.le_adjoint B.populous (B.FormalSharp J z t)
lemma closedRead (v:V)(f:Test4): (B.read v f).IsClosable:= by
 let Y:=B.read (J v) (Probe.bar f); have hh:Dense (Y.domain : Set B.station):= B.populous; exact (LinearPMap.adjoint_isClosed hh).isClosable.leIsClosable ((B.FormalSharp J z (v,f)).symm.le_adjoint hh)
omit z
variable (F: InkWaves V)(W: WView V)(u:InkPort B F W)
include u
lemma literal_price(p:MarkWords V):W.expect p= inner ℂ (B.engaged []) (B.evaluate p).val:= u.real_value p
lemma literal_gram (z:Remembers B J)(i j : MarkWords V): W.kernel J i j=inner ℂ (B.evaluate i).val (B.evaluate j).val:= u.real_pair J z i j
omit u
lemma norm_root : ‖B.engaged []‖=1:= B.size
lemma at_rest (t:E4) : B.joinT.translation t (B.engaged []) = B.engaged []:= Subtype.ext (B.stay t)
lemma along_t (u:E4)(q:MarkWords V): B.joinT.translation u (B.engaged q)= B.engaged (q.map (euSlide u)):= Subtype.ext (congrArg (fun x : D=> x.val) (B.shifted_row u q))
end Carton
end YM.SatinWFixed
