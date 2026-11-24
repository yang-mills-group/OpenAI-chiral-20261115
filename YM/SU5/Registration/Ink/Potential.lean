import YM.SU5.Registration.Ink.Midnight
import YM.Work.C25
/-!
 # Even (observable) field-symbols over contour price

 Don't create operators from abstract Wightman envelopes (without identification diagrams
 at these same points in the original Hilbert space). Work always over M5 domain in
 time-energy. Crossing through all t strictly ordered, W-kernel identification via unpadding.
 In particular its W-kernel positive on all W from the contour. No cone purchase yet.
 Inspiration YM/Fields/System, Next/BOUNDARY. Does not assert locality yet!
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Filter Function Set MeasureTheory Spectral Mink Boundary Boundary.Small OS Complex OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin SatinRegistration
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}{V : Type*} [AddCommGroup V] [Module ℂ V] {n:ℕ}
variable (B: Carton S V)
-- normalized surface, same test word calculus
noncomputable def WView.expect (W:WView V)(Q:MarkWords V) : ℂ:= W.W Q.length (fun i=> (Q.get i).1) (Joint.materialize Q.length (fun i=> (Q.get i).2))
abbrev JMap (V : Type*) [AddCommGroup V][Module ℂ V]:= V →ₛₗ[starRingEnd ℂ] V
variable (J:JMap V)
noncomputable abbrev opTag (p:MarkType V) : MarkType V:= (J p.1, Probe.bar p.2)
noncomputable def wordRev (v: MarkWords V): MarkWords V:= List.reverse (v.map (opTag J))
def WView.kernel (W:WView V)(J:JMap V) (u v:MarkWords V):= W.expect (wordRev J u ++ v)
structure Remembers : Prop where
 both : Involutive J
 bill (p:ℝ≥0) (v): B.bar p (J v)= (B.bar p v).adjoint
-- argument p=0 allowed but irrelevant
namespace Carton
local notation "T"=> S.E
local notation "D"=> radial S
local notation "ρ"=> (𝓝[>] (0:ℝ≥0))
variable (z: Remembers B J)
lemma watches (v:V)(x:D)(f:Test4): Tendsto (fun p=> valise S (B.bar p v) f x.1) ρ (𝓝 (B.black v f x).1):=by
 have h:= B.blue_finish v f ρ id tendsto_id (show (bands S).Approaches ρ (fun _=>x) x from fun k=>by simp only [sub_self,Grading.budget,Grading.due,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds); simp_rw [← blue_apply]; exact Grading.Approaches.hilbert _ h
lemma invoice_add (v w:V)(f:Test4) : B.black (v+w) f= B.black v f+B.black w f:=by
 ext1 x; apply Subtype.ext;
 refine tendsto_nhds_unique_of_eventuallyEq (B.watches _ x f) ((B.watches v x f).add (B.watches w x f)) ?_
 simp only [map_add,vadd,ContinuousLinearMap.add_apply]; rfl
lemma invoice_smul (v:V)(c:ℂ)(f:Test4): B.black (c • v) f=c • B.black v f:=by
 ext1 x; apply Subtype.ext; refine tendsto_nhds_unique_of_eventuallyEq (B.watches _ x f) ((B.watches v x f).const_smul c) (?_); simp only [map_smul,vscale,ContinuousLinearMap.smul_apply]; rfl
noncomputable def operator : V →ₗ[ℂ] Test4 →ₗ[ℂ] (D→ₗ[ℂ] D):=
 { toFun := fun v=> SatinRegistration.field S _ (B.coherent v) (B.price v)
   map_add' u v:= by ext1 f; exact B.invoice_add ..
   map_smul' t v:= by ext1 f; exact B.invoice_smul .. }
lemma black_eq (v:V)(f:Test4):B.operator v f=B.black v f:=rfl
lemma black_con (v:V)(x:D): Continuous (fun f=> (B.operator v f x).val):= field_distribution S _ (B.coherent v) (B.price v) x
include z
lemma black_adjoint (v:V)(f:Test4): SatinRegistration.adj S _ (B.coherent v) (B.price v) f=B.black (J v) f:=by
 have he: (fun p:ℝ≥0 => B.bar p (J v)) = fun p => (B.bar p v).adjoint := funext fun x=> z.bill x v
 unfold SatinRegistration.adj black; congr 2; -- can use `congr`, automation
 exact he.symm
lemma sharp (t:MarkType V)(x y:D): inner ℂ (B.activate t x).1 y.1=inner ℂ x.1 (B.activate (opTag J t) y).1 :=by
 change inner ℂ (SatinRegistration.field S _ (B.coherent t.1) _ _ x).1 y.1= _
 rw [field_adjoint]; exact congrArg (fun (A': D→ₗ[ℂ] D)=> inner ℂ x.1 (A' y).1) (B.black_adjoint J z t.1 (Probe.bar t.2))
omit z
lemma row_picks (t:MarkType V)(L:MarkWords V): B.row (t::L)=B.activate t (B.row L):=rfl
end Carton
lemma WView.expect_ofFn (W:WView V)(v:Fin n→MarkType V): W.expect (List.ofFn v)= W.W n (fun i=>(v i).1) (Joint.materialize n (fun i=>(v i).2)):=by
  have key (b : MarkWords V) (k : ℕ) (h : b.length = k) (v : Fin k → MarkType V)
      (he : ∀ i, b.get i = v (Fin.cast h i)) :
      W.expect b = W.W k (fun i => (v i).1) (Joint.materialize k fun i => (v i).2) := by
    subst k; simp only [expect, he, Fin.cast_refl, id_eq]
  exact key _ _ (by simp) v (List.get_ofFn _)

structure InkPort (F: InkWaves V)(W:WView V): Prop where
 region : F.Region
 strict_mat : B.Defined F
 gap_cost : F.Breathes
 weighted : F.Bounds
 lines : F.Lines
 path : F.Along
 shores (n : ℕ) (y:Heights n)(u:y∈ sunrise n) :
   ∃ Z:MultilinearMap ℂ (fun _:Fin n=>V) (Distn (Points n)), ∀ v f, Tendsto (fun t=> F.psi v t f) (𝓝[east n] y) (𝓝 (Z v f))
 level : F.NonTangentialFree W
 looks : F.during W
 half_price : W.cone_tests

variable (F:InkWaves V)(W:WView V)
lemma InkPort.supply (p:B.Defined F)(u:F.NonTangentialFree W) : InkPort B F W:=by
 let v:=B.defined_power p; let r:=B.defined_region p; let h:= InkWaves.bounds r v; let t:=InkWaves.along r v; let q:=InkWaves.lines r v; let z:= F.clock_appointed W v q t u; exact ⟨r, p,v,h,q,t, fun _ _=> F.seeks h t q v _,u,z,F.shiny_half W v z h⟩
lemma InkPort.obtainF : ∃ F:InkWaves V,∃ W:WView V,InkPort B F W:=by
 obtain ⟨F,p⟩:= B.defined_exists; let v:=B.defined_power p; let r:=B.defined_region p; let t:= InkWaves.bounds r v; obtain ⟨W,h⟩:=F.jointly t (InkWaves.along r v) (InkWaves.lines r v) v; exact ⟨F,W,supply B F W p h⟩

variable {B F W}
namespace InkPort
variable (p:InkPort B F W)
include p
lemma tensor (v:Fin n→V)(f:Fin n→Test4) : W.W n v (Joint.materialize n f)=inner ℂ B.omega (B.row (List.ofFn (fun i=>(v i,f i)))).1:= B.reality_tensor v f p.strict_mat p.level
lemma real_value (Q:MarkWords V): W.expect Q= inner ℂ B.omega (B.row Q).1:= by
 have he := tensor p (fun i=>(Q.get i).1) (fun i=>(Q.get i).2); have ht:(fun i=>( (Q.get i).1,(Q.get i).2))=Q.get:= rfl
 rw [ht,List.ofFn_get] at he; exact he
lemma reference_eq {P:InkWaves V} {K:WView V}(h: InkPort B P K) :
  (∀ n (x:SpacePoints n) (z:Times n), z∈strict n→ F.F n z x=P.F n z x) ∧ W=K:= by
 refine ⟨fun n x z t=> ?_,?_⟩
 · obtain ⟨d,u⟩:= Work.C03.exists_lit t; ext1 v; exact (p.strict_mat n z t d u x v).trans (h.strict_mat n z t d u x v).symm
 suffices W.W=K.W by cases W; cases K; congr
 funext n; ext1 v; apply ContinuousLinearMap.ext_on (R₁:=ℂ) (s:= Set.range (Joint.materialize n))
 · intro x; change x∈(Submodule.span ℂ (Set.range (Joint.materialize n))).topologicalClosure; rw [Work.C25.answer n]; exact Submodule.mem_top
 rintro f ⟨a,rfl⟩; exact (p.tensor v a).trans (h.tensor v a).symm
lemma real_pair (p0:Remembers B J)(A C:MarkWords V): W.kernel J A C= inner ℂ (B.row A).1 (B.row C).1:=by
 induction A generalizing C with
 | nil=> exact p.real_value C
 | cons t A ih=>
   rw [B.row_picks, B.sharp J p0]; rw [← B.row_picks];
   refine Eq.trans ?_ (ih (opTag J t::C)); simp [WView.kernel, wordRev]
lemma true_pos (p0:Remembers B J): Analysis.NNKernel (W.kernel J) := by
 have h: W.kernel J= fun i j=> inner ℂ (B.row i).1 (B.row j).1:=funext fun i=> funext fun j=> p.real_pair J p0 i j
 rw [h]; exact Fields.hilbertNonnegative H (fun i=> (B.row i).1)
end InkPort
end YM.SatinWFixed
