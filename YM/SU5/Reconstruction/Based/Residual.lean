import YM.SU5.Reconstruction.Based.Dressed
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
/-! # suffices to budget only global rotations at each Root. Dressed probes
 already compatible with different purchases to reach them; works at ANY moment. -/
variable (K:Calibration){m:Side}
variable {x:Cover}{i:SpinIdx}{a:SU.Slot}
-- on wrap via path into TRUE component roles
lemma wrappedGauge {n:Side}(U:Pane n)(g:Seat n→SU.E) : onC n (gauge g U)= gauge (g ∘ wrap (More n)) (onC n U):=by
 ext e:1; rcases e with ⟨x,i⟩; rw [onC_spec]; unfold Lattice.gauge; simp only [comp_apply,map_add,wrap_step,onC_spec]

def RootTrivial {n:Side}(g:Seat n→ SU.E):Prop:= ∀ x∈ S,g (wrap (More n) (R.base x))=1
lemma route_changed {n:Side}(g:Seat n→ SU.E) (t:RootTrivial R g)(x:Cover)(h:x∈S)(U:Pane n): fromRoot R x (onC n (gauge g U))=fromRoot R x (onC n U)*(g (wrap (More n) x))⁻¹ := by rw [wrappedGauge,Rooted.turning R _ _ h,comp_apply, t x h,one_mul]; rfl
lemma circuit_agrees {n:Side} (g:Seat n→ SU.E)(t:RootTrivial R g)(U V: Pane n): Agrees S (collect R (onC n (gauge g U)) (onC n (gauge g V))) (collect R (onC n U) (onC n V)) := by
 intro e h u; rw [wrappedGauge,wrappedGauge,turning_circuit R _ _ _ e h u,comp_apply, t e.1 h,inv_one,one_mul,mul_one]
lemma priceBasis (n:Side) (x:Cover)(i:SpinIdx)(b:SU.Slot)(U : LinksC)(g:Seat n→ SU.E)(h:g (wrap (More n) (nodeC x))=(fromRoot R (nodeC x) U)⁻¹) : rootBasis R n x i b U = acts (tradew n g).val (basisC n x i b):= by
 rw [Tapestry.turn_basisC,h]; rfl
lemma readyBasis {n:Side} {x:Cover} {i:SpinIdx}{a:SU.Slot}(p:nodeC x∈ S)(U:Pane n)(g:Seat n→ SU.E)(t:RootTrivial R g):
    rootBasis R n x i a (onC n (gauge g U))= acts (tradew n g).val (rootBasis R n x i a (onC n U)) := by
 let F:Seat n→SU.E := fun _=> (fromRoot R (nodeC x) (onC n U))⁻¹
 let k := nodeC x
 have ht:(g*F) (wrap (More n) k)=(fromRoot R k (onC n (gauge g U)))⁻¹ := by rw [Pi.mul_apply,route_changed R g t k p U,mul_inv_rev,inv_inv]
 rw [priceBasis R n x i a _ (g*F) ht, priceBasis R n x i a _ F rfl,← Hive.trade_c F g, ← act_mul]; rfl

def BeforeRoots (f: Family K):Prop:=∀ (m:Side)(g:Seat (K.c m)→ SU.E), RootTrivial R g → Tapestry.Harmony g (f m) (f m)
namespace BeforeRoots
lemma creation (x:Cover)(u:nodeC x∈ S)(i:SpinIdx)(a:SU.Slot):BeforeRoots R K (rootCreate R K x i a):=fun m g t V=> by rw [rootCreate_apply,rootCreate_apply,twist_create]; exact congrArg create (readyBasis R u V.1 g t)
lemma removal (x:Cover)(u:nodeC x∈ S)(i:SpinIdx)(a:SU.Slot): BeforeRoots R K (rootRemove R K x i a):= fun m g t V=>by rw [rootRemove_apply,rootRemove_apply,twist_remove]; exact congrArg Fock.remove (readyBasis R u V.1 g t)
lemma loop {wide:Bool} {f:PairsC→ℂ} (p:Coeff wide S f): BeforeRoots R K (scalar K (ask R f)):= by
 intro m g t V; unfold scalar; rw [twist_scalar,map_one]; exact congrArg (fun z:ℂ=>z•(1:FC _)) (p.locus _ _ (circuit_agrees R g t V.1 V.1) (circuit_agrees R g t V.1 V.2)) -- ; tunes
lemma zero : BeforeRoots R K 0:= fun _ _ _ _=> (map_zero _).symm
lemma one : BeforeRoots R K 1:= fun _ _ _ _=> (map_one _).symm
variable {R K} {f h: Family K}
lemma mul (p:BeforeRoots R K f)(q:BeforeRoots R K h): BeforeRoots R K (f*h):= fun m g t v=> by simp only [Pi.mul_apply,map_mul,p m g t v,q m g t v]
lemma add (p:BeforeRoots R K f)(q:BeforeRoots R K h): BeforeRoots R K (f+h):= fun m g t v=> by simp only [Pi.add_apply,map_add,p m g t v,q m g t v]
lemma scale (z:ℂ)(p:BeforeRoots R K f): BeforeRoots R K (z• f):= fun m g t v=> by simp only [Pi.smul_apply,twist_scalar,p m g t v]
end BeforeRoots

def RootsChecked (f:Family K)(m : Side) := ∀ (g:Seat (K.c m)→ SU.E), (∀ x∈ S, g (wrap (More (K.c m)) x)=g (wrap (More (K.c m)) (R.base x))) → Tapestry.Harmony g (f m) (f m)
lemma harmonyBoth {N:Side}{x:Mark N} (t g: Seat N → SU.E)(p:Tapestry.Harmony t x x)(h:Tapestry.Harmony g x x): Tapestry.Harmony (t*g) x x:=by
 intro u; rw [show simultaneous (t*g) u= simultaneous t (simultaneous g u) from Prod.ext (gauge_sq u.1 t g).symm (gauge_sq u.2 t g).symm,p,h]
 rw [← Hive.trade_c, show quantU (tradew N t * tradew N g)=quantU (tradew N t)* quantU (tradew N g) from Subtype.ext (quant_mul ..),Fock.twin]
lemma roots_warrant {f:Family K}(p:BeforeRoots R K f)(t:RootsChecked R K f m)(u:Hosp S (K.c m)): covariant (f m):=by
 intro g; let n:=K.c m; let W(x):=g (wrap (More n) (R.base x))
 obtain ⟨v,h⟩:=scoreTrace W u; let y:=g*v⁻¹
 have h₂:RootTrivial R y:= fun x hx => by rw [show y _=_ from Pi.mul_apply ..,Pi.inv_apply,h _ (R.base_mem x hx)]; unfold W; rw [R.stays _ hx,mul_inv_cancel]
 have h₁:Tapestry.Harmony v (f m) (f m):= t v (fun x hx=> (by rw [h x hx,h _ (R.base_mem x hx)]; unfold W; rw [R.stays _ hx]))
 exact (show y*v=g by unfold y; group) ▸ harmonyBoth y v (p m y h₂) h₁
end YM.CF.Buffered.Afterglow.Rooted
