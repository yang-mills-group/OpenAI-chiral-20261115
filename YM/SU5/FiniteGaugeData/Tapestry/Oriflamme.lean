import YM.SU5.FiniteGaugeData.Tapestry.Baldachin
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP

/-!
# Local gauge action on the supported algebra. Covariance of B (with restriction
of FINER gauge at projected COARSER sites) and of the limiting state. Finite traces
use the same rule; this is not assuming separate Haar draws to gauge symmetrize any
matter labels.
-/
set_option quotPrecheck false
section
abbrev GVertex := Cover → SU.E
variable {K: Calibration} {S T:Finset Cover} {R:Cover→SU.E}
variable {f g F: Dome K} {n:Side}
lemma monoTrace (u:Seat n→SU.E)(p: S⊆T)(t:TraceGauge T R u):TraceGauge S R u:= fun i v=> t i (p v)
lemma largerGauge {f g:Family K}(p:S⊆T)(h:Circular S R f g): Circular T R f g:=fun m t q=> h m t (monoTrace t p q)

lemma doubleHarmony {N:Side}{f F g:Mark N}{t u:Seat N→SU.E}(p:Harmony t f g)(q:Harmony u g F) : Harmony (t*u) f F:=by
  have H(v:Fields N): simultaneous (t*u) v = simultaneous t (simultaneous u v):= Prod.ext (kind v.1) (kind v.2)
  intro v; rw [H,p,q]; let X:=tradew N t; let Y:=tradew N u; rw [←Hive.trade_c]; change twist (quantU X) (twist (quantU Y) _)=twist (quantU (X*Y)) _; rw [show quantU (X*Y)=quantU X*quantU Y from Subtype.ext (quant_mul ..)]; simp only [twist_formula,Submonoid.coe_mul,star_mul,mul_assoc]
where kind (x:Pane N): Lattice.gauge (t*u) x=Lattice.gauge t (Lattice.gauge u x):=funext fun e=>by simp [Lattice.gauge,mul_assoc] -- ambiguity
lemma oneHarmony {N:Side} (f:Mark N): Harmony (1: Seat N→ SU.E) f f:= by
  intro x; rw [show simultaneous 1 x=x from Prod.ext (kind x.1) (kind x.2),Hive.trade_p,show quantU (1:UNI (Single N))=1 from Subtype.ext quant_one,Fock.one_des]
where kind (x:Pane N): Lattice.gauge (1: Seat N→ SU.E) x=x:= funext fun i=>by simp [Lattice.gauge]

lemma printGauged (p:f∈bay K S true)(q:g∈bay K S true){m:Side} (h: Hosp S (K.c m))(u: Seat (K.c m)→ SU.E)(t:TraceGauge S R u)(a: Harmony u (f.val m) (g.val m)) : Circular S R f.val g.val:= by
 obtain ⟨x,rfl⟩:= accolade K S f p; obtain ⟨y,rfl⟩:= accolade K S g q; obtain ⟨z,e⟩:= turnScore K S R x
 have he:= circularUnique K S R x y z e m h ⟨u,t,a⟩
 -- he order
 simpa [he] using (show Circular S R (badge K S x).val (badge K S z).val from e)

lemma certificate (p:Circular S R f.val g.val)(q:Circular T R f.val F.val)(G:g∈bay K S true)(H:F∈bay K T true): F=g:=by
  obtain ⟨m,v⟩:= (separates K (S∪T)).exists
  obtain ⟨u,a⟩:=scoreTrace R (⟨v⟩:Hosp (S∪T) (K.c m)); apply Subtype.ext; refine looksLike (m:=m) ⟨v⟩ ((locates ..).mp (tallerBay K T true subset_union_right H)) ((locates ..).mp (tallerBay K S true subset_union_left G)) (funext fun x=>?_)
  exact (twist (quantU (tradew (K.c m) u))).injective ((q m u (monoTrace u subset_union_right a) x).symm.trans (p m u (monoTrace u subset_union_left a) x))

variable (K S R)
private lemma confirmed (wide:Bool)(f:Dome K)(p:f∈bay K S wide) : ∃ v: Dome K, v∈bay K S wide ∧ Circular S R f.val v.val:=by
 obtain ⟨F,P,U⟩:= reColor R ((locates K S wide).mp p); have he: InTest K true S false F:=by cases wide; exact P.widen; exact P
 exact ⟨⟨F,broadCompile K S he⟩,P,U⟩

def herald (f:Dome K):Dome K:= (confirmed K (precinct K f) R true f (precinct_spec K f)).choose
lemma depicted {wide:Bool}{f:Dome K}(p:f∈bay K S wide): herald K R f∈bay K S wide∧ Circular S R f.val (herald K R f).val:=by
  obtain ⟨v,h,t⟩:=confirmed K S R wide f p; have hx : herald K R f∈ bay K (precinct K f) true ∧ _ := (confirmed K (precinct K f) R true f (precinct_spec K f)).choose_spec
  rw [show herald K R f=v from certificate (f:=f) t hx.2 (widerBay K S wide h) hx.1]; exact ⟨h,t⟩
lemma appointed (f g:Dome K)(p:Circular S R f.val g.val)(e:g∈bay K S true): herald K R f=g:= certificate (f:=f) p ((depicted K (precinct K f) R (precinct_spec K f)).2) e ((depicted K (precinct K f) R (precinct_spec K f)).1)

def pennantₗ : Dome K→ₗ[ℂ] Dome K where
 toFun f:= herald K R f
 map_add' f g:=by
   obtain ⟨S,s,t⟩:= coAwake K f g; have hp:= depicted K S R s; have hx:= depicted K S R t; exact appointed K S R _ _ (hp.2.add R S hx.2) ((bay K S true).add_mem hp.1 hx.1)
 map_smul' z f:=by
   obtain ⟨S,s⟩:=findsBay K f; have hp:=depicted K S R s; exact appointed K S R _ _ (hp.2.scale R S z) ((bay K S true).smul_mem hp.1 z) -- order

def pennant : Dome K→ₐ[ℂ] Dome K:= AlgHom.ofLinearMap (pennantₗ K R) (appointed K ∅ R _ _ (fun m _ _ _=> (map_one _).symm) (bay K ∅ true|>.one_mem)) fun x y=> by
  obtain ⟨S,s,t⟩:=coAwake K x y; have hp:= depicted K S R s; have hx:= depicted K S R t; exact appointed K S R _ _ (hp.2.mul R S hx.2) ((bay K S true).mul_mem hp.1 hx.1)
lemma pennant_spec (f:Dome K): pennant K R f=herald K R f:=rfl
lemma pennantLocal {wide:Bool}{f:Dome K}(p:f∈bay K S wide): pennant K R f∈ bay K S wide:= (depicted K S R p).1
lemma pennantTrace {wide:Bool}{f:Dome K}(p:f∈bay K S wide): Circular S R f.val (pennant K R f).val:= (depicted K S R p).2
lemma pennantWide {wide:Bool} {f:Dome K}(p:f∈ vestibule K wide): pennant K R f∈vestibule K wide:=by obtain ⟨S,v⟩:= p; exact ⟨S,pennantLocal K S R v⟩
lemma colorFixed {f:Dome K} : f∈enclave K ↔ ∀ R:Cover→SU.E, pennant K R f=f:=by
  obtain ⟨S,t⟩:= findsBay K f; constructor
  · exact fun p R=> appointed K S R f f ((harmonicHere (S:=S)).1 p R) t
  intro h; apply (harmonicHere (S:=S)).2; intro R; nth_rw 2 [← h R]; exact pennantTrace K S R t -- potential rewrites f in S? tune
lemma pennantId (f:Dome K): pennant K 1 f=f:=by
  obtain ⟨S,t⟩:= findsBay K f; obtain ⟨m,h⟩:= (separates K S).exists
  exact appointed K S (1:Cover→SU.E) f f (printGauged t t (m:=m) ⟨h⟩ 1 (fun _ _=> rfl) (oneHarmony _)) t
lemma pennantCompose (v:Cover→SU.E)(f:Dome K): pennant K v (pennant K R f)=pennant K (R*v) f:=by
  obtain ⟨S,t⟩:= findsBay K f; obtain ⟨m,h⟩:= (separates K S).exists; obtain ⟨u,hu⟩:= scoreTrace R (⟨h⟩:Hosp S (K.c m)); obtain ⟨w,hx⟩:=scoreTrace v (⟨h⟩:Hosp S (K.c m))
  have he:=pennantLocal K S R t
  have hv:=pennantLocal K S v he
  symm; apply appointed K S _ f _ _ hv
  have h' : TraceGauge S (R*v) (u*w):= fun i p=>by rw [Pi.mul_apply,Pi.mul_apply,hu _ p,hx _ p]
  exact printGauged t hv ⟨h⟩ _ h' (doubleHarmony (pennantTrace K S R t m u hu) (pennantTrace K S v he m w hx))
lemma pennantInverse (f:Dome K) : pennant K R (pennant K R⁻¹ f)=f:=by rw [pennantCompose,inv_mul_cancel,pennantId]
lemma pennantBadge (x:Swatch S): pennant K R (badge K S x)=badge K S (ocelli K S R x):= appointed K S R _ _ (decorates K S R x) (locatesBadge ..)
-- any Z field orientation, see van etc.
variable (α: Axis)(z:ℤ)
abbrev reflectGauge (T:Cover→ SU.E): Cover→SU.E:= T∘ (plane α z).motion
-- one-step relation for Θ, no inadvertent need for extracting reflected Turtle centers
lemma reflectHarmony {w:Seat n→ SU.E}{b:Bool}{S: Lattice.Support (More n)}{A B: Mark n}(p: Harmony (w∘(plane α z).anon n) A B)(q:AtSupport b S B): Harmony w (reflMark α z A) (reflMark α z B):=by
 intro x; unfold reflMark; rw [show reflFields α z (simultaneous w x) = simultaneous (w∘(plane α z).anon n) (reflFields α z x) from Prod.ext (van ..) (van ..),p _]; exact theta_twist_right _ _ _ (congrArg Subtype.val (Lifted.gaugeSquare α z n w)) (q.allV _).sector
lemma pennantReflect {f:Dome K}: pennant K R (aureole K α z f)= aureole K α z (pennant K (reflectGauge α z R) f):=by
  obtain ⟨S,t⟩:= findsBay K f; let g:=pennant K (reflectGauge α z R) f; have ht:g∈bay K S true:= pennantLocal K S _ t
  let T:= negativeSide S z α; apply appointed K T R _ (aureole K α z g) _ (aureoleBay K S _ α z g ht)
  intro n w h; refine reflectHarmony α z (pennantTrace K S (reflectGauge α z R) t n (w∘(plane α z).anon (K.c n)) ?_) (((locates K S true).mp ht).support n)
  intro i v; change w _=_; rw [Shape.anno]; exact h _ (mem_image_of_mem _ v)
end
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
namespace Exhibition
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
variable (s:ℕ)(R:Cover→SU.E)
local notation "K"=> tent Y H
local notation "Up" S:max=> followBox (Λ:=Λ) (l:=l) S
lemma planetGauge (x:Dome K): planet Y H s D (pennant K R x)= planet Y H s D x:= by
  obtain ⟨S,t⟩:=findsBay K x; obtain ⟨f,rfl⟩:= accolade K S x t; rw [pennantBadge]; exact (ensembled S R Y H D s (decorates K S R f)).symm -- color spec
lemma pennantNatural (x:Dome K): liftD Y H s D (pennant K (parentGauge Λ R) x)=pennant K R (liftD Y H s D x):= by
  obtain ⟨S,t⟩:= findsBay K x; obtain ⟨y,rfl⟩:= accolade K S x t; rw [pennantBadge,fromLocal,fromLocal]; exact Eq.symm (appointed K (Up S) R (badge K (Up S) (B S s y)) _ (visibleColor S R Y H D s y _ (decorates K S (parentGauge Λ R) y)) (locatesBadge ..))
end Exhibition
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.pennantCompose
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.pennantNatural
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.planetGauge
#print axioms YM.CF.Buffered.Afterglow.Tapestry.pennantReflect
#print axioms YM.CF.Buffered.Afterglow.Tapestry.colorFixed
