import Merino.Plume.Cloud
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}


/-- Motion with optional Charge at first-pane Cover level. -/
def snow (s:Signed)(b:Cover)(h:Bool)(x:LinksC):LinksC:=
 polarT h ∘ Lattice.pull s b x
variable (s:Signed)(b:Cover)(h:Bool)
lemma snowC:Continuous (snow s b h):=by
 apply continuous_pi; intro i
 unfold snow Function.comp Lattice.pull Lattice.Step.read
 split <;> exact (rev_C h).comp (by fun_prop)

lemma slush (U:Pane n):
 snow s b h (onC n U)= onC n (polarT h ∘ pull s (wrap (More n) b) U):=by
 funext ⟨i,j⟩
 simp only [snow,onC_spec,comp_apply]
 let d:=(Lattice.posDir j).rotate s
 have e:= travel_at 0 U (affine s b i) [d]
 simp only [travel,mul_one,add_zero] at e
 rw [show wrap (More n) (affine s b i)=
      affine s (wrap (More n) b) (wrap (More n) i) by simp [affine]] at e
 exact congrArg (polarT h) e

private lemma epos (i:Cover)(j:Axis):
 affine s b (i+step j)=affine s b i + ((Lattice.posDir j).rotate s).vec:=by
 simp only [Lattice.Step.vec_rotate,Lattice.Step.vec_pos,affine, Signed.act_add]
 abel


lemma skate {x y:LinksC}{S:Finset Cover}(p:Agrees (S.image (affine s b)) x y):
 Agrees S (snow s b h x) (snow s b h y):=by
 rintro ⟨i,j⟩ a k
 change polarT _ (((Lattice.posDir j).rotate s).read _ _)=_
 let d:=(Lattice.posDir j).rotate s
 let c:= affine s b i
 have v:c∈S.image (affine s b):=mem_image_of_mem _ a
 change i+step j∈S at k
 have u:c+d.vec∈S.image (affine s b):=(epos s b i j) ▸ (mem_image_of_mem (affine s b) k)
 -- eliminate d
 suffices e:d.read x c=d.read y c from congrArg (polarT h) e
 obtain ⟨f,_|_⟩:=d
 · exact p (c,f) v u
 have w: c-step f∈S.image (affine s b):=by
    rw [sub_eq_add_neg];exact u
 exact congrArg Inv.inv (p (c-step f,f) w (by simpa using v))
lemma sang_snow(k:Cover→E)(x:LinksC):
 snow s b h (gauge k x)=gauge (fun i=>polarT h (k (affine s b i))) (snow s b h x):=by
 funext ⟨i,j⟩
 simp only [snow,Lattice.pull,comp_apply]
 rw [Lattice.Step.gauge_read,map_mul,map_mul,map_inv, Lattice.gauge, epos]
 rfl


/-- A uniformly bounded pure-gauge singlet stencil. -/
structure Swan (S:Finset Cover) (L:ℝ)(f:LinksC→ℂ):Prop where
   reads:Measurable f
   region: LocalOn S f
   sang:GaugeInvariant f
   bound (V):‖f V‖≤L
variable {F G : LinksC→ℂ}{L:ℝ}{S:Finset Cover}
lemma Swan.nonneg (v:Swan S L F):0≤L:=(norm_nonneg _).trans (v.bound 1)
lemma Swan.skis (v:Swan S L F):
 Swan (S.image (affine s b)) L (F∘snow s b h):=
 ⟨v.reads.comp (snowC s b h).measurable,fun _ _ p=> v.region _ _ (skate s b h p),
 fun k x=>by simp only [comp_apply,sang_snow,v.sang _ _],fun _=>v.bound _⟩

abbrev vale (m:ℕ)(b:Cover):=(Lattice.box m).image (fun i=>i+b)
lemma Swan.hill (v:Swan (Lattice.box m) L F):
 Swan (vale m b) L (F∘snow s b h):=by
 have p:=v.skis s b h
 have t:(Lattice.box m).image (affine s b) = vale m b:=by
   unfold vale
   nth_rw 2 [← box_covariant m s]
   rw [image_image]
   rfl
 rwa [t] at p


abbrev present (K:Calibration)(F:LinksC→ℂ):Buffered.Family K:=
 Buffered.scalar K (F ∘ Prod.fst)
lemma Swan.law (K:Calibration)(v:Swan S L F): InTest K true S false (present K F):=by
 refine InTest.seed (wide:=true) (f:=F ∘ Prod.fst) ⟨fun g=>by contradiction, ⟨v.reads.comp measurable_fst,L,fun _=>v.bound _⟩,fun x y a _=>v.region _ _ a⟩
lemma Swan.greet (K:Calibration)(v:Swan S L F):Singlet (present K F):=by
 apply Eventually.of_forall; intro i _ g x
 simp only [present,Buffered.scalar, simultaneous, Prod.map_fst,comp_apply,twist_scalar,map_one]
 -- prod?
 congr 1
 exact sang_full v.sang _ g x.1
-- voucher

end YM.CF.Merino.Plume
