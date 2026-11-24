import Bay.D.Meg
import Bay.D.Blinket
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

open Buffered.Lifted
abbrev flood(K:Calibration)(f: LinksC→ℂ):Buffered.Family K:= scalar K (f∘Prod.fst)
variable (K:Calibration){S:Finset Cover}{L:ℝ}{f:LinksC→ℂ}
namespace Enroll

lemma sendT (h:Enroll S L f): InTest K true S false (flood K f):= by
 refine .seed ⟨by simp,⟨h.meas.comp measurable_fst,L,fun i=>h.flat _⟩,fun i k p _ => h.seated _ _ p⟩

lemma dueT(h:Enroll S L f): Tower.pay (flood K f) L:=by
 intro i x
 change ‖f _ •(1:FC _)‖≤ L
 rw[norm_smul,norm_one,mul_one]
 exact h.flat _

lemma pureT(h:Enroll S L f) :Tapestry.Neutral K (flood K f):=by
 intro n g x
 let G := g ∘ wrap (More (K.c n))
 have a := h.seated _ _ (gauge_trace G (show TraceGauge S G g from fun _ _=>rfl) x.1)
 change f _ • 1= twist _ (_ • 1)
 rw[twist_scalar,map_one];exact congrArg (fun z:ℂ=> z • (1:FC (Single (K.c n)))) (a.trans (h.hue ..))
def ship(h:Enroll S L f):Dome K:=⟨flood K f,aux_test (sendT K h)⟩

variable {F:ℕ→LinksC→ℂ}
lemma cache(h:∀i,Enroll S L (F i))(u:Enroll S L f)
   (x:∀ε:ℝ,0<ε→∀ᶠ i:ℕ in atTop,∀z, ‖F i z-f z‖≤ ε):
  BQueue S (fun i=>flood K (F i)) (flood K f):=by
 have w:0≤L:=(norm_nonneg _).trans (u.flat 1)

 refine ⟨fun i=>sendT K (h i), sendT K u,
   ⟨L+1,by linarith,fun i x=>(dueT K u i x).trans (le_add_of_nonneg_right zero_le_one),
     Eventually.of_forall fun n i x=>(dueT K (h n) i x).trans (le_add_of_nonneg_right zero_le_one)⟩,
   fun ε p=>?_⟩
 filter_upwards [x ε p] with n v i y
 change ‖(_ : ℂ) • (1:FC (Single (K.c i)))-(_ : ℂ) • 1‖≤ _
 rw [←sub_smul,norm_smul,norm_one,mul_one]
 exact v _

-- Real & imaginary seats
abbrev latticeFieldEstimates(f:LinksC→ℂ)(b:Bool)(x:LinksC):ℂ:=
   if b then (f x).im else (f x).re
lemma halfT(h:Enroll S L f)(b:Bool): Enroll S L (latticeFieldEstimates f b):=by
 unfold latticeFieldEstimates; cases b
 · exact ⟨Complex.continuous_ofReal.measurable.comp (Complex.continuous_re.measurable.comp h.meas),
     fun i=> (Complex.norm_real _).le.trans ((Complex.abs_re_le_norm _).trans (h.flat i)),
     fun i j k=>congrArg (fun z=>(z.re:ℂ)) (h.seated i j k),
     fun t x=>congrArg (fun z=>(z.re:ℂ)) (h.hue t x)⟩
 exact ⟨Complex.continuous_ofReal.measurable.comp (Complex.continuous_im.measurable.comp h.meas),
     fun i=> (Complex.norm_real _).le.trans ((Complex.abs_im_le_norm _).trans (h.flat i)),
     fun i j k=>congrArg (fun z=>(z.im:ℂ)) (h.seated i j k),
     fun t x=>congrArg (fun z=>(z.im:ℂ)) (h.hue t x)⟩

lemma latticeFieldEstimatesL(g:LinksC→ℂ)(b:Bool)(x:LinksC):‖latticeFieldEstimates f b x-latticeFieldEstimates g b x‖ ≤ dist (g x) (f x):=by
 rw[dist_comm,dist_eq_norm]
 unfold latticeFieldEstimates; cases b
 · simp only[Bool.false_eq_true,reduceIte,←Complex.ofReal_sub,Complex.norm_real]; exact Complex.abs_re_le_norm (f x-g x)
 simp only[reduceIte,←Complex.ofReal_sub,Complex.norm_real]; exact Complex.abs_im_le_norm (f x-g x)

def flush(h:∀i,Enroll S L (F i))(u:Enroll S L f)(x:TendstoUniformly F f atTop)
 (b:Bool):Cache K S:=⟨_,
    ship K (halfT u b),cache K (fun i=>halfT (h i) b) (halfT u b)
      fun ε p=> (Metric.tendstoUniformly_iff.mp x ε p).mono fun n y z=>
       (latticeFieldEstimatesL _ _ _).trans (y z).le⟩

def flowing(h:∀i,Enroll S L (F i))(u:Enroll S L f)(x:TendstoUniformly F f atTop):Lake K S:=
    ⟨flush K h u x false,flush K h u x true⟩
end Enroll

structure Gather (o:Cover)(b:ℕ)(t d L:ℝ) where
 fleet: ℕ→LinksC→ℂ
 rise:LinksC→ℂ
 wash(i):Furled o b t d L (fleet i)
 spun:Furled o b t d L rise
 dawn:TendstoUniformly fleet rise atTop
variable {o:Cover}{b:ℕ}{t d:ℝ}
local notation "SΩ"=>Band o b
namespace Gather
def atK(w:Gather o b t d L):Lake K SΩ:=
 Enroll.flowing K (fun i=>(w.wash i).toEnroll) w.spun.toEnroll w.dawn
lemma stamp{N:Side}(w:Gather o b t d L)(m:Side)(e:K.c m=N)
 (i:ℕ)(F:Pane N→ℂ)(v:F=w.fleet i ∘ onC N):
 (w.atK K).Seal i m e F:=by subst N;subst F;constructor <;> rfl

lemma gather_sum(g:LinksC→ℂ):
 flood K (Enroll.latticeFieldEstimates g false)+Complex.I • flood K (Enroll.latticeFieldEstimates g true)=flood K g:=by
 funext m x
 change (_:ℂ) • (1:FC (Single _)) + Complex.I • ((_:ℂ) • 1)=(_:ℂ)•1
 rw [smul_smul,←add_smul,mul_comm Complex.I];exact congrArg (fun z:ℂ=>z • (1:FC (Single (K.c m)))) (Complex.re_add_im (g _))
lemma achieved(w:Gather o b t d L):
 ((w.atK K).allLake).val=flood K w.rise := gather_sum ..

lemma anyGauge(w:Gather o b t d L):
 Tapestry.Neutral K ((w.atK K).allLake).val:=
   (w.achieved K).symm ▸ Enroll.pureT K w.spun.toEnroll
end Gather

def Sprucy (o:Cover)(b:ℕ)(t d L:ℝ){N:Side}
 (f:Pane N→ℂ):Prop:=
 ∃p:BudgetPoint,p.B=b∧p.threshold=t∧ Vinyl p (wrap _ o) (b/10) d L f

lemma Sprucy.craft {N:Side}{g:Pane N→ℂ} (h:Sprucy o b t d L g)(p:AtEase SΩ N):
  Furled o b t d L (g ∘ D.craft SΩ N)∧g=(g ∘ D.craft SΩ N) ∘ onC N:=by
 obtain ⟨p',x,y,w⟩:=h
 subst b
 exact ⟨w.readIn rfl y (Nat.div_le_self ..) p,
   funext fun i=>(w.localV _ _ (craft_back p i)).symm⟩

theorem gatherings {R:ℕ→Side}{g:∀i,Pane (R i)→ℂ}
 (h:∀ᶠ i:ℕ in atTop,Sprucy o b t d L (g i))
 (p:∀ᶠ i:ℕ in atTop,AtEase SΩ (R i)):
 ∃φ:ℕ→ℕ,StrictMono φ∧∃w:Gather o b t d L,∀i,
    g (φ i)=w.fleet i ∘ onC _:=by
 obtain ⟨n,e⟩:=eventually_atTop.mp (h.and p)

 let v(i):= (e (n+i) (by omega))
 have z:=fun i=>Sprucy.craft (v i).1 (v i).2
 obtain ⟨φ,t,f,r,x⟩:=furleds (F:=fun i=>g (n+i) ∘ D.craft SΩ _) (fun i=>(z i).1)
 exact ⟨fun i=>n+φ i,fun _ _ h=>Nat.add_lt_add_left (t h) _,
    ⟨_,f,fun i=>(z _).1,x,r⟩,fun i=>(z _).2⟩
end YM.CF.Bay.D
