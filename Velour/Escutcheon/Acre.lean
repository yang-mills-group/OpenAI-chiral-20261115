import Velour.Escutcheon.Chasing
import YM.SU5.FiniteGaugeData.Poin.Bureau
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {S:Semigroup H timeAxis}


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

open YM.Damask Mink
variable (b:SpaceAxis){H':Hilbert}{T:Semigroup H' b.castSucc}

def scroll(b:SpaceAxis):ℝ→Lorentz := (Ray.fromAxis b).boost

theorem royal (b:SpaceAxis): timeAxis≠b.castSucc:=by
  exact (Fin.castSucc_lt_last b).ne'

variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
  (A:S.Tiles (royal b))(B:T.Tiles (royal b).symm)
variable {n:ℕ}
namespace Livery
local notation "h₃"=> royal b
local notation "∆"=> scroll b
open Flute

lemma coronation : magnet (Ray.fromAxis b)=silk h₃:=by
 apply Subtype.ext
 change position (EuclideanSpace.single b (1:ℝ)) 0=basis b.castSucc
 apply ext_by
 · rw [spatial_position]
   ext i; simp [spatial, PiLp.single_apply]
 rw [time_position]
 simp [YM.time,royal]


lemma tally (x:E4):fsp (Ray.fromAxis b) x=sewnOut h₃ x:=by rw [fsp,Ray.onAxis,coronation];rfl

lemma foil_scroll (x:E4)(v:ℝ):
 Lorentz.act (∆ v) x=
 sheer h₃ (hyperu v (x timeAxis) (x b.castSucc))
          (hypers v (x timeAxis) (x b.castSucc)) x:=by
 let e:=Ray.fromAxis b
 have t:= trip e (YM.time x) (e.along x) v (fsp e x) (nez e x)
 rw [attend] at t
 unfold e at t; rw [Ray.onAxis,coronation,tally] at t; exact t

variable (u:Fin n→κ)
local notation "Rc"=>L.ringCost J u
def walked(z w:Fin n→ℂ)(g:Lorentz)(x:Points n):= 
 L.gemK h₃ A u z w (lmove g x)
lemma crown_boost (d:Fin n→ℝ)(p:StrictMono d)(x:Points n)(a:ℝ):
 L.walked b A u (θδ a d) (ηδ a d) (∆ a) x=
 L.drifts h₃ A u x.ofLp (initβ (clockV timeAxis x) d I) (soaked (clockV b.castSucc x)) a:=by
   rw [L.drifts_gem h₃ A u _ (clockV timeAxis x) _ (clockV b.castSucc x) p]
   unfold walked
   congr 1
   ext1 i; exact foil_scroll b _ a

variable (f:Fin n→Test4)
def diadem (d:Fin n→ℝ)(a:ℝ):Points n→ℂ:=fun x=>
 Joint.materialize n f x * L.walked b A u (θδ a d) (ηδ a d) (∆ a) x
local notation "C"=> L.diadem b A u f

abbrev af (g:Lorentz)(f:Fin n→Test4):=
 _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.active (Poincare.motion g) f

lemma together (g:Lorentz): MeasurePreserving (Poincare.togetherL g n) volume volume:=by
   have e:(Poincare.togetherL g n:Points n→Points n)=Poincare.zusammen (Poincare.motion g) n:=by
      ext1 x; ext1 i; simp [Poincare.zusammen]
   rw [e]
   exact Poincare.together _ _

def rConcert(z w:Fin n→ℂ):Points n→ℂ:=
   concert S L.Ω.val L.Ω.val (L.spunG u) (L.risers h₃ A u z w) f

lemma radiance (d a):
 Integrable (C d a) volume ∧
 (∫x,C d a x) =
 ∫x, L.rConcert b A u (af (∆ a) f) (θδ a d) (ηδ a d) x:=by
  let m:= Poincare.togetherL (∆ a) n
  let g:=L.rConcert b A u (af (∆ a) f) (θδ a d) (ηδ a d)
  have t:C d a=g ∘ m:= by
    funext x; dsimp only [diadem,g,rConcert,concert]
    rw [← diagrams (∆ a) f x]; rfl
  have r:Integrable g:=billI ..

  have w:MeasurableEmbedding m:=m.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have p:=together (n:=n) (∆ a)
  rw [t]
  exact ⟨(p.integrable_comp_emb w).mpr r,p.integral_comp w g⟩

include B in
lemma arcade (r:Pact L J)(v:Rank Rc→ℝ)(y:Injective v)
   (d:Fin n→ℝ)(p:StrictMono d)(a:ℝ):
 (∫x,C d a x)=∑ i,hoops Rc (risen ∘ v) (risen a) i * ∫x,C d (v i) x:=by
 let Z i:= hoops Rc (risen ∘ v) (risen a) i
 have k(x:Points n): C d a x=∑ i,Z i * C d (v i) x:=by
    have e(y):=L.crown_boost b A u d p x y
    unfold diadem
    simp_rw [e]
    dsimp only [Z]
    rw [L.chasing J h₃ A B u _ _ _ _ r p v y a,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _=>?_ 
    rw [mul_left_comm]
 simp_rw [k]
 rw [integral_finsetSum]
 · simp_rw [integral_const_mul];rfl
 intro i _; exact (L.radiance b A u f d (v i)).1.const_mul _

lemma festoon(a:ℝ):
 Tendsto (fun i=>∫x,C (hymns n i) a x) atTop (𝓝 (L.brim u (af (∆ a) f))):=by
 simp_rw [fun d=>(L.radiance b A u f d a).2]
 apply L.recaps u (silk h₃) A (fun i=>θδ a (hymns n i)) (fun i=>ηδ a (hymns n i))
 · exact fun i=>char a n _ (hymnsP ..)
 · intro i
   unfold θδ soaked
   have t:= (continuous_ofReal.tendsto _).comp ((hymnsL n i).const_mul (Real.cosh a))
   simpa only [Function.comp_def,ofReal_zero,mul_zero] using t

 intro i
 unfold ηδ
 simpa only [Function.comp_def,ofReal_zero,mul_zero,zero_mul] using
    (((continuous_ofReal.tendsto _).comp (hymnsL n i)).const_mul (Real.sinh a:ℂ)).mul_const I


include A B
theorem rose_window (p:Pact L J)(v:Rank Rc→ℝ)(y:Injective v)(a:ℝ):
 L.brim u (af (∆ a) f)=∑ i,hoops Rc (risen ∘ v) (risen a) i * L.brim u (af (∆ (v i)) f):=by
 have t:=tendsto_finsetSum Finset.univ fun i (_: i∈Finset.univ) =>
   (L.festoon b A u f (v i)).const_mul (hoops Rc (risen ∘ v) (risen a) i)
 exact tendsto_nhds_unique_of_eventuallyEq (L.festoon b A u f a) t
    (Eventually.of_forall fun j=>L.arcade b J A B u f p v y _ (hymnsP n j) a)

theorem grows (p:Pact L J):
 Grows Rc (fun a=>L.brim u (af (∆ a) f)):=by
 apply Grows.of_raised
 exact L.rose_window b J A B u f p (levy Rc) (Nat.cast_injective.comp Fin.val_injective)
#print axioms rose_window
#print axioms grows
