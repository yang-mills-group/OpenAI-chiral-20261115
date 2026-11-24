import Velour.Gathers.Totty
namespace YM.Velour
open Filter Finset
lemma Gleams.slower {H:Hilbert}{f:ℕ→H.Op}{X:H.Op}(h:Gleams H f X){n:ℕ→ℕ}
    (p:Tendsto n atTop atTop): Gleams H (fun i=> f (n i)) X:=
  ⟨let ⟨B,r⟩:=h.bought; ⟨B,p.eventually r⟩,fun v=> (h.gaze v).comp p,fun v=>(h.turn v).comp p⟩
lemma slowlyMany {ι:Type}[Nonempty ι][Countable ι]
   (Q:ℕ→ι→ℕ→Prop)(h:∀n d, ∀ᶠ i in atTop, Q n d i):
   ∃ φ:ℕ→ℕ, (∀i,i ≤ φ i) ∧ ∀d,∀ᶠ i in atTop,Q i d (φ i):=by
 obtain ⟨e,u⟩:=exists_surjective_nat ι
 have y(i:ℕ):∃a:ℕ,i ≤ a ∧ ∀j∈range i,Q i (e j) a:= by
    exact ((eventually_ge_atTop i).and ((eventually_all_finset (range i)).mpr fun j _=> h i (e j))).exists
 choose n t using y
 refine ⟨n,fun i=>(t i).1,fun d=>?_⟩
 obtain ⟨j,rfl⟩:=u d
 filter_upwards [eventually_gt_atTop j] with i c
 exact (t i).2 j (mem_range.mpr c)
end YM.Velour
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

variable {P:Spine}{j:Axis}{x:P.Spectrum0 j}


variable (x)
local notation "τ"=> P.macroStep
structure Slower (T U:ℕ→P.Apron) (n:ℕ→ℕ):Prop where
  thin: Tendsto (fun i=> (U i).realWidth P j) atTop (𝓝 0)
  late:Tendsto n atTop atTop
  printed:∀i, ∀a:ℝ, (U i).realWidth P j ≤ a→(U i).velour P j x a = (T (n i)).velour P j x a

namespace Slower
variable {x}{T U:ℕ→P.Apron}{n:ℕ→ℕ}
local notation:max "W" d:max=> Apron.realWidth P d j
local notation:max "V!" d:max =>Apron.velour P j x d

lemma eventually (p:Slower x T U n){a:ℝ}(e:0<a):
   (fun i=>V! (T (n i)) a)=ᶠ[atTop] (fun i=>V! (U i) a):=by
 filter_upwards [p.thin.eventually_le_const e] with i hi
 exact (p.printed i a hi).symm
lemma velvet(p:Slower x T U n)(h:Veloured P j x T): Veloured P j x U:=by
 refine ⟨p.thin,fun _ e=>⟨_, ((h.printed e).slower p.late).agree (p.eventually e)⟩,?_⟩
 obtain ⟨B,D,r,t,u⟩:=h.bill
 refine ⟨B,D,r,t,u.mono fun k y=>?_⟩
 filter_upwards [p.late.eventually y,p.eventually (P.macroStep_pos k)] with i w z
 change V! (T (n i)) _=V! (U i) _ at z
 rw [←z]; exact w


theorem strong (p:Slower x T U n){v:ℕ→ℕ}(w:Tendsto v atTop atTop)
     (r:∀i,τ (v i) ≤ W (U i))
     {B D:ℝ}(m:ℕ)(b:1≤B)(d:1≤D)
     (h:∀ᶠ i in atTop, ∀k:ℕ, m ≤ k→ k≤v i→W (T (n i)) ≤ τ k ∧ ‖V! (T (n i)) (τ k)‖ ≤ B*D^k):
    P.Totty j x U:=by
 refine Totty.of_tail m b d ?_
 filter_upwards [h,w.eventually (eventually_ge_atTop m)] with i g y k c
 let a:=W (U i)+τ k
 have ha: W (U i) ≤ a:=le_add_of_nonneg_right (P.macroStep_pos k).le
 change ‖V! (U i) a‖ ≤ _
 rw [p.printed i a ha]
 let l:= min k (v i)
 have e: τ l ≤ a:=by
   cases min_choice k (v i) with
   | inl h=> exact (show l=k from h) ▸ le_add_of_nonneg_left ((U i).real_width_pos P j).le
   | inr h=> exact (show l=v i from h) ▸ ((r i).trans ha)
 obtain ⟨f,q⟩:=g l (le_min c y) (min_le_right ..)
 refine ((T (n i)).velour_le P j x f e).trans (q.trans ?_)
 exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ d (min_le_left ..)) (zero_le_one.trans b)
end Slower



end Spine
namespace Spine
open Aria Casting
open MacroGrid Velour
variable (P:Spine)(x:P.Spectrum0 3)(A:ℕ→P.Apron)

def TottyCup:Prop:=
  ∀(j:Axis)(l:List Axis), P.Totty j (P.advocate 3 x j) (fun i=> (A i).pivot P l)

variable (v:ℕ→ℕ)
  (Φ:(ℕ→ℕ)→ℕ→P.Apron)
local notation "I!"=> Axis×List Axis
local notation "τ"=> P.macroStep
local notation:max "x!" j:max=> P.advocate 3 x j
local notation:max "T♯" a:max l:max n:max =>
    Apron.pivot P (a n) l

lemma slow_cup (e:P.VelvetCup x A) (w:Tendsto v atTop atTop)
    (s:∀n:ℕ→ℕ,(∀i,i ≤ n i)→
      ∀(j:Axis)(l:List Axis),
         Slower (x! j) (fun i=>T♯ A l i)
              (fun i=>T♯ (Φ n) l i) n
         ∧ ∀i,τ (v i) ≤ (T♯ (Φ n) l i).realWidth P j):
    ∃n,P.VelvetCup x (Φ n) ∧ P.TottyCup x (Φ n):=by


 let U(i k:ℕ)(d:I!)(B D:ℝ): Prop:=
   ((T♯ A d.2 i).realWidth P d.1≤τ k ∧
     ‖(T♯ A d.2 i).velour P d.1 (x! d.1) (τ k)‖ ≤ B*D^k)
 have t(d:I!): ∃ (B D:ℝ)(m:ℕ), 1≤B ∧ 1≤D ∧
                        ∀k:ℕ,m ≤ k→∀ᶠ i in atTop, U i k d B D :=by
    let p:=e d.1 d.2
    obtain ⟨B,D,a,b,y⟩:=p.bill
    obtain ⟨m,h⟩:=eventually_atTop.mp y
    exact ⟨B,D,m,a,b,fun k r=>(p.thin.eventually_le_const (P.macroStep_pos k)).and (h k r)⟩
 choose B D m y using t
 let C (i:ℕ)(d:I!):= Finset.Icc (m d) (v i)
 let Q(i:ℕ)(d:I!)(j:ℕ):=
    ∀k∈C i d, U j k d (B d) (D d)
 have r(i:ℕ)(d:I!):∀ᶠ j in atTop, Q i d j:=
    (eventually_all_finset (C i d)).mpr fun k h=>
       (y d).2.2 k (Finset.mem_Icc.mp h).1
 obtain ⟨n,h,h'⟩:= slowlyMany Q r
 refine ⟨n,fun j l=>((s n h j l).1).velvet (e j l),fun j l=>?_⟩


 obtain ⟨p,q⟩:=s n h j l
 exact p.strong w q (m (j,l)) (y (j,l)).1 (y (j,l)).2.1
    ((h' (j,l)).mono fun i w k c t=>w k (Finset.mem_Icc.mpr ⟨c,t⟩))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
