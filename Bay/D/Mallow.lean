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

variable (P:VacuumSelection.Spine)(s:ℕ)
local notation "K"=>P.calibration
local notation "Ω"=>scale P s
local notation "Y"=>P.run
local notation "N" c:max=> Papal.count Y s c
abbrev Cidre (c t:ℕ):= Cider
    (P.par.V.L.mood (P.run.uv t-s))
    (P.par.V.L.tied (P.run.uv t-s))
    (n:= More (N c)) (gram P.run s c t).p Ω
     (gram P.run s c t).beta

variable {S:Finset Cover}
/-- Price with no stencil dependence stated. -/
structure Lightly (c t r:ℕ)(x:Lake K S)(M:ℂ):Prop where
 salt: ∃ (o b:Seat (N c))(F:Pane (N c)→ℂ), 
    o∈Kspan (N c) S ∧ b∈Kspan (N c) S ∧ Cidre P s c t o b F M ∧
    Lake.Seal x r _ (Journey.terrain P.run P.large (P.run.ir c) s) F

lemma Lightly.small {c t r:ℕ}{x:Lake K S} {M}
 (q:Lightly P s c t r x M):
  Quaff P s c t (x.sun.pool r) S M.re ∧ Quaff P s c t (x.ray.pool r) S M.im:=by
 obtain ⟨o,b,F,h,j,p,l⟩:=q.salt
 obtain ⟨T,u,w⟩:=p Complex.reCLM (fun y=>by simpa using Complex.abs_re_le_norm y)
 obtain ⟨V,v,z⟩:=p Complex.imCLM (fun y=>by simpa using Complex.abs_im_le_norm y)
 exact ⟨⟨_,_,_,_,u,w,h,j,l.1⟩,⟨_,_,_,_,v,z,h,j,l.2⟩⟩

lemma prizes {r:ℤ} {x:Lake K S}
 {M:ℕ→ℂ} {μ:ℂ} (m:Tendsto M atTop (𝓝 μ))
 {i k:ℕ→ℕ}
 (w:Encore P s i k)
 (n:Noria P s (plow (P.calibration) (3:Axis) r S))
 (v:∀ᶠ b in atTop,Lightly P s (i b) (k b) b x (M b))
 (R:P.Register) (g:Guest P):
 PairGrip Ω μ (Price P s g x.allLake):=by
 have h:= monsoon P s w (Complex.continuous_re.tendsto _|>.comp m) x.sun.good
       (v.mono fun b t=>(Lightly.small P s t).1) n R g
 have l:= monsoon P s w (Complex.continuous_im.tendsto _|>.comp m) x.ray.good
       (v.mono fun b t=>(Lightly.small P s t).2) n R g
 refine ⟨_,_,?_,h,l⟩
 rw[Lake.allLake,map_add,map_smul,smul_eq_mul]


structure Light (c t r:ℕ){S:Finset Cover}(x:Lake K S)(a:ℤ)
     (M:Group3):Prop where
 buy:
   let b:=Lake.jumper K (N c) a
   let d:=(Signed.mirror 3).act b
   ∃ (o:Seat (N c)) (F: Pane (N c) →ℂ),
    x.Seal r _ (Journey.terrain P.run P.large (P.run.ir c) s) F ∧
    (forward b).rise o∈Kspan (N c) (Lake.paint K S a) ∧
    (after d).rise o∈Kspan (N c) (Lake.paint K S a) ∧
    ∀j: Fin 3, Cidre P s c t ((forward b).rise o) ((after d).rise o)
      (strata F (forward b) (after d) j) (M j)

lemma Light.dry {c t r} {x:Lake K S}{a M} (h:Light P s c t r x a M)(j:Fin 3):
   Lightly P s c t r (x.tones a j) (M j):=by
   obtain ⟨o,F,e,g,f,h⟩:=h.buy
   exact ⟨_,_,_,g,f,h j,Lake.tone_three e _ _ rfl _⟩

lemma Lightly.toll {c t r:ℕ}{x:Lake K S}{M:ℂ}
 (v:Lightly P s c t r x M):‖M‖≤Ni Ω+Ni Ω:=by
 obtain ⟨a,b⟩:=Lightly.small P s v
 obtain ⟨o,d,w,j,p,h,_⟩:=a.leaseD
 obtain ⟨l,g,z,e,u,v,_⟩:=b.leaseD
 apply Complex.norm_le_abs_re_add_abs_im _|>.trans
 rw[←h,←v]
 exact add_le_add p.flavor_fee u.flavor_fee

abbrev subSlot {φ:ℕ→ℕ}(w:Tendsto φ atTop atTop)(v:Cache K S):Cache K S where
 pool:= v.pool∘φ
 lake:=v.lake
 good := ⟨fun _=>v.good.whereTo _,v.good.landing,
    (by obtain ⟨c,t,r,h⟩:=v.good.bdd; exact ⟨_,t,r,w.eventually h⟩),
    fun z p=>w.eventually (v.good.saved z p)⟩
abbrev subLake {φ:ℕ→ℕ}(w:Tendsto φ atTop atTop)(x:Lake K S):Lake K S:=
 ⟨subSlot P w x.sun,subSlot P w x.ray⟩

variable {r:ℤ} (R:P.Register) {i k:ℕ→ℕ}
 (w:Encore P s i k)
 (n:Noria P s (plow (P.calibration) (3:Axis) r S))

def Itinerary(x:ℝ): Prop:= 0<x∧∀a b, PairGrip x a b→‖b-a‖≤twB x
lemma itineraries:∀ᶠ x in atTop,Itinerary x:= (eventually_gt_atTop _).and pairBack

include w n R in
theorem collects
 (x:Lake K S)
 (p:Itinerary Ω):
 ∀ᶠ y in atTop,∀M,Lightly P s (i y) (k y) y x M→
   ∀g, ‖Price P s g x.allLake-M‖ ≤2*twB Ω:=by
 by_contra c
 obtain ⟨ψ,v,d⟩:=extraction_forall_of_frequently (fun _=>not_eventually.mp c)
 push Not at d
 choose M t o using d
 choose g z using o
 have h(a): M a ∈ closedBall 0 (Ni Ω +Ni Ω):=
   mem_closedBall.mpr (by rw [dist_zero_right]; exact Lightly.toll P s (t a))

 obtain ⟨μ,_,φ,u,a⟩:= (isCompact_closedBall ..).tendsto_subseq h
 let e:=ψ∘φ
 have h':Tendsto e atTop atTop:=v.tendsto_atTop.comp u.tendsto_atTop
 let x':=subLake P h' x
 have k':Encore P s (i∘e) (k∘e):= ⟨row_shifts _ w.1 h',h'.eventually w.2⟩
 have hp(d):Lightly P s ((i∘e) d) ((k∘e) d) d x' ((M∘φ) d):= ⟨(t (φ d)).salt⟩
 have tw:0<twB Ω:=by have :=p.1; unfold twB atRate;positivity
 obtain ⟨b,j⟩:=(a.eventually (Metric.ball_mem_nhds _ tw)).exists
 have hq:=p.2 μ _ (prizes P s (i:=i∘e) (k:=k∘e) (r:=r) (x:=x') a k' n (Eventually.of_forall hp) R (g (φ b)))
 apply (z (φ b)).not_ge
 rw[two_mul]
 exact (norm_sub_le_norm_sub_add_norm_sub _ μ _).trans (add_le_add hq
    ((dist_eq_norm ..).symm.le.trans ((dist_comm ..).le.trans (mem_ball.mp j).le)))
include R w in

theorem mallets {S₁:Finset Cover} {a r:ℤ} 
  (n₁:Noria P s (plow K 3 r (Lake.paint K S₁ a)))
  (p:Itinerary Ω)(x:Lake K S₁):
 ∀ᶠ y in atTop,∀M,Light P s (i y) (k y) y x a M→∀g j,
    ‖Price P s g (Lake.notes P (P.shifts 3 a x.allLake) j)- M j‖≤2*twB Ω:=by
 have h:= (eventually_all ..).mpr (fun j=>collects P s R w n₁ (x.tones a j) p)
 filter_upwards [h] with u d M t g j
 rw [←Lake.tone_clause]
 exact d j (M j) (Light.dry P s t j) g

#print axioms mallets
