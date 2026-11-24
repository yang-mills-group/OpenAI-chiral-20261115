import Bay.D.Helix
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

variable {K:Calibration}{S T:Finset Cover}{F G:ℕ→Buffered.Family K}{f g:Buffered.Family K}

abbrev Trip (K:Calibration) (F:ℕ→Buffered.Family K)(f:Buffered.Family K)
  (S:Finset Cover):= BQueue S F f

lemma trip_add
 (a:BQueue S F f) (b:BQueue S G g) :
  BQueue S (fun i=> F i+G i) (f+g) :=by
 obtain ⟨C,h,H,R⟩:=a.bdd
 obtain ⟨d,j,k,q⟩:=b.bdd
 refine ⟨fun i=> (a.whereTo i).add (b.whereTo i), a.landing.add b.landing,
    ⟨C+d,by positivity,pay_add H k, (R.and q).mono fun _ v=> pay_add v.1 v.2⟩,
    fun ε e=>?_⟩
 filter_upwards [a.saved (ε/2) (by positivity), b.saved (ε/2) (by positivity)] with i p q
 rw [add_sub_add_comm]
 exact (add_halves ε) ▸ (pay_add p q)
lemma trip_scale
 (a:BQueue S F f) (z:ℂ):
 BQueue S (fun i=>z • F i) (z • f):=by
 obtain ⟨C,h,H,q⟩:=a.bdd
 let V:=‖z‖+1
 have v:0<V:=by unfold V;positivity
 have p(g:Buffered.Family K) {d:ℝ}(u:Tower.pay g d) : Tower.pay (z • g) (V*d):=by
    intro i Q; exact le_trans (Tower.pay_scale u z ..) (mul_le_mul_of_nonneg_right
     (le_add_of_nonneg_right zero_le_one) (pay_nonneg u))

 refine ⟨fun i=> InTest.smul z (a.whereTo i),InTest.smul z a.landing,
   ⟨_,mul_pos v h,p _ H,q.mono (fun _ x=>p _ x)⟩,?_⟩
 intro e k
 filter_upwards [a.saved (e/V) (by positivity)] with i x
 rw [←smul_sub]
 simpa only [mul_div_cancel₀ _ v.ne'] using p _ x

lemma trip_enlarge (h:S⊆T) (a:BQueue S F f):BQueue T F f:=⟨fun i=>(a.whereTo i).mono h, a.landing.mono h,a.bdd,a.saved⟩

lemma trip_one (S:Finset Cover): BQueue S (fun _=>1:ℕ→Buffered.Family K) 1 :=
 BQueue.stay InTest.one zero_lt_one Tower.pay_unit

lemma staff_shift (K: Calibration) {N:Side}{W: Fabric N→Prop}
 {a:Mark N} (h: Staff W a S 1)
 (u:∀{x},W x→∀i s,W (x.twistL i s))(r:ℤ):
 Staff W (reflMark 3 (gaugeT K r) (reflMark 3 0 a)) (plow K 3 r S) 1:=by
 have e:=(h.foldr u (3:Axis) 0).foldr u 3 (gaugeT K r)
 rw[support_translation,sub_zero] at e
 exact e


lemma zero_rest {N:Side}(E: Finset (Seat N)): Lattice.halo 0 E ⊆ E := by
 intro x h
 obtain ⟨y,e,b⟩:= halo_spec.mp h
 obtain ⟨w,g⟩:=box_test.mp (Work.E08.lift_mem_box b)
 have t:Lattice.lift (x-y)=0:=by ext i; specialize w i; specialize g i; change Lattice.lift (x-y) i=0; omega
 have v:x-y=0:=by rw[←wrap_lift (x-y),t,map_zero]
 exact sub_eq_zero.mp v |>.symm ▸ e

abbrev Sonata(K:Calibration)(F: Buffered.Family K)(z:ℂ):=1+z • F
lemma trip_sonata (z:ℂ)(h:BQueue S F f):
 BQueue S (fun i=>Sonata K (F i) z) (Sonata K f z):=
 trip_add (trip_one S) (trip_scale h z)

lemma recital {m N:Side} (h:K.c m=N)
  (u:InTest K true S false f)
  (o d:Seat N) (A:Pane N→ℝ)
  (c:o∈Kspan N S) (t:d∈Kspan N S)
  (r: arrange _ _ h (f m)=Hookah.chalkOp (fun x=>(A x:ℂ)))
  (z:ℂ) (a:ℤ):
 Staff (Tunic o d A z)
     (arrange _ _ h (relocate K 3 a (Sonata K f z) m)) (plow K 3 a S) 1:=by
 subst N
 apply staff_shift K _ (fun h=>h.rev) a
 let y:Fabric (K.c m):=⟨Sonata K f z m,Kspan _ S,o,d⟩
 have hy:Tunic o d A z y:=by
   refine ⟨(show InTest K true S false (Sonata K f z) from (show InTest K true S false 1 from InTest.one).add
      (InTest.smul z u)).support _,c,t,1,z,Or.inl rfl,?_,?_,?_⟩
   · change f m = _ at r
     funext V
     change 1+ z • f m V= (1+z*(A ((1:Kite _).swirl V.1):ℂ)) •_
     rw[r,show ((1:Kite _).swirl V.1)=V.1 from Lattice.pull_id _,add_smul,one_smul,mul_smul]
   · exact Kite.r_one ..
   · exact Kite.r_one ..
 refine ⟨[y],Sylvan.one hy,?_,?_,rfl⟩
 · rw[buffet_more,buffet_empty,mul_one]
 rw[Broad_more,Broad_nil,union_empty]
 exact zero_rest _

variable (P:VacuumSelection.Spine)(s:ℕ)
  {i k:ℕ→ℕ}
local notation "X"=>P.Test
local notation "Y"=>P.run
local notation "Υ"=>P.calibration
local notation "Ω"=>scale P s
local notation "N" r:max=> Papal.count Y s r

structure Quaff (c b:ℕ)(x: Buffered.Family Υ)(S:Finset Cover)(μ:ℝ):Prop where
   leaseD: ∃(o d:Seat (N c)) (F :Pane (N c)→ℝ) (W':Chalk (More (N c)) ℝ),
       Lease Y s c b o d F W' ∧ beans Y s c b W'=μ ∧
       o∈Kspan (N c) S ∧ d∈Kspan (N c) S ∧
       pegN P s c x=Hookah.chalkOp (fun V=>(F V:ℂ))

lemma monsoon
 (e:Encore P s i k)
 {μ:ℝ}{m:ℕ→ℝ}(b:Tendsto m atTop (𝓝 μ)) {X0:X}
 {F0:ℕ→Buffered.Family Υ} (v:BQueue S F0 X0.val)
 (p:∀ᶠ n:ℕ in atTop, Quaff P s (i n) (k n) (F0 n) S (m n))
 {r:ℤ}(h:Noria P s (plow Υ 3 r S))
 (R:P.Register) (y:Guest P):
 Grip Ω μ (Price P s y X0):=by

 have a (z:ℂ)(t:‖z‖≤thetaB Ω):
     ‖1+z*Price P s y X0‖≤ Real.exp (z.re* μ+tilt Ω) ∧ |μ|≤Ni Ω:=by
    let u := 1+z• X0
    have q:Gigue P s i k z m (P.shifts 3 r u) (fun i=>relocate Υ 3 r (Sonata Υ (F0 i) z))
       (plow Υ 3 r S):=by
      refine ⟨h,(trip_sonata z v).station 3 _,?_⟩
      filter_upwards [p] with n a
      obtain ⟨o,d,x,W,w,hv,c,d',f⟩:=a.leaseD
      refine ⟨_,_,_,_,w,hv,?_⟩
      exact recital (Journey.terrain Y P.large _ _) (v.whereTo n) o d x c d' f z r
    have d:=music P s t b e q R y
    unfold u at d
    rwa [price_slide,map_add,price_one,map_smul,smul_eq_mul] at d
 exact ⟨(a 0 (by rw[norm_zero];have h':=h.able.1;unfold thetaB atRate;positivity)).2,
       fun z t=>(a z t).1⟩
