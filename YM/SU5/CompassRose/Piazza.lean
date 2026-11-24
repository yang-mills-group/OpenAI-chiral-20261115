import YM.SU5.CompassRose.Fair

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open Lamour Lamour.Bridge
variable (P:Spine)(s:ℕ)(A:ℝ)(β:ℕ→ℝ)
local notation "K"=> P.calibration
local notation "R" s:max=> sPow P.par s A
local notation "K!" f:max => Papal.household P.calibration f
local notation "P$" s:max => P.eReadL s
local notation "ζ⇒" => P.reflectTest 3
local notation "M$" => P.halfShift 3
local notation "lamp" X:max => temp (hat P.par.R.L P.par.x X)
namespace Piazza
open Fixture Shuttle Arrival
variable {I:Type*} [XX : Fintype I]
variable (F:I→Fixture)(X:ℕ→I→ Cover)(U:I→Gaia)(w:List I)
abbrev openC (x:I→ Cover):=(w.map (fun i=> Fixture.litP P s A β (F i) (x i))).prod
abbrev lateC (x:I→ Cover):=(w.map (fun i=> Fixture.poseP P s A β (F i) (x i))).prod
abbrev beams := (w.map (fun i=> (F i).dye)).prod
abbrev waters (x:I→ Cover) : Finset Cover:= (univ:Finset I).biUnion fun i=> (F i).inkP (x i)
local notation "K'" s:max=> openC P s A β F w (X s)
local notation "K+"=> beams F w
lemma litInk (x:I→ Cover) : InTest K true (waters F x) false (openC P s A β F w x).val ∧ CovCover K (openC P s A β F w x).val:=by
 induction w with
 | nil=> exact ⟨InTest.one,fun n _ _=>(map_one _).symm⟩
 | cons i w ih=>
   obtain ⟨h,h'⟩:= ih; let Z:=Fixture.litP P s A β (F i) (x i); let G:=openC P s A β F w x; let p:=inInk P s A β (F i) (x i)
   have ht:(F i).inkP (x i) ⊆ waters F x:= by intro a s; exact mem_biUnion.mpr ⟨i, mem_univ i,s⟩
   refine ⟨(p.1.mono ht).mul h, fun m g v=>?_⟩; change Z.val _ _ * G.val _ _= twist _ (Z.val m v*G.val m v); rw [map_mul]; exact congrArg₂ (· * ·) (p.2 m g v) (h' m g v)
omit XX
lemma penlight : (K' s)=(K+) • lateC P s A β F w (X s):=by
 induction w with
 | nil=> exact (one_smul ℂ _).symm
 | cons i w ih=> let Z:=Fixture.litP P s A β (F i) (X s i); change Z*openC P s A β F w _=_; rw [ih]; unfold Z litP; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul]; rfl
lemma bareWords : (lateC P s A β F w (X s)).val=K! (clusterW P β (fun i s=> trench (F i) (X s i)) (fun i _=> (F i).r) w A s):=by
 induction w with|nil=>rfl |cons i w ih=>exact congrArg ((Fixture.poseP P s A β (F i) (X s i)).val * · ) ih
abbrev refF : I→Fixture:=fun i=> (F i).reflectedF
lemma refWords (x:I→ Cover):
    (ζ⇒) (openC P s A β F w x)=openC P s A β (refF F) w (Shuttle.flip ∘ x):=by
 induction w with
 | nil=> exact Subtype.ext (mirror_unit ..)
 | cons i w h=> let L:= Fixture.litP P s A β (F i) (x i); let G:=openC P s A β F w x; change (ζ⇒) (L*G)=_; rw [show (ζ⇒) (L*G)=(ζ⇒) L*(ζ⇒) G from Subtype.ext (mirror_times ..)]; unfold L G; rw [reflectR,h]; rfl
abbrev moves (k:ℕ)(x:I→ Cover):= Shuttle.forward x P.par A k s
lemma shiftWords (k:ℕ): (M$) (kroll P.par A k s) (K' s)=openC P s A β F w (moves P s A k (X s)):=by
 induction w with
 | nil=>exact map_one _
 | cons i w ih=> let L:= Fixture.litP P s A β (F i) (X s i); change (M$) _ (L* openC P s A β F w _)=_; rw [map_mul,ih, show (P.halfShift 3 _ L)=_ from (Fixture.litNextR P s A β (F i) (X s i) (kroll P.par A k s))]; rfl
variable (k:ℕ)
lemma pairwise_visas (d:w.Pairwise fun i j=> U i≠ U j)(h:∀ i,0< gait P.par (U i) k 3) :
    let Y := dualC (fun i=> gait P.par (U i) k)
    (twins w).Pairwise fun i j=> Y i ≠ Y j:=by
 intro Y; refine List.pairwise_append.mpr ⟨List.pairwise_map.mpr (d.imp fun x p=> x (add_right_cancel (Shuttle.flip_inj p))), List.pairwise_map.mpr (d.imp fun x p=> x (add_right_cancel p)),?_⟩
 intro i h' j t; obtain ⟨i,p,rfl⟩:= List.mem_map.mp h'; obtain ⟨j,v,rfl⟩:= List.mem_map.mp t; intro e; have hx:=congrArg (fun t:Gaia=>t 3) e; change Shuttle.opposite _ _=gait _ _ _ _ at hx; rw [opp_tim] at hx; exact absurd hx ((lt_trans (neg_lt_zero.mpr (h i)) (h j)).ne)

abbrev Fbeams (U:I→Gaia) := (K+) * bill U (Sconce.F ∘ Fixture.lampS ∘ F) (Sconce.spin ∘ Fixture.lampS ∘ F) w
abbrev dub := Sum.elim (refF F) F
lemma join_words :
    ((ζ⇒) ((M$) (kroll P.par A k s) (K' s))) * ((M$) (kroll P.par A k s) (K' s))= openC P s A β (dub F) (twins w) (troupe (X s) P.par A k s):=by rw [shiftWords,refWords]; simp only [openC,twins,List.map_append,List.prod_append,List.map_map]; rfl
lemma inFlight : Tendsto (fun k=> Fbeams (dub F) (twins w) (dualC (fun i=> gait P.par (U i) k))) atTop (𝓝 (Fbeams (refF F) w (Shuttle.opposite∘U)*Fbeams F w U)):=by
 unfold Fbeams; let Ω:=fun (i:I) (k:ℕ)=> Shuttle.opposite (gait P.par (U i) k); have hx(n:ℕ)(i j:I): Ω i n-Ω j n= (Shuttle.opposite∘ U) i-(Shuttle.opposite∘ U) j:= by simp only [Ω,Function.comp_apply,flip_d,gait_d]
 let Z:= Sconce.F ∘ Fixture.lampS ∘ refF F; let Q0:= Sconce.F ∘ Fixture.lampS ∘ F; let H:= Sconce.spin ∘ Fixture.lampS ∘ refF F; let H0:=Sconce.spin ∘ Fixture.lampS ∘ F; let v:=fun n i=> Ω i n; let D₀ := Shuttle.opposite∘ U
 have he: (Sconce.F ∘ Fixture.lampS ∘ dub F) = Sum.elim Z Q0 := funext fun z=> by cases z <;> rfl
 have hp: (Sconce.spin ∘ Fixture.lampS ∘ dub F)=Sum.elim H H0:=funext fun z=> by cases z <;> rfl
 change Tendsto _ _ (𝓝 (beams (refF F) w * bill D₀ Z H w * ((K+)*bill U Q0 H0 w)))
 rw [show beams (dub F) (twins w)= beams (refF F) w * (K+) from ?_,he,hp]; rw [show beams (refF F) w * bill D₀ Z H w * ((K+)*bill U Q0 H0 w)= beams (refF F) w * (K+) * (bill D₀ Z H w * bill U Q0 H0 w) from (by ring)]; exact (rose_falling w w (Shuttle.opposite∘ U) U v (fun n i=> gait P.par (U i) n) hx (fun i j k=> gait_d ..) (fun i j=> foreign P.par (U i) (U j)) Z Q0 H H0).const_mul _
 simp only [beams,twins,List.map_append,List.prod_append,List.map_map]; rfl

section lengths
variable (W:I→Gaia) (e:A>0)
include e
variable {z d:ℝ} (Q:Investment P.par z d)(V:Dispatchers P.par)(m:Meritorious P.par)(v:ℕ→ℕ) (T:Pools P v β)
  (p:∀ i, Appoint P.par A (fun s=> X s i) (U i)) (t:∀ i j,U i=U j→ ∀ᶠ s:ℕ in atTop,X s i=X s j) (a:w.Pairwise fun i j=> U i ≠ U j)
include Q V m T p t a XX
lemma estimate : Tendsto (fun s=> (P$ s) (K' s)) atTop (𝓝 (Fbeams F w U)):=by
 let W:=fun i s=> trench (F i) (X s i); let r:=fun i:I=> fun _:ℕ=> (F i).r; have hv(i:I): LayoutBudget P A (U i) (W i) (r i) (r i) (F i).lampS.F (F i).lampS.spin:= (F i).lampS.obtains_at P A _ (F i).fitting e (fun s=>X s i) (U i) (p i)
 let Z:= Fixture.lampS ∘ F; apply ((wake_earning P v β T W e Q V m U (fun i=> (Z i).F) (fun i=>(Z i).spin) r r hv w a t).const_mul (K+)).congr; intro s; rw [penlight,map_smul]; exact congrArg (fun i=> ((K+) * P.E s i)) (bareWords P s A β F X w).symm
lemma backwards : Fbeams (refF F) w (Shuttle.opposite∘U)=star (Fbeams F w U):=by
 let Y(s:ℕ):=(ζ⇒) (K' s); let D(s:ℕ):=(P$ s) (Y s)
 have h:Tendsto D atTop (𝓝 (star (Fbeams F w U))):= (estimate P A β F X U w e Q V m v T p t a).star.congr fun s=>(Arrival.facing P s (K' s)).symm
 apply tendsto_nhds_unique _ h; apply (estimate P A β (refF F) (fun i=> Shuttle.flip∘ X i) (Shuttle.opposite ∘ U) w e Q V m v T (fun i=>xflip_a (p i)) (fun i j v=>(t i j (Shuttle.flip_inj v)).mono fun _ q=> congrArg Shuttle.flip q) (a.imp fun d p=> d (Shuttle.flip_inj p))).congr; intro s; exact congrArg (P$ s) (refWords P s A β F w (X s)).symm
omit Q V m T t a
local notation "Fₖ" k:max s:max=> OPlus P.par X A k s
lemma goingF (h:∀ i,0< gait P.par (U i) k 3) : ∀ᶠ s:ℕ in atTop, Tower.region 3 0 (K).ℓ (waters F (Fₖ k s)):=by
 let Y(s:ℕ):= Fₖ k s; let d:= (K).ℓ; let D(s i):= nodeC (Y s i); let r(i):=(F i).r+8; have he(i:I): ∀ᶠ s:ℕ in atTop, (↑(d+r i):ℤ) ≤ (D s i) 3:= xfront e (xplus_a e (p i) k) (h i) (d+r i)
 filter_upwards [Filter.eventually_all.mpr he] with s t'; intro i h'; obtain ⟨j,u,hx⟩:= mem_biUnion.mp h'; have hp:= ((pav_v (D s j) i (r j)).1 hx 3).1; change (0:ℤ)+ d ≤ i 3; have h:= t' j; omega
include Q V m T t a
lemma poll_aperture : WakePoll P (fun s=> K' s) (Fbeams F w U):=by
 let F' k:= Fbeams (dub F) (twins w) (dualC (fun i=> gait P.par (U i) k)); have he := estimate P A β F X U w e Q V m v T p t a; have hp:Tendsto F' atTop (𝓝 (star (Fbeams F w U)* Fbeams F w U)):= by rw [←backwards P A β F X U w e Q V m v T p t a]; exact inFlight P F U w
 refine adequacy P (fun s=> K' s) (kroll P.par A) (Fbeams F w U) F' (fun k s=> waters F (Fₖ k s)) he hp ?_
 filter_upwards [Filter.eventually_all.mpr (show ∀ i:I,∀ᶠ k:ℕ in atTop,(0:ℝ)<gait P.par (U i) k 3 from fun i=> (gait_up P.par (U i)).eventually_gt_atTop 0)] with n h
 constructor
 · filter_upwards [goingF P A F X U n e p h] with s t; rw [shiftWords]; exact ⟨(litInk P s A β F w (moves P s A n (X s))).1,t⟩
 let Ω(i):= gait P.par (U i) n; obtain ⟨g,b⟩:= troupe_loan e p t n h; simp_rw [join_words]; exact estimate P A β (dub F) (fun s=> troupe (X s) P.par A n s) (dualC Ω) (twins w) e Q V m v T g b (pairwise_visas P U w n a h)
#print axioms poll_aperture
end lengths
end Piazza
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
