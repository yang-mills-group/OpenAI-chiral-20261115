import YM.CF.BProof.Trek.Lit
/-! Borel computations incl on viewing new cores. `XKN` measured before or after. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c a:Side} {Y:Yard s}
variable {A:Type*}[MeasurableSpace A]
-- `B` finset block variable read by measurable partition eliminating. Generic local.
section
variable {I:Type*}[MeasurableSpace I][Countable I][MeasurableSingletonClass I]{J:Type*}[MeasurableSpace J]
lemma meal {f:A→I}(p:Measurable f)(g:I→A→J)(h:∀ i,Measurable (g i)):Measurable fun x=>g (f x) x:= by
 intro s e; rw [show (fun x=>g (f x) x) ⁻¹' s=⋃ i,f ⁻¹' {i} ∩ g i ⁻¹' s from ?_]; exact MeasurableSet.iUnion fun i=>(p (measurableSet_singleton _)).inter (h i e)
 ext; simp
end
structure Tonic (F:A→Script Y):Prop where
 base(i) (t):Measurable fun x=>(F x).X i t
 key(i) (s t): Measurable fun x=>(F x).K i s t
 frame(i t):Measurable fun x=>(F x).frame i t
 label(i t):Measurable fun x=>(F x).label i t
section
variable (S: Hall s)(f:Ratio c s)
lemma production (U:A→Bkg s)(P:A→Y.FaceS)(D:A→Y.Glyph)(u:Measurable U)(p:Measurable P)(v:Measurable D): Tonic (fun x=>actual S f (U x) Y (P x) (D x)):=by
 have ht (i:Y.Index):Measurable (fun x:A=> (U x,P x i)):= u.prodMk ((measurable_pi_apply (X:=fun i:Y.Index=> Eyes s) i).comp p)
 constructor
 · intro i t; change Measurable (fun x:A=> winter Y i S f (U x) (P x i) t); exact (measurable_pi_apply (X:=fun _:Site s=>Ballot) t).comp ((tideL Y i S f).comp (ht i))
 · intro i t v; change Measurable (fun x:A=>summer Y i S f (U x) (P x i) t v); exact (measurable_pi_apply (X:=fun _:Site s=>Stamp) t).comp ((storyL Y i S f v).comp (ht i))
 · intro i t; have he:Measurable (fun x:A=> gown (Y.u i) Y.long (U x) (P x i) t):= (measurable_pi_apply (X:=fun _:Site s=>E) t).comp ((stage_m ..).measurable.comp (ht i)); exact he.inv
 intro i t; have he (i:Y.Index)(b:Bool): Measurable (fun x:A=>D x i (b,t)) := (measurable_pi_apply (X:=fun _:Bool×Space s=> Fin 5) (b,t)).comp ((measurable_pi_apply (X:=fun _:Y.Index=> Signs s) i).comp v)
 change Measurable (fun x:A=> planeN Y (D x) i t); unfold planeN; split_ifs; exact he ..; exact he ..
end
namespace Tonic
variable {F:A→ Script Y}(p:Tonic F)
variable {t:ℕ} {u v:ℝ}{H:Herald u v}(C:Sized t H.whole)(g:Ratio c s)
variable (U:A→Bkg s)(h:Measurable U) (B:A→ Blocks Y c)(f:Ratio a s)
include p
lemma code (i:Site s) : Measurable (fun x:A=> (F x).code i):= p.label .. -- tune incl p binder
lemma Xbase : Measurable fun x=> (F x).over:=by
 apply measurable_pi_lambda; intro x; unfold Script.over; dsimp only; split_ifs; exact p.base ..; exact (measurable_of_countable (f:=fun i=>XG i _) ).comp (p.code _) -- tune t from goal
lemma Hbase (x:Site s)(v:ℝ): Measurable (fun t=>(F t).port C x v):=by
 unfold Script.port Script.curv; try dsimp only
 split_ifs
 · let f(i:Fin 5)(u:A):= rosy i ((F u).frame (hr Y x) x) (Script.ramp C (hr Y x) x) v; apply meal (p.code x) f; intro i; unfold f rosy motion congrC; have ht : Measurable (fun u:A=> (F u).frame (hr Y x) x * Mag.center i):= (p.frame ..).mul measurable_const; apply Measurable.comp (g:=fun g:E=> (matter g).val*amend i (Script.ramp C (hr Y x) x) v*(matter g).valᵀ) -- tune Meas.comp args g/f
   · exact Continuous.measurable ((matter_cont.mul continuous_const).mul matter_cont.matrix_transpose)
   exact ht
 · exact p.key ..
 exact (measurable_of_countable (f:=fun i=> TG i _ v)).comp (p.code _)
-- maybe `Blocks` MeasurableSpace` issue, use Countable witness fibers instead if needed
include h
lemma Xbuild (S:Blocks Y c): Measurable fun x=> (F x).XX C g S (U x) f:=by
 apply measurable_pi_lambda; intro x; apply (measurable_pi_apply (X:=fun _:Site s=>Ballot) x).comp ((expandX_m f _).comp (Measurable.prodMk h ?_)); apply measurable_pi_lambda; intro i; change Measurable (fun x:A=> (F x).guardX C g S i); unfold Script.guardX; split_ifs; exact (measurable_pi_apply i).comp (p.Xbase); exact measurable_const
lemma Hbuild (S:Blocks Y c)(i:Site s)(v:ℝ): Measurable fun x=> (F x).HH C g S (U x) f i v:=by
 unfold Script.HH; split_ifs; exact p.Hbase ..; refine Pair.full_cont.measurable.comp (f:=fun x=> ((F x).XX C g S (U x) f i).val) ((continuous_subtype_val (p:=fun x:Vect=> x∈Sphere)).measurable.comp ((measurable_pi_apply (X:=fun _:Site s=>Ballot) i).comp (p.Xbuild C g U h f S))) -- tune
end Tonic
end YM.CF.BProof.Trek
