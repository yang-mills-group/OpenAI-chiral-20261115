import YM.CF.Vp929.Roof.Braid
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Guide MeasureTheory Palace Mos Mesa Cube Lat Skye Read Cane Spire Scroll Laurent Paper SU
open scoped Topology Classical NNReal Matrix.Norms.Frobenius
variable (C:Side)(K:ℕ→ℝ)(n:Side)(p:2*(spanR* Bolt C)<(More n).val)
variable (r:ℕ)(u d:ℝ)
namespace Braid
variable {I:Type*}(Q:I→Pane n→Pane n)(samp:Finset (Seat n)→ℝ→I)
variable (h:∀ i,Basic n (Q i) u d r)(sw:∀ (S:Finset (Seat n))(t:Sweep n),samp (S.map (boxA t).symm.toEmbedding)=samp S)
variable [Fintype I][MeasurableSpace I][MeasurableSingletonClass I](M:∀ i,Measurable (samp i))
lemma flash_pick(U:Finset (Seat n)):Measurable fun x:Ids n=> x (greet U (priorP x)):=by
 exact mealM (F:=fun x:Ids n=>greet U (priorP x)) (fun i=>((mastM _).comp primeV) (measurableSet_singleton i)) (G:=fun i x=> x i) (fun i=> measurable_pi_apply i)
include h M
lemma measT(U:Finset (Seat n)):Measurable fun x:Orbit n=>sprout n Q samp U x.2 x.1:=by
 let v(x:Orbit n):=x.2 (greet U (priorP x.2)); have ht:Measurable v := (flash_pick n U).comp measurable_snd; let A(x:Orbit n): I× Sweep n:= (samp U (v x).1,(v x).2.1); have he:Measurable A:= ((M U).comp (measurable_fst.comp ht)).prodMk (measurable_fst.comp (measurable_snd.comp ht))
 exact mealM (F:=A) (fun i=>he (measurableSet_singleton i)) (G:=fun i x=> mend (Q i.1) i.2 x.1) (fun i=> (mine (h i.1) i.2).meas.comp measurable_fst)
lemma meterV(V:Finset (Seat n)):Measurable fun x:Orbit n=> join n r Q samp V x.2 x.1:=by
 apply measurable_pi_lambda; intro e; unfold Braid.join; split; · exact (measurable_pi_apply e).comp (measT n r u d Q samp h M _)
 exact (measurable_pi_apply e).comp measurable_fst
lemma meterP: Measurable fun x:Orbit n=> story n r u Q samp x.1 x.2:=by
 exact mealM (F:=fun x:Orbit n=> RG.flags u x.1) (fun i=>measurable_fst (RG.flags_measurable_eq ..)) (G:=fun i x=> join n r Q samp i x.2 x.1) (meterV n r u d Q samp h M)
omit h M
lemma gaugesM: Measurable fun x:(Seat n→SU.E)× Pane n=> Lattice.gauge x.1 x.2:=by apply Continuous.measurable; apply continuous_pi; intro i; simp only [Lattice.gauge]; fun_prop
lemma framing : Measurable (@frameP n) := measurable_pi_lambda _ fun i=> measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))
include h M
lemma springM:Measurable (spring n r u Q samp):=by
 let v(x:Orbit n):=frameP x.2; have ht:Measurable v:=(framing n).comp measurable_snd; let b(x:Orbit n):=(gauge (v x) x.1,x.2); have hb:Measurable b:= ((gaugesM n).comp (ht.prodMk measurable_fst)).prodMk measurable_snd
 have e:Measurable (fun x:Orbit n=> (frameP x.2)⁻¹):= measurable_pi_lambda _ fun i=> ((measurable_pi_apply i).comp ht).inv
 let F(x:Orbit n):=((v x)⁻¹,(fun y:Orbit n=> story n r u Q samp y.1 y.2) (b x)); have E:Measurable F:= e.prodMk ((meterP n r u d Q samp h M).comp hb)
 rw [show spring n r u Q samp=(fun x: (Seat n→SU.E)× Pane n=> Lattice.gauge x.1 x.2) ∘ F from rfl]; exact (gaugesM n).comp E
include sw
lemma springH[Nonempty I](v:ℝ)(p:∀A:Pane n,RG.flags d A=∅→ Guard A v): Roof n u v r (spring n r u Q samp):=by
 refine ⟨fun x=>p _ ?_,springM n r u d Q samp h M, fun V a g=> springG ..,fun V X s=> springV n r u Q samp sw V X s, fun V a i=> springLamp n r u Q samp V a i, fun V W t z X S=>transmis n r u d Q samp h V W t z X S ⟩
 unfold spring; rw [RG.gauge_flags]; apply paysV _ r u _ Q samp h
end Braid
end YM.CF.VolumeCape
