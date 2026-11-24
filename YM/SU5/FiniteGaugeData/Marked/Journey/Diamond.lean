import YM.SU5.FiniteGaugeData.Marked.Journey.Adopt

/-!
# If using with `Printed`, can keep the very same E at observing zero (on
identified arguments). This version can route ALL resolutions together on
the common period/cutoff process, by at most dropping a finite UV prefix
(the finite prefix is just so every selected cone point can be a true read
on the `Printed` in the type of the Gram application).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Burn Coupling
variable {Λ:Preparation}{l:ℕ}{Y:Course Λ (VolumeCape.Dream.Nimbus l)}{h:Real.exp 1 ≤ Λ.x}
local notation "K₀"=>tent Y h
variable {K:Calibration} {C:Conveyor K}{J:Tiling K}{V:SpanCal K}(W:Printed K C J V)
variable {u π i k:ℕ→ℕ}(a:StrictMono u)(b:StrictMono π)(e:StrictMono i)(f:StrictMono k)
variable {I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}(P: Universal Y h (u∘i) (π∘k) I E)
variable (S:Coupling.Schedule K C Λ Y u π)
local notation "H"=>W.narrative.hist

lemma usher : ∀ᶠ n:ℕ in atTop,∀ m:Side,K.takes m → m.val^5 ≤ n → Wick H m n:= by
  filter_upwards [eventuallyWick H,K.sides] with n g x m v y
  exact g m ⟨v,x.2 m v (y.trans' (by simpa using (pow_le_pow_right₀ (by have e:m.val ≥ 1:=m.property; omega : 1 ≤ m.val) (show 1≤5 by omega)))),y⟩

include W P a b e f S
lemma compose_stage :
    ∃ k' A, ∃ P':Process K, Stage W Y u π S P' i (k∘k') A ((E 0) ∘ adopt h S)
                 ∧ Universal Y h (u∘i) (π∘k∘k') I E := by
  let c:=S.carried W a b; let v:=c.cut ∘ k; let g:=c.volume ∘ i
  have hM:Tendsto v atTop atTop:= (c.uv.comp f).tendsto_atTop
  obtain ⟨N,N'⟩:= eventually_atTop.mp (hM.eventually (usher W))
  let k'(x:ℕ):= N+x; have k'v: StrictMono k':=by intro x y t; exact Nat.add_lt_add_left t _
  let A:= v ∘ k'; let P': Process K:=⟨g,fun r=> c.admitted _,c.v_grows.comp e.tendsto_atTop,fun _=> A,fun _=> hM.comp k'v.tendsto_atTop⟩
  have hu (x y:ℕ)(u':(P'.m x).val^5 ≤ A y): (Y.voyage (u (i x))).kick ≤ π (k (k' y)) ∧ Wick H (P'.m x) (A y) := by
    exact ⟨P.pick.ticket x (k' y) u', N' (k' y) (Nat.le_add_right ..) (P'.m x) (P'.sides x) u'⟩
  let Ea:= (E 0) ∘ adopt h S
  have received (F:Family K)(z:TestFamily K true F)(x y:ℕ)(t:(P'.m x).val^5 ≤ A y): P'.atUV H x y F=sharp Y h 0 (u (i x)) (π (k (k' y))) (adopt h S F) :=
    (((Schedule.mains W S (i x) (k (k' y)) (hu x y t).1 (hu x y t).2).2.2 F z).2.trans (home_score h S ..))
  have roll {X:Type} [PseudoMetricSpace X]{G': ℕ→ℕ→X}{F z}(t:Couplet (u∘i) (π∘k) G' F z (fun t=>∀ᶠ r in atTop,legacy Y (u (i r)) (π (k (t r))))): Couplet (u∘i) (π ∘ k ∘ k') G' F z (fun v=> ∀ᶠ r in atTop,legacy Y (u (i r)) (π (k (k' (v r))))) := ⟨fun x=> (t.inner x).comp k'v.tendsto_atTop,t.periods,fun v=> t.paths (k' ∘ v)⟩ -- remove s
  let Q:Cabinet Y h (u∘i) (π∘k∘k'):= ⟨P.pick.grow_i,P.pick.grow_k.comp k'v,fun x y=> P.pick.ticket x (k' y),fun s T U X'=>by obtain ⟨Z,z,V⟩:=P.pick.prices s T U X'; exact ⟨Z,z,roll V⟩⟩
  let QQ: Universal Y h (u ∘ i) (π ∘ k ∘ k') I E:= ⟨Q,fun s v h=>roll (P.together s v h),P.gaugeMatter⟩
  let needs: Settled H P' true Ea:= {
    convergence := fun F h'=> by
      have X':= QQ.together 0 _ (broad h S h')
      exact ⟨(I 0 (adopt h S F))∘u∘i,Eventually.of_forall (fun r=> (X'.inner (u (i r))).congr' ((P'.grows_n r|>.eventually_ge_atTop ((P'.m r).val^5)).mono fun x y=> (received F h' r x y).symm)),X'.periods⟩
    joint := fun _=> ⟨A,rfl,fun F t e pV=> ((QQ.together 0 _ (broad h S t)).paths e pV).congr' (pV.mono fun _ z=> (received F t _ _ z).symm)⟩ }
  refine ⟨k',A,P',⟨rfl,rfl,rfl,(c.uv.comp f).comp k'v,e,f.comp k'v,c.ir.comp e,needs,?_⟩,QQ⟩
  intro x y z T U L M N C X R
  exact ⟨(hu x y z).1,(hu x y z).2.allowed,(Schedule.mains W S (i x) _ (hu x y z).1 (hu x y z).2)⟩

omit W P a b e f S
/-- Full receipt, same E (typecast of level 0 `E` from elected FiniteGaugeData limits)
for Gram and all Borel insertion products on the eligible domain. Direct route
at all observing resolutions on the same scales. Finite docket includes
actual *wide* observable (even CAR on joint link data) signed numerator and
actual nonzero partition. No factorization into generations.

Reminder `K C J V W ID` section per FiniteGaugeData interface still input here. See Both,
Schedule. If asked to apply the buffered theorem to a specific elected set of
heat histories as well, the calibration assignment must issue `Both` or
similar with the heat matches; the direct convergence / `Settled` and Gram
application only needs its `Schedule`, i.e. the Printed K/C/etc supplied on
these very actual (sharp) histories, with the same reconstruction and
denominator.
-/
theorem diamond (ε:ℝ):
    ∃ (Λ:Preparation)(l:ℕ), ε < Λ.x ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (h:Real.exp 1 ≤ Λ.x),∃ (Y : Course Λ (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=Λ.δ) Λ.V Λ.W Λ.J Λ.N0 z Λ.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared Λ.P Λ.delay) ∧
        (∀ i j:ℕ, Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ u π:ℕ→ℕ, StrictMono u ∧ StrictMono π ∧ Nonempty (Y.Query u π) ∧
          ∃ i k I E, StrictMono i ∧ StrictMono k ∧ Universal Y h (u∘i) (π∘k) I E ∧
            ∀ (K:Calibration)(C:Conveyor K)(J:Tiling K)(V:SpanCal K)(W:Printed K C J V)(S:Coupling.Schedule K C Λ Y u π),
              let Ea:= (E 0) ∘ adopt h S
              ∃ (k' A:ℕ→ℕ)(P:Process K), Stage W Y u π S P i (k∘k') A Ea ∧ Universal Y h (u∘i) (π∘k∘k') I E ∧
                E 0 1=1 ∧ Ea 1=1 ∧ ∀ n:ℕ, ∀ F:Fin n→eligible K true, (Matrix.of fun i j=> Ea (thetaK K (F i).val*(F j).val)).PosSemidef := by
  obtain ⟨Λ,l,P0,P1,x,Y,P3,P4,P5,f,g,P2,K0,k0,i,k,I,E,P6,P7,A⟩:=daybreak ε
  refine ⟨Λ,l,P0,P1,x,Y,P3,P4,P5,f,g,P2,K0,k0,i,k,I,E,P6,P7,A,fun K C J V W S=>?_⟩
  obtain ⟨u,v,P,D,H'⟩:= compose_stage W P2 K0 P6 P7 A S
  intro Z
  exact ⟨u,v,P,D,H',(H'.gaugeMatter 0).1,D.settled.value,fun _ F=> (Concert.gram W D.settled F).2⟩
end YM.CF.Buffered.Afterglow.Journey
#print axioms YM.CF.Buffered.Afterglow.Journey.diamond
