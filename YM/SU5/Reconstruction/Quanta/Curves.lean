import YM.SU5.Reconstruction.Quanta.Epicycles
import YM.SU5.FiniteGaugeData.Tower.Baggage
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-! # Lift the actual POS witnesses even odd. Resolution keeps parity upon transfer. -/
open QuantaCore NorthTapes
namespace Garret
variable {g₀:Bool}{S Z:Finset Cover}{f g:Family (tent Y H)}
local notation "W" =>wingspan Λ l
local notation "B" => Λ.block
local notation "L"=>Λ.R.L.val

variable (a:Axis)(z:ℤ)
local notation "W₀" t:max=> volumeAround Λ l t
local notation "v₀" q:max =>((Λ.R.L.val:ℤ)^q*z)
local notation "Pm" z:max => poleForm K a z
variable {a₀ b:ℕ→ℕ}{D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q: Coherent (i:=i) (k:=k) (E:=E) Y H D a₀ b)
local notation "π₀" r:max=>i (a₀ r)
local notation "κ" r:max=>k (b r)
local notation "tr" r:max t:max S:max F:max=> train Y H s t (π₀ r) (κ r) S F
local notation "Qr" r:max g:max S:max f:max t:max=> quarry Y H s (π₀ r) (κ r) g S f t
local notation "Ft" k:max S:max g:max p:max=> InTest K true ((W₀ k) S) g p
local notation "hv" t:max m:max => ((tent Y H).c (momentm Y m t))

include V
open SlabMark Fock
lemma trend {f':ℕ→Family (tent Y H)}(p:BQueue S f' f): Tendsto (fun n=> E s (f' n)) atTop (𝓝 (E s f)):=by
 let v:= toll Y H s S; have t:0≤v:=(toll_pays Y H s S).1
 apply Metric.tendsto_nhds.mpr; intro e h; let b:=e/(v+1); have hb:0<b:=by unfold b; positivity
 filter_upwards [p.saved b hb] with n hx
 rw [dist_eq_norm,← E_sub Y H V s (aux_test (p.whereTo n)) (aux_test (p.landing))]; refine (E_bound Y H V s S (InTest.subOp (p.whereTo n) p.landing) hx).trans_lt ?_

 have he:b*(v+1)=e:= div_mul_cancel₀ e (by positivity); change v*b<e; nlinarith
omit V
-- feasible arrays, without assuming transfer of odd X itself converges
include Q
lemma family_train {n:ℕ}(p:InTest K true S false f): BQueue ((W₀ n) S) (fun r=> tr r n S f) (stream Y H D s n f):=by
 obtain ⟨v,t⟩:= Journey.valuation Y H p; obtain ⟨A,h,Broadcast⟩:= Tower.fares Y H s Q S n
 have ht:pay f (v+1):=fun a x=>(t a x).trans (by linarith); have hh:0<v+1:=by have h:0≤v:=pay_nonneg (show pay f v from t); linarith
 refine ⟨fun k=>Tower.prepared_train Y H s S n _ _ p,(proceeds Y H Q.circuit s n p).1,⟨A*(v+1),mul_pos h hh,?_⟩, fun e he=>?_⟩
 · constructor;· obtain ⟨i,h⟩:=(Broadcast 1 zero_lt_one).exists; exact (h _ p _ ht).1
   exact (Broadcast 1 zero_lt_one).mono fun r h=>(h _ p _ ht).2.1
 filter_upwards [Broadcast (e/(v+1)) (by positivity)] with r t
 exact (div_mul_cancel₀ e hh.ne') ▸ (t _ p _ ht).2.2.1
omit Q
lemma left_comm {J:Calibration}{f g:Family J}(p:InTest J true S g₀ f)(q:InTest J true Z false g):f*g=g*f:= by
 funext m x; have he:= ((p.support m).mono (subset_univ _)).allV x; have h:= ((q.support m).mono (subset_univ _)).allV x; change f m x*g m x=g m x*f m x; rw [he.sign_com h]; simp [Sector.grainB]
lemma party {J:Calibration}{f g:Family J}(p:InTest J true S g₀ f)(q:InTest J true Z false g) :
 mirror J a z g * poleForm J a z g₀ f f * g=poleForm J a z g₀ (f*g) (f*g):=by
 unfold poleForm; rw [mirror_times,Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
 let t:=mirror J a z f; let y:=mirror J a z g; have h : t*y=y*t:=left_comm (axial J a z p) (axial J a z q)
 refine congrArg (fun u : Family J => Reflect.chord g₀ • u) ?_
 change y*(t*f)*g=t*y*(f*g)
 rw [←mul_assoc y,←h,mul_assoc (t*y)]
lemma law_present (p:InTest K true S false f): BQueue S (fun _=>f) f:=by
 obtain ⟨v,h⟩:= valuation Y H p; have hh:= pay_nonneg (show pay f v from h)
 exact BQueue.stay p (show 0<v+1 by linarith) (fun x a=> (h x a).trans (by linarith))
include V Q
local notation "z₀"=> Heat.gaugeShift Λ.block z
lemma equipped (n:ℕ)(U:Finset Cover)(u:InTest K true S g₀ f)(v:region a (Heat.gaugeShift Λ.block z) ((K).ℓ) S)
    (y:InTest K true Z false g)(w:region a ((Λ.R.L.val:ℤ)^n*(Heat.gaugeShift Λ.block z)) (reserve Λ l) Z)
    (p: InTest K true U false ((Pm z₀) g₀ f f)):
    0 ≤ E (s+n) (mirror K a ((Λ.R.L.val:ℤ)^n*(z₀)) g * stream Y H D s n ((Pm z₀) g₀ f f) * g) :=by
 let a':ℤ:=(Λ.R.L.val:ℤ)^n*(z₀)
 let h':=law_present Y H y; have h:= ((BQueue.revolve a a' h').multiply (family_train Y H s Q (n:=n) p)).multiply h'
 apply ge_of_tendsto (trend Y H V (s+n) h); filter_upwards [living Y H V s S Q n,reaches Y H V s S a z₀ Q U n v] with r iT sT
 let X:= Qr r g₀ S f n; have ht:InTest K true ((W₀ n) S) g₀ X:= iT _ le_rfl f _ u; let i':=(π₀ r); let k':=(κ r)
 change 0 ≤ E (s+n) (mirror K a a' g * train Y H s n i' k' U ((Pm z₀) g₀ f f)*g)
 rw [sT g₀ f f u u p, party a a' ht y]
 let L':= (W₀ n) S ∪ Z; let e:InTest K true L' g₀ (X*g):=by simpa using (InTest.mul (ht.mono subset_union_left) (y.mono subset_union_right) : InTest K true L' _ (X*g)) -- notation union fix
 have he:region a a' (reserve Λ l) L':=fun x t=>(Finset.mem_union.mp t).elim (parades Y H a z₀ v n x) (w x)
 let b':ℤ:= (Λ.R.L.val:ℤ)^n*z; have ha:a'=Heat.gaugeShift Λ.block b':=by unfold a' b' Heat.gaugeShift; ring
 change 0 ≤ E (s+n) (poleForm (tent Y H) a a' g₀ (X*g) (X*g)); rw [ha] at he ⊢; exact election0 Y H V (s+n) a b' e he
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.family_train
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.equipped
