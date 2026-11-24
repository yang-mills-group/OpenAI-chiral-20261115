import YM.CF.Continuum.Winter
import YM.CF.Salt.Step
import YM.CF.Mica.Slide
import YM.CF.Cour.EdgeC
import YM.CF.Buffered.StepIdentity
import YM.CF.Urn.Role
/- Advance to arbitrary Sweeps and charge. Based on Winter.relative beta. X1 exact. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered
open Filter Function NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Reef
variable {m B N L : Side} {σ Cκ Λ' e v x y z η:ℝ} {j n:ℕ} {hj:Odd L.val} {Y:Pricing j L hj (Thread j)}
local notation "Λ"=>CSide m B
variable {P:Grasp Y B e}{X:GramM (mid m B)}{K:Scree.Loom (mid m B)}
namespace Jubilee
lemma channelsH (R:PathData SU.group)(p:BudgetPoint){c:Clip}(t:R.Bounds c σ Cκ Λ')(h:Rare R)(W:Sweep N)(V:Pane N)(β:ℝ): R.inChannels c p β (flashA W V)= R.inChannels c p β V:=by
 have hs(Z: Pane N): R.inChannels c p β (echo Z)= R.inChannels c p β Z:=by
    unfold PathData.inChannels PathData.principal; simp_rw [echo_p,Beau.base_K p R t,Beau.place_v p _ (fun i=>(h i).2.1),Beau.place_v p _ (fun i=>(h i).2.2),Beau.place_v p _ (fun i=>(h i).1)]
 let Z:= pull W.s ((assembly N).embed W.b) V
 have hh:R.inChannels c p β Z=R.inChannels c p β V:= YM.Push.Local.channels_pull ..
 rw [revoke]; generalize W.charge=b; cases b; exact hh; exact (hs Z).trans hh
abbrev Rot (W:Sweep N)(A:Orbit N): Orbit N:= (flashA W A.1,bun W A.2)
abbrev Twin(W:Sweep N)(u:UNI SpinIdx):= prepU (castX W) u (xtra W.charge) N
variable {Q:Sweep (mid m B)→Prop} (C': Hom.Credit) (t:Hom.InterestX C' (mid m B) X.J)(p:Pearl P)(F:Stamped j L hj Y) (h0: 1≤ j) (H0:Roof (mid m B) v e n K)(F1:IncX Q X.F X.p x y)(F2:IncX Q X.slip X.p x z)(Fx:Dark Q X.K X.p x η)(w:Sweep (mid m B))(uV:Q w)(u:UNI SpinIdx)(hu:JetS w.s w.charge (detX w.s) u)(tB:X.path.Bounds X.funds σ Cκ Λ')(rB:Rare X.path)(hp:P.roundZ ≤ (mid m B).val)
include p F h0 H0 F1 F2 Fx uV hu tB rB hp t
local notation "Tmp"=> Twin w u
local notation "ΛV"=> arum Tmp w.charge (detX w.s) (mateK Λ)
abbrev sign(W:Sweep N):= cSignX (W.charge.xor (detX W.s))
lemma FBand (V:Orbit Λ)(hV:Injective (priorP V.2)): ΛV (Complex.exp (-X.v) • denZ X P K V)= Complex.exp (-X.v) • denZ X P K (Rot w V):=by
  let T := Twin w u; let R := GramM.board X; let J:=Rot w V; let Z:=K V
  have hZ:K J=flashA w Z:=H0.move _ _ _ hV; have hv: Guard Z e:= H0.paid V
  have h2: Pec.pigment X.J.I (flashA w Z)= sign w (Pec.pigment X.J.I Z) := Cour.portPartH X.J.I t.leanJ.2.lead t.tilt (castX w) w.charge Z
  have h3 : X.path.inChannels X.funds X.p X.beta J.1=X.path.inChannels X.funds X.p X.beta V.1:= channelsH X.path _ tB rB w V.1 X.beta
  let NL:= X.betaL K V-X.v; let NL':= X.betaL K J-X.v
  have hf : NL'=sign w NL := by unfold NL' NL GramM.betaL GramM.H0; rw [h3,hZ,h2]; unfold sign; generalize w.charge.xor (detX w.s)=b; cases b; rfl; simp [cSignX]; ring_nf; first | rfl | done
  let A:=spar j X.J.M Z; let B':=spar j X.J.M (flashA w Z); have hA : IsStarProjection A:= (P.broadness _ hp X.J.M).projection _ hv
  have hB : IsStarProjection B':= (P.broadness _ hp X.J.M).projection _ (hZ ▸ H0.paid J)
  let W' := paintR w.charge (detX w.s) T
  have ht : W' (R V) = R J:=by
    unfold R GramM.board
    letI : NormedAlgebra ℚ (Scree.Cipher Λ):= NormedAlgebra.restrictScalars ℚ ℝ _
    rw [map_mul,map_exp W' W'.toLinearMap.continuous_of_finiteDimensional,map_add]; exact congrArg₂ (·*·) (congrArg exp (congrArg₂ (·+·) (Window.turn_exponent w F1 uV hu V.1).symm (Window.turn_exponent w F2 uV hu V.1).symm)) (Window.turn_forced w uV hu Fx _ _ hV).symm
  have h4: sings w.charge T A= swapX (detX w.s) B':= funde_f (castX w) _ u hu Z j h0 X.J.M _ (F.fields_one _ (P.needed.trans hp)) (hv.shrink P.gem)
  have h5: Spire.tourP T w.charge (detX w.s) (tank A (R V))=tank B' (R J):=by rw [←ht,tank_eq _ _ hA,tank_eq _ _ hB]; exact appleT hA hB _ _ _ h4 _
  have he(M : Orbit Λ): Complex.exp (-X.v) • denZ X P K M=Complex.exp (X.betaL K M-X.v) • acts (tank (spar j X.J.M (K M)) (R M)) (relV P X.J (K M)) :=by
    unfold denZ; rw [smul_smul,←Complex.exp_add]; congr 2; ring_nf
  change arum T _ _ _ _=_ • denZ _ _ _ J; rw [he,he,arum_scale,show X.betaL K J-X.v= _ from hf,hZ, arum_act,h5]
  have hx : arum T w.charge (detX w.s) (mateK Λ) (relV P X.J Z)= relV P X.J (flashA w Z):= Hive.birds w.charge p F hp h0 (castX w) u hu X.J.P t.leanJ.1 t.ready Z hv (M:=X.J.M)
  rw [hx]; congr 1; unfold sign; generalize w.charge.xor (detX w.s)=b; cases b; rfl; exact Eq.symm (Complex.exp_conj _)
omit p F h0 H0 F1 F2 Fx uV hu tB rB hp t
-- measure
lemma latticeFieldEstimates (W:Sweep N): MeasurePreserving (Rot W) (city N) (city N):=(Salt.flash_p W).prod (tuft W)
lemma revt (W:Sweep N)(V:Orbit N): Rot W⁻¹ (Rot W V)=V:= Prod.ext (revB W _) (tuftT W _)
abbrev mart (W:Sweep N):Orbit N≃ᵐOrbit N:= ⟨⟨Rot W, Rot W⁻¹,revt W,by intro V; change Rot W (Rot W⁻¹ V)=V; nth_rw 1 [← inv_inv W]; exact revt ..⟩,(latticeFieldEstimates _).measurable, (latticeFieldEstimates _).measurable⟩
lemma volt_e (W:Sweep N) (g:Orbit N→ℂ):sign W (∫ x,g x∂city N)=∫ x,sign W (g x)∂city N:=by unfold sign; generalize W.charge.xor (detX W.s)=b; cases b; rfl; exact Eq.symm integral_conj
lemma ex_P {I:ℂ}(F: Mark Λ)(Xq:Orbit Λ→Phys Λ): markedRead F K (fun i=> I • Xq i)= I*markedRead F K Xq :=by unfold markedRead letterRead; simp_rw [ContinuousLinearMap.comp_apply,map_smul,smul_eq_mul]; exact integral_const_mul ..
include p F h0 H0 F1 F2 Fx uV hu tB rB hp t
-- relation prices enough. Including non Fine, no Envelope needed here even.
lemma price_R (g H: Mark Λ)(pW:∀ x: Orbit Λ,Injective (priorP x.2)→ H ((Rot w x).1,K (Rot w x)) = Spire.tourP Tmp w.charge (detX w.s) (g (x.1,K x))):
 Complex.exp (-X.v)*markedRead H K (denZ X P K)=sign w (Complex.exp (-X.v)*markedRead g K (denZ X P K)):=by
 rw [← ex_P H,←ex_P g]; let U'(x):=Complex.exp (-X.v) • denZ X P K x
 let V(f:Mark Λ)(x:Orbit Λ):=letterRead (f (x.1,K x)) (U' x); change (∫ x,V H x∂city _)= sign w (∫ x,V g x∂city _)
 rw [← (show MeasurePreserving (mart w) _ _ from latticeFieldEstimates w).integral_comp' (V H),volt_e]
 apply integral_congr_ae; refine ((Measure.quasiMeasurePreserving_snd (μ:=prior SU.group (More Λ)) (ν:=depot Λ)).ae sepT).mono ?_
 intro x h; have he:ΛV (mateK Λ)=mateK Λ := arum_self Tmp w.charge (detX w.s) (Tset Λ) ((touchP Λ) ▸ tickB Λ) (tickR (castX w) _ u hu _)
 change inner ℂ (mateK Λ) (acts (H ((Rot w x).1,K (Rot w x))) (U' (Rot w x)))=sign w (V g x)
 rw [pW _ h, ← show ΛV (U' x)= U' (Rot w x) from FBand C' t p F h0 H0 F1 F2 Fx w uV u hu tB rB hp x h,←arum_act]; nth_rw 1 [←he]; exact arum_globe Tmp w.charge (detX w.s) (Tset Λ) ((touchP Λ) ▸ tickB _) (tickR (castX w) _ u hu Λ) _ _
omit p F h0 H0 F1 F2 Fx uV hu tB rB hp t
lemma volt_one (W:Sweep N)(U:UNI SpinIdx): Spire.tourP (Twin W U) W.charge (detX W.s) 1 = 1:=map_one (Urn.lotB _ _ _)
lemma sign_div (W:Sweep N)(x y:ℂ):sign W (x/y)= sign W x/sign W y:=by unfold sign; generalize W.charge.xor (detX W.s)=b; cases b; rfl; exact map_div₀ (starRingEnd _) x y
include p F h0 H0 F1 F2 Fx uV hu tB rB hp t
lemma tray (g H:Mark Λ)(pW:∀ x: Orbit Λ,Injective (priorP x.2)→ H ((Rot w x).1,K (Rot w x)) = Spire.tourP Tmp w.charge (detX w.s) (g (x.1,K x))):
 markedRead H K (denZ X P K) / partitionZ X P K=sign w (markedRead g K (denZ X P K) / partitionZ X P K):= by
 let A (W:Mark Λ):= markedRead W K (denZ X P K); let Z:= partitionZ X P K; let c:=Complex.exp (-X.v); have hs:∀ x:ℂ,c*x/(c*Z)=x/Z:=fun x=>mul_div_mul_left _ _ (Complex.exp_ne_zero _)
 have he:A 1=Z:= markvac K _
 have h:=price_R C' t p F h0 H0 F1 F2 Fx w uV u hu tB rB hp
 have hz:c*Z=sign w (c*Z):=by rw [←he]; exact h 1 1 fun x _ => (volt_one ..).symm
 change A H / Z=sign w (A g/Z); rw [←hs,←hs (A g), sign_div,← hz]; exact congrArg (fun x:ℂ=> x/(c*Z)) (h _ _ pW)
end Jubilee
end YM.CF.Buffered
end
