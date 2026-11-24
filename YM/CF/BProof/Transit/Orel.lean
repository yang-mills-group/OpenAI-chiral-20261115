import YM.CF.BProof.Transit.Action
import YM.CF.Continuum.Winter
import YM.CF.Tye.Spin
import YM.CF.BProof.Physical
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 28000
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
variable {m B N L:Side}{j n:ℕ}{X:GramM (mid m B)}{K:Scree.Loom (mid m B)}
open RG Hom Nacre
abbrev forward (w:Site N): Sweep N:= ⟨1,w,false⟩
namespace Town
local notation "Λ"=>mid m B
abbrev block (T:Sweep N)(x:Orbit N):Orbit N:=(flashA T x.1,bun T x.2)
abbrev costs (w:Site N):UNI (Single N):= siteU (castX (forward w)) false (spinU false 1) N
lemma costs_j :JetS 1 false false (spinU false 1):=by exact Spire.det_i ▸ spinZ false 1 -- rw false everywhere tune
lemma forw (w:Site N) (v:Pane N): flashA (forward w) v=pull 1 ((assembly N).embed w) v:=revoke .. -- tune
lemma walkA (w:Site N): MeasurePreserving (block (forward w)) (city N) (city N):=by
 refine (show MeasurePreserving (flashA (forward w)) _ _ from ?_).prod (tuft _); rw [funext (forw w)]; exact Wilson.prior_pull (1:Signed) ..
lemma irreg (s:Sweep N)(x:Orbit N): block s⁻¹ (block s x)=x:= Prod.ext (revB s _) (tuftT s _)
lemma inv_s (w:Site N):(forward w)⁻¹=forward (-w):=by change Sweep.mk (1:Signed)⁻¹ (-((1:Signed)⁻¹).act w) false=_; rw [inv_one, Signed.act_one] -- tune names

def abbey (w:Site N) : MeasurableEquiv (Orbit N) (Orbit N) :=
 ⟨⟨block (forward w),block (forward w)⁻¹,irreg _,fun x=>by let s:=forward w; change block s _=_; nth_rw 1 [← inv_inv s]; exact irreg s⁻¹ x⟩,(walkA _).measurable,by change Measurable (block (forward w)⁻¹); rw [inv_s]; exact (walkA _).measurable⟩
variable (C' : Hom.Credit)
variable {e v x y z l:ℝ} {hj : Odd L.val}{Y : Pricing j L hj (Thread j)}{P : Grasp Y B e} {Q:Sweep (mid m B) → Prop}
lemma belong (t : Hom.InterestX C' (mid m B) X.J) (h0 : 1 ≤ j) (D : Pearl P) (F : Stamped j L hj Y) (H0 : Roof Λ v e n K) (F1 : IncX Q X.F X.p x y) (F2 : IncX Q X.slip X.p x z) (Fx : Dark Q X.K X.p x l) (w: Site (mid m B))(q: Q (forward w))(V:Orbit (mid m B))(hV:Injective (priorP V.2))(hp:P.roundZ ≤ (mid m B).val): arum (costs w) false false (mateK _) (denZ X P K V)=denZ X P K (block (forward w) V):=by
  let T:= costs w
  let W:=forward w
  let R:= GramM.board X
  let J:=block W V
  let Z:=K V
  have hw : detX W.s=false:=Spire.det_i
  have hu : detX (castX W).s=false:=Spire.det_i
  have hh : JetS W.s W.charge (detX W.s) (spinU false 1):= by rw [hw]; exact costs_j
  have hZ:K J=flashA W Z:=H0.move _ _ _ hV
  have hv: Guard Z e:= H0.paid V
  have h2: Pec.pigment X.J.I (flashA W Z)= Pec.pigment X.J.I Z:= Pec.tolls t.leanJ.2.lead (castX W).t Z
  have h3 : X.path.inChannels X.funds X.p X.beta J.1=X.path.inChannels X.funds X.p X.beta V.1:= by
    change X.path.inChannels _ _ _ (flashA (forward w) V.1)=_; rw [forw]; exact YM.Push.Local.channels_pull ..
  have hf : X.betaL K J=X.betaL K V:= by unfold GramM.betaL GramM.H0; rw [h3,hZ,h2]
  let A:=spar j X.J.M Z; let B':=spar j X.J.M (flashA W Z); have hA : IsStarProjection A:= (P.broadness _ hp X.J.M).projection _ hv
  have hB : IsStarProjection B':= (P.broadness _ hp X.J.M).projection _ (hZ ▸ H0.paid J)
  let L' := paintR false false T
  have ht : L' (R V) = R J:=by
    have hx:= Window.turn_exponent W F1 q hh V.1
    have hy:= Window.turn_exponent W F2 q hh V.1
    have hz:= Window.turn_forced W q hh Fx V.1 V.2 hV
    rw [hw] at hx hy hz; unfold R GramM.board
    letI : NormedAlgebra ℚ (Scree.Cipher Λ):= NormedAlgebra.restrictScalars ℚ ℝ _
    rw [map_mul,map_exp L' L'.toLinearMap.continuous_of_finiteDimensional,map_add]; exact congrArg₂ (·*·) (congrArg exp (congrArg₂ (·+·) hx.symm hy.symm)) hz.symm
  have h4: sings false T A= swapX false B':= funde_f (castX W) inert (spinU false 1) costs_j Z j h0 X.J.M _ (F.fields_one _ (P.needed.trans hp)) (hv.shrink P.gem)
  have h5: Spire.tourP T false false (tank A (R V))=tank B' (R J):=by rw [←ht,tank_eq _ _ hA,tank_eq _ _ hB]; exact appleT hA hB _ _ _ h4 _
  change arum T _ _ _ _=denZ _ _ _ J; unfold denZ; rw [hf,hZ, arum_scale]
  rw [arum_act,h5]
  have hx : arum T false false (mateK Λ) (relV P X.J Z)= relV P X.J (flashA W Z):= by
    let Y':= Hive.birds false D F hp h0 (castX W) (spinU false 1) hh X.J.P t.leanJ.1 t.ready Z hv (M:=X.J.M)
    rw [hu] at Y'; exact Y'
  rw [hx]; rfl
lemma lives (t:Hom.InterestX C' (mid m B) X.J) (h0 : 1 ≤ j) (D : Pearl P) (F : Stamped j L hj Y) (H0 : Roof Λ v e n K) (F1 : IncX Q X.F X.p x y) (F2 : IncX Q X.slip X.p x z) (Fx : Dark Q X.K X.p x l) (w: Site (mid m B))(q: Q (forward w))(U: Obs (mid m B))(hp:P.roundZ ≤ (mid m B).val): Fixed.numerator P X K (move (forward w) U) = Fixed.numerator P X K U :=by
  let s:= forward w; let Z:= denZ X P K; let T:= abbey w; let G (V:Obs (mid m B)) (x: Orbit (mid m B)):= beamZ Λ (acts (V x.1) (Z x))
  change (∫ u,G _ u ∂city Λ)=(∫ u,G _ u ∂city Λ)
  rw [← (show MeasurePreserving T (city Λ) (city Λ) from walkA w).integral_comp' (G (move (forward w) U))]
  apply integral_congr_ae
  refine ((Measure.quasiMeasurePreserving_snd (μ:=prior SU.group (More (mid m B))) (ν:=depot (mid m B))).ae sepT).mono ?_
  intro z hz; have h:= belong C' t h0 D F H0 F1 F2 Fx w q z hz hp
  let Q:=arum (costs w) false false (mateK _); have he:Q (mateK _) = mateK Λ := arum_self (costs _) false false (Tset _) ((touchP _) ▸ tickB _) (tickR (castX s) inert (spinU false 1) costs_j _)
  have hh(moveX:FC (Single Λ)) : teen s moveX= Spire.tourP (costs w) false false moveX:=by change lotB false (detX 1) (costs w) _=_; rw [det_i]; rfl
  change inner ℂ (mateK Λ) (acts (teen s (U (flashA s⁻¹ (flashA s z.1)))) (denZ _ _ _ (block (forward w) z)))=inner ℂ (mateK _) (acts _ _); rw [hh,revB, ← h,←arum_act]; nth_rw 1 [←he]; exact arum_globe _ _ _ (Tset _) ((touchP _) ▸ tickB _) (tickR (castX s) inert (spinU false 1) costs_j _) _ _
end Town
end YM.CF.BProof.Bide
