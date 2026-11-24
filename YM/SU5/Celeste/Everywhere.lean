import YM.SU5.Celeste.Honor
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "Z"=> P.par
local notation "Q"=> P.par.block
local notation "Ticket"=> Lamour.Bridge.Celeste.Voice
local notation "oneT"=> Lamour.Bridge.Celeste.Voice.one
open Lamour.Bridge.Celeste.Morn
open Tapestry.Altitude
open Ballad CF.Pannier.Chancel FixedProbe
variable {z e u:ℝ}(s:ℕ)(A:Gaze P.par.block 4 (reserve P.par P.width) z)(w:P.Spectrum0 3)
local notation "Φ" x:max=> P.tuneK (Morn.Holds (Q) A.hair x)
def canyon : Fin 1 → Cover:=fun _=> Morn.death (P.par.block) A.hair -- parameter A? yes
abbrev skyC : Finset Cover := (rayL P.par.block A.hair).patio
noncomputable def authority(x:Lead.Clan):P.Test:= ((purePrice x:ℂ)⁻¹) • Φ x
lemma cross_paid(x:Lead.Clan): (P.authority A x).val∈ observ P.calibration (P.skyC A) false:= by
 let F:= (Holds Q A.hair x).hushed (purePrice x:ℂ)⁻¹; exact ⟨F.1.narrow _,fun _=> F.2 _⟩
noncomputable def maybeTest(x:Lead.Clan):KernelTest P.run P.large:=⟨(P.authority A x).val,(P.authority A x).property,fun _=> ((obs_in ..).1 (P.cross_paid A x)).2⟩
-- wires in all types explicit to avoid parser. 
lemma hitPhase (p:P.Pulsating (P.otherSpectrum 3 3 w) s A e)(q:0<e)(v:∀ i:Lead.Clan, Medal.SharpEnough i e)(x:SU.Slot): ∀ j:Axis, P.Retained j s (P.otherSpectrum 3 j w) (P.canyon A) (P.skyC A) x (P.authority A (Window.family x)):=by
 let V:=Window.family x; have ht:0<separationR P.par.block A.hair:=Nat.mul_pos (Nat.mul_pos (by decide) P.par.block.property) A.bright; intro j; let b:=P.otherSpectrum 3 j w; let u:=P.otherSpectrum 3 3 w
 refine P.retention j s b _ _ _ (fun i j _=>Subsingleton.elim i j) _ (Submodule.smul_mem (Filigree _ _ _ _) (purePrice V:ℂ)⁻¹ ?_) (P.cross_paid A V) ?_
 · exact shinesFil (rayL Q A.hair) V ht P.calibration
 change 1/8 < ‖P.singleState j s b _‖; unfold b; rw [P.single_agrees, ← P.single_agrees (k:=3)]; -- binders check
 unfold authority; rw [map_smul,smul_eq_mul]; exact lt_of_lt_of_le (by norm_num : (1:ℝ)/8<1/4) (Medal.strong_l V (P.singleState 3 s u (Φ V)) q (P.θSingle_u u s A V p) (v V)) -- adapt
lemma homeLinear (x y:P.Test)(c:ℂ): P.E s (x+c • y).val=P.E s x.val+c*P.E s y.val:= by
 let Ψ:=P.groundZero 3;
 rw [←P.occupied 3,←P.occupied 3,←P.occupied 3,← P.at_label,←P.at_label,←P.at_label,map_add,map_smul]; change inner ℂ Ψ ((P.reading 3 s x).val Ψ + c • (P.reading 3 s y).val Ψ)= _; rw [inner_add_right,inner_smul_right]
lemma truthOne : P.E s (1:P.Test).val=1:= P.law.gaugeMatter s|>.1
lemma linear (x:P.Test)(c:ℂ) : P.E s (c • x).val=c*P.E s x.val:= by
 have ht:= P.homeLinear s 0 x c; rw [zero_add] at ht; rw [ht]; have hz:P.E s (0:P.Test).val=0:=by rw [← P.occupied 3, ← P.at_label,map_zero]; exact inner_zero_right _; -- solver goal ambiguity
 rw [hz,zero_add]
lemma unselected_win (v:∀ i:Trinity, ‖P.E s (P.tuneK (A.price i)).val‖≤ e)(p:0<e)(u:∀ i:Lead.Clan, Medal.SharpEnough i e)(x:Lead.Clan): 1/4 ≤ ‖P.E s (P.authority A x).val‖:=by
 let z:=P.E s (Φ x).val; unfold authority; rw [linear]; apply Medal.strong_l x z p _ (u _); have he:= v (Sum.inl true,x); rw [P.chooseOne,sub_eq_add_neg,←neg_smul,P.homeLinear,P.truthOne,mul_one,← sub_eq_add_neg] at he; exact he
lemma addressPaid (x:P.Spectrum0 3) (k:ℕ)(v:Lead.Clan)(N:ℕ) (q: Carries P.run P.large P.law s P.projection (P.maybeTest A v) (P.skyC A) N): pinhole P.Test s (P.authority A v)∈ well P.par P.calibration P.width false (cabin N) Set.univ := by
 let F:= (Holds Q A.hair v).hushed (purePrice v:ℂ)⁻¹; refine oneSlotWell _ P.calibration _ _ _ _ s (Set.mem_univ s) ⟨P.skyC A,((obs_in ..).1 (P.cross_paid A v)).1,q.keepsSize 0⟩ ?_
 exact P.celebrity F
/-- for ALL 6 clans in **same χ**. Actual motion HERE in τ. need rotation restoration & locality still; cf companion PHASE notes. -/
def Intact (x:SU.Slot)(e:ℝ): Prop :=
 let V:=Window.family x;
 AnchorGap (Λ:=P.par) s (P.canyon A) (P.skyC A) ∧
 P.TrinityState (P.otherSpectrum 3 3 w) s A e V ∧
 1/4 ≤ ‖P.E s (P.authority A V).val‖ ∧
 (∃ N:ℕ,pinhole P.Test s (P.authority A V)∈ well P.par P.calibration P.width false (cabin N) Set.univ ∧
 Carries P.run P.large P.law s P.projection (P.maybeTest A V) (P.skyC A) N) ∧
 1/8 < ‖P.spirits R 3 w (pinhole P.Test s (P.authority A V))‖ ∧
 (∀ j:Axis, P.Retained j s (P.otherSpectrum 3 j w) (P.canyon A) (P.skyC A) x (P.authority A V))
theorem participants (v:∀ i:Trinity, ‖P.E s (P.tuneK (A.price i)).val‖≤ e)(p:P.Pulsating (P.otherSpectrum 3 3 w) s A e)(t:0<e)(q:∀ i:Lead.Clan, Medal.SharpEnough i e) :∀ x:SU.Slot, P.Intact R s A w x e:=by
 intro x; unfold Intact; let V:=Window.family x; obtain ⟨N,h⟩:= carry P.run P.large P.law s P.projection _ _ (show (P.maybeTest A V).val∈ _ from P.cross_paid A V)
 have ht:=P.hitPhase s A w p t q x; refine ⟨FixedProbe.anchor_gap s (fun i=>porchGone (rayL Q A.hair)), P.reelCenter _ _ _ V t (q V) p,P.unselected_win s A v t q V,⟨N,P.addressPaid s A w 0 V N h,h⟩,?_,ht⟩ -- order check
 change 1/8 < ‖P.spirits R 3 w (P.slotHole s _)‖; rw [P.oneCup]; have he:= (ht 3).mixed; rw [P.single_agrees] at he; exact he
end Spine
open Lamour.Bridge.Celeste.Morn Ballad
open Spine TopologicalSpace CF.Pannier.Chancel CF.Velvet
-- train constructor for future labels & qualified app
variable {P:Spine}{x A e a:ℝ}{ι:Type}[Fintype ι]
structure Vinyl (V:Spine) (R:V.Register)(X:Supplier)(u v:ℝ):Prop where
 growth : V.par.nominated (VolumeCape.Dream.Nimbus V.width)
 meets : u < V.par.x
 walls : V.par.d ≤ v
 terraces : SeasonCert V.run V.large R.exhibition
 paper : ∃ (q d w : ℕ) (Z C : ℝ), Papal.Cornet V.run V.large q d w C Z ∧ Geometry V.par ∧ decorate X V.par V.width Z ≤ V.par.h
 nerve : ∃ v,Velvet.Procurement V.par.K.j v V.par.d
lemma Lactate (X:Supplier)(U:Papal.Lexicon ι a)(u v:ℝ) (p:0<v)(h:0<a)(w:a≤1/2): ∃ P : Spine,∃ R:P.Register, Vinyl P R X u v ∧ ∃ k,Papal.Lecture P.run P.large (U P.par.block (reserve P.par P.width)) k (4*Real.exp 1*(4*a)):= by
  let S:= Papal.energyK U h w
  let fuel:Supplier:= fun K p V H B d A W M J l Z=> max (X K p V H B d A W M J l Z) (S K p V H B d A W M J l Z)
  obtain ⟨P,t,E,pL,Y,A,q',d,w',Z₁,C',hQ,kP,vZ,r',R,a',_,_,_⟩:= satin_bench_variation fuel u v 1 p zero_lt_one 0 3
  have hvY: decorate S P.par P.width Z₁ ≤ P.par.h:=(le_max_right ..).trans vZ
  refine ⟨P,Y,⟨t,E,pL,A,⟨q',d,w',Z₁,C',hQ,kP, (le_max_left ..).trans vZ⟩,a'⟩,Papal.drapeX P.run P.large U _ h w kP a' hvY⟩
lemma small_bank (ι:Type)[Fintype ι](e:ℝ)(h:0<e): ∃ β:ℝ, 0<β ∧ β ≤ 1/2 ∧
    let A:=4*Real.exp 1*(4*β); A≤e ∧ (Fintype.card ι:ℝ)*A < e^2:= by
  let Cm(x:ℝ):=4*Real.exp 1*(4*x); let A (x:ℝ):=(Fintype.card ι:ℝ)*Cm x; have he:Continuous A:= by unfold A Cm; fun_prop
  have h0:Continuous Cm:=by unfold Cm; fun_prop -- indent?
  have hX: ∀ᶠ x:ℝ in 𝓝[>] 0, Cm x ≤ e:= eventually_nhdsWithin_of_eventually_nhds (h0.continuousAt.tendsto.eventually (ge_mem_nhds (show Cm 0<e by simpa [Cm] using h)))
  have ht: ∀ᶠ x:ℝ in 𝓝[>] 0, A x < e^2:= eventually_nhdsWithin_of_eventually_nhds (he.continuousAt.tendsto.eventually (gt_mem_nhds (show A 0< e^2 by simpa [A,Cm] using (pow_pos h 2))))
  exact (Filter.Eventually.and (show ∀ᶠ x in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin) (Filter.Eventually.and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num))) (hX.and ht))).exists
/-- Same canonical Satin E all-probe world, normalization/payment and coupling. Stronger vacuum result for tasks in this workspace. NO causal completion claim.
 Note `PublicPhase otherSpectrum 3 3` in pinning data; if using same `Hab` at 3 directly consume `single_agrees`: `Sanctuary` also phrases **using that extension convention exactly**. 
-/
theorem sixFoldSatin (X:Supplier)(u v:ℝ)(p:0<v){e:ℝ}(d:0<e): ∃ P: Spine,∃ R:P.Register,Vinyl P R X u v ∧ ∃ (β t:ℝ), 0<β∧ 0<t ∧ t<e ∧
    ∃ (A: Gaze P.par.block 4 (reserve P.par P.width) β), (∃ k, Papal.Lecture P.run P.large A.toLadle k (4*Real.exp 1*(4*β))) ∧
    ∀ᶠ s:ℕ in atTop,∃ x:P.Spectrum0 3,P.Sanctuary R 3 x ∧
                       (∀ i:Trinity, ‖P.E s (P.tuneK (A.price i)).val‖≤ t) ∧ P.Pulsating (P.otherSpectrum 3 3 x) s A t ∧ ∀ z:SU.Slot,P.Intact R s A x z t:= by
 obtain ⟨q,h,g⟩:= Medal.auth d
 obtain ⟨β,β₀,wp,s,s0⟩:=small_bank Trinity q h.1; let Y (B:Side)(ℓ:ℕ): Gaze B 4 ℓ β:= Classical.choice (brought_up B _ _ _ (by decide) β₀ wp); let U:Papal.Lexicon Trinity β:=fun B ℓ=>(Y B ℓ).toLadle
 obtain ⟨P,V,F,k,H⟩:=Lactate X U _ _ p β₀ wp; let W:=Y P.par.block (reserve P.par P.width)
 refine ⟨P,V,F,β,q,β₀,h.1,h.2,W,⟨k,H⟩,?_⟩; filter_upwards [P.seasonPick V W.toLadle H q h.1 s0] with y gy
 obtain ⟨u,x,z,l⟩:= gy y rfl; have v(i):= (u i).trans s; let p: P.Pulsating (P.otherSpectrum 3 3 x) y W q:= fun i=>(l i 3).le; exact ⟨x,z,v,p, P.participants V y W x v p h.1 g⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.participants
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.participants
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.sixFoldSatin
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.sixFoldSatin
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.cadet
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.refrain
