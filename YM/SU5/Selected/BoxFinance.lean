import YM.SU5.Selected.CompactResolution

/-! Missing price needed for separability and continuity in phase selection:
operator-norm box control for every fixed support. This doesn't assert such
norm control vs spatial translations or as boxes change scale. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set
open Tapestry (Swatch render render_inj texture render_eq renderLe spread sampling render_fabric)
variable (S:Finset Cover)
local notation "rx"=>render S K
noncomputable def hues : Submodule ℂ (Tapestry.Swatch S) where
  carrier := {f| strict = true → CovCover K (rx f)}
  zero_mem' := fun _ => by rw [map_zero]; exact covariant_zero _
  add_mem' {x y} hx hy h := by rw [map_add]; exact (covariant_parts K (hx h) (hy h)).1
  smul_mem' a {x} hx h:=by rw [map_smul]; exact covariant_scale K (hx h) _
local notation "φ"=> hues Y H strict S
lemma closed_hues : IsClosed ((φ) : Set (Swatch S)) := by
  apply IsSeqClosed.isClosed
  intro y x v t
  intro a
  apply (Tapestry.harmonicHere (S:=S)).2
  intro T
  exact Tapestry.continuousColor K S T t t (Eventually.of_forall fun i => Tapestry.harmonicHere.mp
    (v i a) T)
instance complete_hues : CompleteSpace (φ) := (closed_hues Y H strict S).completeSpace_coe
instance : NormedSpace ℂ (φ) := Submodule.normedSpace _
instance full_norm_space : @NormedSpace ℂ (φ) _ ((inferInstance : NormedAddCommGroup (φ)).toSeminormedAddCommGroup) :=
   (show NormedSpace ℂ (φ) from inferInstance)
variable (s u:ℕ)(h:Between (tent Y H) j 0 (ruler Λ.block*u) S) (p:0<u)

noncomputable def toEntry (x : φ) : Entry Y H s j strict u :=
  ⟨(⟨rx x.val,(purpose_ok ..).2 ⟨(show _ from ⟨S, texture S K x.val, by
    rw [SlabMark.area0]; exact fun t p => (h t p).1⟩),x.property⟩⟩ : Fₛ s),S,texture S K x.val,h⟩
local notation "η"=> toEntry Y H j strict S s u h
noncomputable def boxChart : (φ) →ₗ[ℂ] (A →L[ℂ] A) where
  toFun f:= B s (η f) p
  map_add' x y:= box_add Y H V G j strict C s u _ _ _ p (map_add rx x.val y.val)
  map_smul' z x:= box_scale Y H V G j strict C s u _ _ p z (map_smul rx _ x.val)
local notation "Xb"=>boxChart Y H V G j strict C S s u h p

private lemma cents (t:ℕ)(w:s≤t)(x y:Fₛ t) :
    Continuous (fun i=> inner ℂ ((κ t) x) (Xb i ((κ t) y))) := by
  let T:= ((innerSL ℂ ((κ t) x)).toLinearMap.comp
    ((ContinuousLinearMap.apply ℂ A ((κ t) y)).toLinearMap.comp Xb)) -- order?
  change Continuous T
  let z := mirror K j 0 x.val
  have hz: TestFamily K true z:= reflect_ok K j _ (field_test Y H t j 0 strict x)
  let v:=relocate K j ((Λ.R.L.val^(t-s)*u:ℕ):ℤ) y.val
  have hv:TestFamily K true v := move_ok K j _ (field_test Y H t j 0 strict y)
  obtain ⟨c,e⟩ := hz.paid; obtain ⟨cv,wv⟩:=hv.paid
  obtain ⟨k,x'⟩:= Journey.valuation Y H e; obtain ⟨kv,y'⟩:= Journey.valuation Y H wv
  let d(i:φ):=stream Y H G.refine s (t-s) (rx (i:(Tapestry.Swatch S)))
  obtain ⟨m,_,hp⟩:=fares Y H s G.history S (t-s)
  obtain ⟨i,tp⟩:=(hp 1 zero_lt_one).exists
  let r:=volumeAround Λ l (t-s) S
  have hk(i:φ):pay (d i) (m*(spread S*‖i‖)) := (tp _ (texture S K i.val) _ (rendered_price Y H S i.val)).1
  let f(i:φ):=z*(d i*v)
  let r':=c∪(r∪cv)
  have h'(i):T i=E t (f i):= by
    change inner ℂ ((κ t) x) ((B s (η i) p) ((κ t) y))=_
    rw [snatch Y H V s G.history G.clipped j strict C u _ p w,stems Y H V,area0,slab_eq]; rfl
  apply AddMonoidHomClass.continuous_of_bound T
    (toll Y H t r' * (k*(m*spread S*kv)))
  intro i; rw [h']
  have hp'(i:φ) : InTest K true r false (d i):= (proceeds Y H G.history.circuit s (t-s) (texture S K i.val)).1
  have ht: InTest K true (r ∪ cv) false (d i * v) := InTest.mul ((hp' i).mono Finset.subset_union_left) (wv.mono Finset.subset_union_right)
  have auxbound := (E_bound Y H V t r' (show InTest K true r' false (f i) from .mul (e.mono Finset.subset_union_left) (ht.mono Finset.subset_union_right))
    (pay_mul (show pay z k from x') (pay_mul (hk i) (show pay v kv from y'))))
  have hw : ‖E t (f i)‖≤ (toll Y H t r')*(k*((m*(spread S* (‖(i.val:Tapestry.Swatch S)‖:ℝ)))*kv)):=auxbound
  change ‖E t (f i)‖≤ _ * ‖(i.val:Tapestry.Swatch S)‖
  exact hw.trans_eq (by ring)

/-- Closed graph: all **actual linear forms** by the mixed PSD Gram converge;
apply from both sides to a later rung, hence continuity on the (Banach) chart.
Consequently in operator seminorm already before selecting countable horizon. -/
lemma chart_box_continuous : Continuous Xb := by
  refine @LinearMap.continuous_of_seq_closed_graph ℂ inferInstance (φ) inferInstance (full_norm_space Y H strict S) (complete_hues Y H strict S) ( (Ark.Ht Y H G.history.circuit j 0 strict C).Op ) inferInstance inferInstance inferInstance Xb ?_
  intro y x r hx hr
  apply test_high Y H V s G.history j strict C
  intro t w a
  apply all_voices Y H G.history.circuit j 0 strict C
  intro m b
  let n:=max t m; have ht:t≤n:=le_max_left ..; have hm:m ≤ n:=le_max_right ..
  let t' := Raise Y H G.history.circuit j 0 strict t n ht a
  let m' := Raise Y H G.history.circuit j 0 strict m n hm b
  rw [←join_actor Y H V G.history.circuit j 0 strict C t n ht,
    ←join_actor Y H V G.history.circuit j 0 strict C m n hm]
  change inner ℂ ((κ n) m') (r ((κ n) t')) = inner ℂ ((κ n) m') (Xb x ((κ n) t'))
  exact tendsto_nhds_unique (f := fun i => inner ℂ ((κ n) m') (Xb (y i) ((κ n) t')))
    (tendsto_const_nhds.inner (((ContinuousLinearMap.apply ℂ A ((κ n) t')).continuous.continuousAt.tendsto.comp hr)))
    ((cents Y H V G j strict C S s u h p n (w.trans ht) m' t').continuousAt.tendsto.comp hx)
noncomputable def boxCLM : (φ) →L[ℂ] (A →L[ℂ] A) := ⟨Xb,chart_box_continuous Y H V G j strict C S s u h p⟩

-- norm continuity estimate with same all-tori pricing; doesn't require
-- s strongly uniform as support moves. 
local notation "Lo" => boxCLM Y H V G j strict C S s u h p
lemma prices_box (x:Entry Y H s j strict u)(t:InTest K true S false x.val.val){q:ℝ}(v:pay x.val.val q):
    ‖B s x p‖ ≤ ‖Lo‖*q := by
  obtain ⟨F,t'⟩ := Tapestry.rendered S K t
  let f:φ := ⟨F, fun w=>(by rw [t']; exact ((purpose_ok ..).1 x.val.property).2 w)⟩
  have hf:x=η f:=Subtype.ext (Subtype.ext t'.symm)
  have hm: B s x p= Lo f := congrArg (fun x:Entry Y H s j strict u=> boxOp Y H V s G.history G.clipped j strict C u x p) hf
  have h₁:‖f‖≤q:=sample_price Y H S F (t'.symm ▸ v)
  rw [hm]; exact (@ContinuousLinearMap.le_opNorm ℂ ℂ (φ) ( (Ark.Ht Y H G.history.circuit j 0 strict C).Op ) _ _ _ _ (full_norm_space Y H strict S) _ _ _ Lo f).trans (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.boxCLM
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.prices_box
