import YM.SU5.Reconstruction.AllGrades.Housing
import YM.SU5.Reconstruction.Quanta.Touch
import YM.SU5.Verified.Satin.GroundExtension
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
open Reed (Fine think)
open Fock Pastry Tenant
namespace Garret
/-! # Turn the fresh rotation into a hierarchy on the same selected even history -/
open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "π"=> i ∘ G.rows
local notation "κ"=> k ∘ G.columns
structure Invitation where
 indexN : ℕ → ℕ
 thinned : StrictMono indexN
 checks : Tenure Y H ((i ∘ G.rows) ∘ indexN) ((k ∘ G.columns) ∘ indexN)
include V
lemma passes : Nonempty (Invitation Y H G):=by
 obtain ⟨f,e,p⟩:= Garret.acquireT Y H π κ (V.pick.grow_i.comp G.history.growsA).tendsto_atTop (fun s=>(G.history.finance (s+1)).mono fun m x=> ⟨x.depth,x.enters⟩)
 exact ⟨⟨f,e,p⟩⟩
omit V
variable (D: Invitation Y H G)
local notation "σ₀"=> (i ∘ G.rows) ∘ D.indexN
local notation "τ₀"=> (k ∘ G.columns) ∘ D.indexN
noncomputable def convey (b:Bool)(s:ℕ)(x:Family (tent Y H)):Family (tent Y H):=
 match b with
 | true=> if h:∃ S:Finset Cover,InTest K true S true x then chooseTape Y H s σ₀ τ₀ h.choose D.checks x else 0
 | false=> G.refine s x
local notation "T" => convey Y H G D
variable {b:Bool}{S Z:Finset Cover}{F F':Family (tent Y H)}(x:InTest (tent Y H) true S b F)
lemma delegates(U: Finset Cover) :∀ᶠ r in atTop, legalAt Y s (σ₀ r) (τ₀ r):=by
 let h: ∀ᶠ r in atTop, legalAt Y s (i (G.rows r)) (k (G.columns r)):= (G.history.finance (s+1)).mono fun r p=> ⟨p.depth,p.enters⟩; exact (D.thinned.tendsto_atTop.eventually h)
include V
lemma tables(U:Finset Cover):∀ᶠ r in atTop,Tivoli U ((tent Y H).c (momentm Y (σ₀ r) s)):= ((V.pick.grow_i.comp (G.history.growsA.comp D.thinned)).tendsto_atTop).eventually (turning Y H s U)
local notation "Θ"=> Garret.pick Y H s
local notation "W" => wingspan Λ l
local notation "fL" => chooseTape Y H s σ₀ τ₀
local notation "mS" t:max r:max=> ((tent Y H).c (momentm Y (σ₀ r) t))
private lemma union0 {X U:Finset Cover}(x:InTest (tent Y H) true X true F)(t:X⊆U) : fL X D.checks F=fL U D.checks F:=by
 funext m z
 apply tendsto_nhds_unique_of_eventuallyEq (ev_tape Y H s σ₀ τ₀ D.checks X x m z) (ev_tape Y H s σ₀ τ₀ D.checks U (x.mono t) m z)
 filter_upwards [tables Y H V (s+1) G D (W X),tables Y H V (s+1) G D (W U),delegates Y H s G D U] with r i k p
 refine congrFun (congrFun (distributed Y H (s+1) (W U) (σ₀ r) k ((tBook Y H s _ _ _ _).mono (wingspan_mono t)) (tBook Y H s _ _ _ _) ?_) m) z
 rw [tReserve Y H s _ _ p _ x i,tReserve Y H s _ _ p _ (x.mono t) k]
lemma tape_label (p:InTest K true S true F):T true s F=fL S D.checks F:=by
 let h:∃ Z:Finset Cover,InTest K true Z true F:= ⟨_,p⟩
 rw [convey,dif_pos h]; exact (union0 Y H V s G D h.choose_spec (subset_union_left (s₂:=S))).trans (union0 Y H V s G D p subset_union_right).symm
include x
lemma attaches_p : InTest K true (W S) b (T b s F):=by
 cases b
 · exact (G.history.circuit.supports s x).1
 rw [tape_label Y H V s G D x]; exact pinsTape ..
omit x
-- both authenticated policies compact on this very selection; ALSO same Stamp/Geo/Gauge.
local notation "sl" r:max b:max S:max F:max=>Θ (σ₀ r) (τ₀ r) b S F
/-- On every invited pair, price of all actual quantum lifts. The same limit D as earlier exactly even. -/
lemma value_of_lifts (S:Finset Cover) (b : Bool):∃ C:ℝ,0<C ∧ ∀ ε:ℝ,0<ε→∀ᶠ r:ℕ in atTop,
   ∀ (F:Family (tent Y H)),InTest (tent Y H) true S b F→∀ d:ℝ,pay F d→
       pay (T b s F) (C*d) ∧ pay (sl r b S F) (C*d) ∧ pay (sl r b S F - T b s F) (ε*d):=by
 cases b
 · obtain ⟨C,c,p⟩:= G.history.implements s S; refine ⟨C,c,fun ε h=>?_⟩
   filter_upwards [D.thinned.tendsto_atTop.eventually (p ε h),tables Y H V (s+1) G D (W S),delegates Y H s G D S] with r v H₀ x F d d' a
   let X:=sl r false S F; obtain ⟨e,y⟩:= lamp_jump Y H s (σ₀ r) (τ₀ r) x d H₀
   have ht:X=block Y H s (σ₀ r) (τ₀ r) S F:=distributed Y H (s+1) (W S) (σ₀ r) H₀ e (Tower.booked ..) (by rw [reserved Y H s S _ _ x d H₀]; exact y)
   rw [show sl r false S F=block Y H s (σ₀ r) (τ₀ r) S F from ht]
   exact ⟨(v _ d d' a).1,(v _ d d' a).2.1,(v _ d d' a).2.2.1⟩
 obtain ⟨C,c,p⟩:= doc_funded Y H s σ₀ τ₀ D.checks S
 refine ⟨C,c,fun ε h=>?_⟩; filter_upwards [p,D.checks.outfits Y H s σ₀ τ₀ S ε h,tables Y H V (s+1) G D (W S),delegates Y H s G D S] with r v f H₀ x F d d' a
 have ht:sl r true S F=torchBlock Y H s (σ₀ r) (τ₀ r) S F:= by rw [torchBlock,if_pos ⟨x,d,H₀⟩]
 rw [tape_label Y H V s G D d,ht]; exact ⟨(v F d d' a).1,(v F d d' a).2,f F d d' a⟩
include x
lemma ever(m:Side)(z:Fields ((K).c m)):Tendsto (fun i=> (sl i b S F) m z) atTop (𝓝 (T b s F m z)):=by
 obtain ⟨A,v,p⟩:= value_of_lifts Y H V s G D S b; obtain ⟨C,c⟩:=valuation Y H x; change pay _ _ at c; have h':= pay_nonneg c
 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 let δ:= ε/(C+1); have hd:0 < δ:=by unfold δ; positivity
 filter_upwards [p δ hd] with r v
 rw [dist_eq_norm]; refine ((v F x C c).2.2 m z).trans_lt ?_
 have ht: δ*(C+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith

-- critical geometry/R/W across later epochs
lemma halo (a:Axis)(z:ℤ): T b s (mirror K a z F)=mirror K a ((Λ.R.L.val:ℤ)*z) (T b s F):=by
 let lat:= (Λ.R.L.val:ℤ)*z; let Z':=reflectedBox a z S; let W':= (W Z'); let U':=reflectedBox a lat (W S)
 let t':= axial K a z x
 funext m y
 apply tendsto_nhds_unique_of_eventuallyEq (ever Y H V s G D t' m y) ((theta_cont (carR a lat ((K).c m))).continuousAt.tendsto.comp (ever Y H V s G D x m (reflFields a lat y)))
 filter_upwards [tables Y H V (s+1) G D (W S), tables Y H V (s+1) G D W', tables Y H V (s+1) G D (W' ∪ U'), delegates Y H s G D S] with r h e w g
 let R:= sl r b Z' (mirror K a z F); let V₀:=sl r b S F; obtain ⟨i,a₀⟩:=lamp_jump Y H s _ _ g x h; obtain ⟨j,z₀⟩:=lamp_jump Y H s _ _ g t' e
 have H:R=mirror K a lat V₀:=distributed Y H (s+1) (W' ∪ U') _ w (j.mono subset_union_left) ((axial K a lat i).mono subset_union_right) (by rw [(distribute_arith Y H (s+1) (σ₀ r) V₀ V₀ 0).2.2.2.2 a lat]; change distribute Y H (s+1) (σ₀ r) R=_; rw [show distribute Y H (s+1) _ R=_ from z₀,show distribute Y H (s+1) _ V₀=_ from a₀]; exact beam_reflect Y H s _ _ g a z x)
 exact congrFun (congrFun H m) y
lemma colors(p:CovCover K F):CovCover K (T b s F):=by
 intro m g y; apply tendsto_nhds_unique_of_eventuallyEq (ever Y H V s G D x m (simultaneous g y)) ((Fock.breeze _).continuousAt.tendsto.comp (ever Y H V s G D x m y))
 filter_upwards [tables Y H V (s+1) G D (W S),delegates Y H s G D S] with r e H₀; exact native_pick Y H s _ _ H₀ e x p m g y
local notation "σ" => (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))
lemma fare_sep {b':Bool}(y:InTest K true Z b' F')(p: separated σ S Z):T (b ^^ b') s (F*F')=T b s F * T b' s F':=by
 let U:= S∪Z; let Q:= W U; let d:InTest K true U (b ^^ b') (F*F'):= InTest.mul (x.mono subset_union_left) (y.mono subset_union_right)
 funext m v
 apply tendsto_nhds_unique_of_eventuallyEq (ever Y H V s G D d m v) ((ever Y H V s G D x m v).mul (ever Y H V s G D y m v))
 let h:Tendsto (i ∘ G.rows ∘ D.indexN) atTop atTop:=(V.pick.grow_i.comp (G.history.growsA.comp D.thinned)).tendsto_atTop
 filter_upwards [h.eventually ((Journey.momentum Y s).eventually (wrapped_far (tent Y H) σ S Z p)),tables Y H V (s+1) G D Q,tables Y H V (s+1) G D (W S),tables Y H V (s+1) G D (W Z),delegates Y H s G D U] with r S' e t t' w
 let R:= sl r (b ^^ b') U (F*F'); let A:= sl r b S F; let A':= sl r b' Z F'; obtain ⟨j,V⟩:=lamp_jump Y H s _ _ w d e; obtain ⟨a,v₀⟩:=lamp_jump Y H s _ _ w x t; obtain ⟨c,c₀⟩:=lamp_jump Y H s _ _ w y t'
 have h:R=A*A':=distributed Y H (s+1) Q _ e j (InTest.mul (a.mono (wingspan_mono subset_union_left)) (c.mono (wingspan_mono subset_union_right))) (by rw [(distribute_arith Y H (s+1) (σ₀ r) A A' 0).2.1,show distribute Y H (s+1) _ R=_ from V,show distribute Y H (s+1) _ A=_ from v₀,show distribute Y H (s+1) _ A'=_ from c₀]; exact beam_sep Y H s _ _ w x y S')
 exact congrFun (congrFun h m) v

lemma combines (p:InTest K true S b F'):T b s (F+F')=T b s F+T b s F':=by
 cases b; · exact G.history.circuit.plus_lift _ (aux_test x) (aux_test p)
 rw [tape_label Y H V s G D (x.add p), tape_label Y H V s G D x,tape_label Y H V s G D p]; funext m z; apply tendsto_nhds_unique_of_eventuallyEq (ev_tape Y H s σ₀ τ₀ D.checks _ (x.add p) m z) ((ev_tape Y H s σ₀ τ₀ D.checks _ x m z).add (ev_tape Y H s σ₀ τ₀ D.checks _ p m z)); exact Eventually.of_forall fun r=> congrFun (congrFun (add_planGr Y H s (σ₀ r) (τ₀ r) x p) m) z
lemma tuning (q:ℂ):T b s (q • F)=q • T b s F:=by
 cases b; · exact G.history.circuit.amp _ (aux_test x) q
 rw [tape_label Y H V s G D (InTest.smul q x), tape_label Y H V s G D x]; funext m z; apply tendsto_nhds_unique_of_eventuallyEq (ev_tape Y H s σ₀ τ₀ D.checks _ (InTest.smul q x) m z) ((tendsto_const_nhds (x:=q)).smul (ev_tape Y H s σ₀ τ₀ D.checks _ x m z)); exact Eventually.of_forall fun r=> congrFun (congrFun (scale_planGr Y H s (σ₀ r) (τ₀ r) x q) m) z
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.passes
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.halo
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.fare_sep
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.value_of_lifts
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.colors
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.tuning
