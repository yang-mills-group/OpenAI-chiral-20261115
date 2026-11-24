import YM.SU5.Reconstruction.Cashier.Operator
/-! Singlets. Consume LAST regulators on this continuation. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 490000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification Tapestry PhaseChoice
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)(j:Axis) (C:Arena Y H G.history.circuit j 0 false)(w:ℕ)
  (S:Finset Cover)(t:Between (tent Y H) j 0 (ruler Λ.block*w) S)(hw:0<w)
local notation "uM"=> (L₀^(s+1-s)*w)
local notation "Wh"=>wingspan Λ l S
local notation "Rx"=>render S (tent Y H)
local notation "B"=>allBox Y H V G j S s C w t hw
local notation "Ξ" s:max w:max=>advance Y H V G.history.circuit j 0 false C (MeshClock.whenly (timeMesh Λ) s w)
lemma coloroff : B (colorless K S)=Ξ s w:=by
 let X:=SlabMark.identity Y H s j false w; have ht:X.val.val=1:=rfl
 rw [←ticket_birth Y H V s G.history G.clipped j false C w hw]
 exact (box_chart Y H V G j S s C w t hw (x:=X) (colorless K S) (ht.trans (bareUnit ..).symm)).symm
open CF.Pannier.Chancel
private lemma from_consult {v:Tapestry.Swatch S}{x:Family K} {m:Side}(h:Hosp S ((tent Y H).c m))(p:Continuous (Rx v m))
 (q:InTest (tent Y H) true S false x)(e:x m=molasses (Rx v m))
 : ∃ u:Swatch S, Rx u=x ∧ B u=B v:=by
 let Q:= reynoldsC S K m v
 have he: render S K Q=x:=Tapestry.looksLike (m:=m) h (texture ..) q ((reynoldsC_apply S K m v h p).trans e.symm)
 exact ⟨Q,he,(boxReynolds Y H V G j C S s w t hw m v h p).symm⟩ -- order check

-- price for coupon account real. acts on both full Ark and selected indoor via C* force.
-- intentionally annotate exact footprint each time even if supports merely Between (require paid f too,
-- StampFoot preserves witness cell when poses in Energy lemma).
def StampFoot (f: Family (tent Y H)) (J:ℝ) :Prop :=
    InTest K true S false f ∧ Between (tent Y H) j 0 (ruler Λ.block*w) S ∧
    ∃ p:0<w, ∃ x: Entry Y H s j false w, x.val.val=f ∧
      ‖boxOp Y H V s G.history G.clipped j false C w x p + advance Y H V G.history.circuit j 0 false C (MeshClock.whenly (timeMesh Λ) s w)‖ < J
local notation "Met"=>StampFoot Y H V s G j C w S
variable {J:ℝ}
lemma stenciled (u:Swatch S) : Met (Rx u) J ↔ ‖B u+Ξ s w‖ < J:=by
 constructor
 · rintro ⟨a,m,b,x,h,t'⟩; rwa [box_chart Y H V G j S s C w t hw u h] at t'
 exact fun h=> ⟨texture ..,t,hw,toEntry Y H j false S s w t (allHues Y H S u),rfl,h⟩
lemma stamps_up {T:Finset Cover} {f:Family K} {J':ℝ} (t:StampFoot Y H V s G j C w S f J) (h:S⊆T)(hp:Between K j 0 (ruler Λ.block*w) T)(e:J≤ J') : StampFoot Y H V s G j C w T f J':=by
 obtain ⟨x,y,u,l,hx,a⟩:=t; exact ⟨x.mono h,hp,u,l,hx,a.trans_le e⟩
local notation "I₁" r:max=>i (G.rows r)
local notation "I₂" r:max=>k (G.columns r)
open CF.Pannier.Chancel.Cliplet
variable (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(th:∀j:Axis,Between (tent Y H) j 0 (ruler Λ.block*w) S)

variable {d q u:ℕ}
local notation "Φ"=>payout d q u
local notation "ρ"=>grain (payout d q u)
local notation "Ψ"=>Sen ρ Φ
local notation "Rb"=>Tapestry.render Ψ (tent Y H)

structure Live (e:ℕ)(d q u:ℕ) (z:SU.Slot)(f: Vacancy.observable (tent Y H) true) :Prop where
 rooted : f.val∈ Filigree (tent Y H) (Window.family z) (booty (grain (payout d q u)) d q) (Sen (grain (payout d q u)) (payout d q u))
 exact_ : exhibit Y H s ((i∘ G.rows) e) f.val=Papal.aliquot Y s ((i∘G.rows) e) ((k∘G.columns) e) q d u (grain (payout d q u)) z
 budget (j:Axis): StampFoot Y H V s G j (c j) w (Sen (grain (payout d q u)) (payout d q u)) f.val (1/128)

private lemma delivery {a b:ℕ}{z:SU.Slot} (g:Swatch Ψ)(t:Matching Y H s d q u a b z ((Rb) g)) (wx:Roomy (Sen ρ Φ) (Papal.count Y s a))
 {f: Vacancy.observable K true} (v:f.val∈ Filigree K (Window.family z) (booty ρ d q) (Sen ρ Φ))(h:exhibit Y H s a f.val=Papal.aliquot Y s a b q d u ρ z)
 (u0:Between (tent Y H) j 0 (ruler Λ.block*w) Ψ)(t':‖allBox Y H V G j Ψ s C w u0 hw g‖<1/128): StampFoot Y H V s G j C w Ψ f.val (1/128):=by
 let S₀:= Sen ρ Φ; let N:=momentm Y a s; let Bb:= allBox Y H V G j Ψ s C w u0 hw
 let X:=g-colorless K Ψ; have ht:((Rb) X)=render Ψ K g-1:=by unfold X; rw [map_sub,bareUnit]
 let Y₀:= (Papal.taggin Y s a b q d u ρ z).frame; let e:=terrain Y H (Y.ir a) s
 have hx: exhibit Y H s a (render Ψ K X)=Y₀-1:=by rw [ht,map_sub,actual_one,t.note] -- rw done?
 have he : Continuous (exhibit Y H s a (render Ψ K X)):=by rw [hx]; exact (feastReady ..).sub continuous_const
 have h' : exhibit Y H s a f.val= molasses (exhibit Y H s a (render Ψ K X)):=by rw [h,hx]
 obtain ⟨p,q'⟩:= equivalent (x:=(render Ψ K X) N) (y:= f.val N) e h' he
 obtain ⟨F,v₀,U⟩:= from_consult Y H V s G j C w Ψ u0 hw (m:=N) (e.symm ▸ wx.seats) q' (FilTest v).widen p
 rw [← v₀]; apply (stenciled Y H V s G j C w Ψ u0 hw F).2
 rw [U,(allBox Y H V G j Ψ s C w u0 hw).map_sub g (colorless K Ψ), coloroff Y H V s G j C w Ψ u0 hw,sub_add_cancel]; exact t'
where
 equivalent {m N:Side}{x y:Mark N}(p:N=m)(h:Tapestry.arrange _ _ p y=molasses (Tapestry.arrange _ _ p x))(q:Continuous (Tapestry.arrange _ _ p x)) : y=molasses x ∧ Continuous x:=by subst N; exact ⟨h,q⟩

include hw
lemma enter (tn:∀j:Axis,Between (tent Y H) j 0 (ruler Λ.block*w) (Sen ρ Φ)) (v:0≤ J)
    (h:∀ᶠ e in atTop, Attendance Y H s d q u w J (I₁ e) (I₂ e)):
    ∀ᶠ e in atTop, ∀ z:SU.Slot,∃ f: Vacancy.observable K true, Live Y H V s G w c e d q u z f := by
 apply Filter.eventually_all.mpr; intro z
 obtain ⟨f,b,x,r⟩:=equip (z:=z) Y H s G v h
 filter_upwards [tend_small Y H V s G w Ψ hw f J b x c tn,r,h] with i t e h
 obtain ⟨F,g,h'⟩:= e.public_
 exact ⟨F,g,h',fun j=>delivery Y H V s G j (c j) w hw (f i) e h.format g h' (tn j) (t j)⟩

end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.enter
