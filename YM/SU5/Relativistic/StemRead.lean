import YM.SU5.Relativistic.RopeCampus
import YM.SU5.Relativistic.ReadPos
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f


namespace Lariat
lemma allEven {K':Calibration}(f:Lariat K' n)(h:f.evens) : f.hue=false:=by
 induction f with| start f=>exact h| stretch f g ih=> change ((hue f).xor g.kind)=false; rw [ih h.1,h.2]; rfl
noncomputable def previousReading(s:ℕ):{n:ℕ}→ (f:Lariat (tent Y H) n) → f.evens → Cloud (Dome (tent Y H))
 | 0,start f,p=>pinhole D₀ s ⟨f.mark,aux_test (show InTest K true f.S false f.mark from (show f.kind=false from p) ▸ f.bill)⟩
 | n+1,stretch f g,p=> previousReading s f p.1 * pinhole D₀ (s+(n+1)) ⟨g.mark,aux_test (show InTest K true g.S false g.mark from (show g.kind=false from p.2) ▸ g.bill)⟩
lemma beforeShort (s:ℕ)(f:Lariat (tent Y H) n)(h:f.evens) : previousReading Y H s f h∈shorter D₀ (s+n):=by induction f with
 | start f=> exact short_pinhole s _
 | @stretch n f g ih=> refine (shorter D₀ (s+(n+1))).mul_mem (climbs D₀ (by omega : s+n≤_) (ih h.1)) (short_pinhole _ _)
include t
lemma beforeEarn (s:ℕ)(f:Lariat K n)(h:f.evens): (vistaFinish Y H (s+n) D (previousReading Y H s f h)).val= Lariat.rideL Y H T s f:=by
 induction f with
 | start f=> unfold previousReading vistaFinish; rw [Nat.add_zero]; rw [Decking.outcrop]; rfl
 | @stretch n f g ih=>
    let p:=previousReading Y H s f h.1
    let x: D₀:=⟨g.mark,aux_test (show InTest K true g.S false g.mark from (show g.kind=false from h.2) ▸ g.bill)⟩
    let F:=vistaDressing Y H D
    let H_:p∈ shorter D₀ (s+n):= beforeShort Y H s f h.1
    have ht : vistaFinish Y H (s+n+1) D (p*pinhole D₀ (s+n+1) x)=F.surge (s+n) (vistaFinish Y H (s+n) D p)*x:= by
       have he : vistaFinish Y H (s+n+1) D (p*pinhole D₀ (s+n+1) x)=vistaFinish Y H (s+n+1) D p*x:= Decking.last (vistaDressing Y H D) (auxiliaryPad K) p (s+n+1) (Altitude.climbs D₀ (Nat.le_succ _) H_) _
       rw [he, vistaFinish, Decking.joins F _ p (auxiliaryPad K) H_]; rfl -- maybe proof def macros
    rw [show previousReading Y H s (stretch f g) h= p*pinhole D₀ (s+n+1) x from rfl]; change (vistaFinish Y H (s+n+1) D _).val = T (s+n) f.hue (E₀ s f)*g.mark
    rw [ht]; change (liftD Y H (s+n) D (vistaFinish Y H (s+n) D p)).val*_=_; rw [lifts_here Y H V, show (vistaFinish Y H (s+n) D p).val= _ from ih h.1, allEven f h.1,t.formerly Y H V Q u _ (aux_test (show InTest K true (box Λ l f) false (E₀ s f) from (allEven f h.1) ▸ aboard Y H u T t s f))]
-- all processor ψ response in Rope uses discount of its grade.
noncomputable def appeal (T:ℕ→Bool→Family (tent Y H)→Family (tent Y H))(s:ℕ) (f:Lariat (tent Y H) n):ℂ := discount ψ (hue f) (s+n) (rideL Y H T s f)
local notation "a₀" s:max=>appeal Y H D G d c x T s
lemma atEven (s:ℕ)(f:Lariat (tent Y H) n)(h:f.evens) : onDrawing Y H D.univ_ G D d c (SameCharacter.resident Y H V G d false (c d) x) (previousReading Y H s f h) = (a₀ s) f:= by
 rw [drawAt Y H V G D d c _ (beforeShort Y H s f h)]
 unfold appeal discount; rw [allEven _ h,if_neg (by decide),←beforeEarn Y H D G u t s f h]; rfl -- w h must infer
-- appeal includes full score with Koszul normalization. Need amplify multiplication relation.
lemma scorePhysical (s:ℕ)(f g:Lariat K n)(z:ℤ):
    scoreCard Y H D G d j c x T s z f g= Reflect.chord (hue f)*appeal Y H D G d c x T s (glueWord (turned Λ j (μ z) f) g):= by
 let B':= glueWord (turned Λ j (μ z) f) g; unfold scoreCard
 by_cases h:hue f=hue g
 · rw [if_pos h]; have ht:hue B'=false:=by unfold B'; rw [glueHue,mate_hue _,h,Bool.xor_self]
   have H':InTest (tent Y H) true (box Λ l B') false (E₀ s B'):= ht ▸ aboard Y H u T t s _
   change ψ (s+n) (Reflect.chord _ • (E₀ s B'))=_*discount ψ (hue B') (s+n) (E₀ s B')
   rw [discount,ht,if_neg Bool.false_ne_true]; exact (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) _).map_smul _ (⟨_,aux_test H'⟩:Dome K)
 rw [if_neg h]
 have ht:hue B'=true:=by unfold B'; rw [glueHue, mate_hue]; cases e:f.hue <;> cases g:g.hue <;> simp_all
 change _=_*discount ψ (hue B') _ _; rw [discount,ht,if_pos rfl,mul_zero]
end Lariat

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
