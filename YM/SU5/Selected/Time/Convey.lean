import YM.SU5.Selected.Cor.Soothe
import YM.SU5.Selected.Time.Pace
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel Tapestry Papal
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
-- use C : Arena false only (assembly neutral). 
local notation "Ch"=> CapCharacter Y H V Q Qc j false C
local notation "Test"=> Vacancy.observable (tent Y H) false
local notation "readχ"=> phaseRead Y H V Q Qc j C
local notation "F₀" i:max=> cap Y H V i Q Qc j false C
local notation "N" i:max=> liftCap Y H V Q Qc j false C i
namespace Fern
open Commission Sermon
-- general j/time seam. orientation. Works before strongly continuous limit hypotheses. Mark coordinates are K units. Physical ticks are given in TimeKeeper Fermi level0 vs gauge campus ratio exactly two. 
variable (z : ℤ) (s:ℕ) {f g:Family (tent Y H)}{S T:Finset Cover} {a0 k0:ℝ}
local notation "U" u:max=>relocate K j u
--local notation "f" f:max=> f -- remove
local notation "θ"=> Tower.mirror K j 0
local notation "x₀" => (ruler (K).B*z)
local notation "R₀" => ruler (K).B
local notation "κ₁"=> (whenly (timeMesh Λ) s 1)
namespace Curtain
-- develop generic accounting to translate to true gap and temporal steps in Actor stage3 of selected same law. sign α.
local notation "L"=> f
variable (p : ∀ x∈ S,x j+(tent Y H).ℓ ≤ ruler (tent Y H).B*z)
    (v : ∀ x∈ T, ruler (tent Y H).B*z+ruler (tent Y H).B+(tent Y H).ℓ ≤ x j)
    (A' : Alight Y H V Q Qc j C s a0 k0 f g S T)
local notation "ιM"=> plow K j
local notation "τ"=> tick Y H s j 0 false
open Guild
open Spectral Spectral.Alps
variable {χ : CapCharacter Y H V Q Qc j false C} (X : Birthplace Y H V Q Qc j false C χ)
local notation "Tη" u:max => (journey Y H V Q Qc j false C X).track u
local notation "ς₁" t:max => markedActor Y H V Q Qc j false C X t
local notation "ς" => markedActor Y H V Q Qc j false C X s
local notation "μ"=> vacuum Y H V Q Qc j false C X
local notation "J"=> Diary.jetTime Y H V Q Qc j false C X
local notation "V₀" => journey Y H V Q Qc j false C X
local notation "u₀"=> phaseRead Y H V Q Qc j C χ s
local notation "W₀"=> whenly (timeMesh Λ) s
variable (hX : InTest (tent Y H) false S false f)(hY : InTest (tent Y H) false T false g)
variable (ehX:Neutral (tent Y H) f)(ehY : Neutral (tent Y H) g)
variable (x y: Tower.Field Y H s j 0 false)
-- Member of strict-time-complement not asserted vs margin. explicitly assertion outside strict-time-zero. `jetTime` docs: dummyspace stays confined. `slide` ticks on precise budget. Real Mink times `t` separation kept smearing of originating positive half operators (no pretending x local poset). Eu-Hilbert containers.
local notation "P" v:max=> Spectral.Alps.aboveH v
include V Q Qc C
structure Steams (f g:Family (tent Y H)) (S T:Finset Cover): Prop where
 born: x.val = θ ((U (-z)) f) ∧ InTest K false (reflectedBox j 0 (plow K j (-z) S)) false x.val ∧ Neutral K x.val
 bore: y.val=(U (-z-1)) g ∧ InTest K false (plow K j (-z-1) T) false y.val ∧ Neutral K y.val
 slide (w:ℕ): inner ℂ (ς x) ((Tη (W₀ (1+w))) (ς y))= u₀ (f*(U (w:ℤ)) g)
 raw_mean : inner ℂ μ (ς y) = u₀ g ∧ inner ℂ (ς x) μ=u₀ f
 slideHeight (u:ℕ)(w:ℕ)(p:s≤u) : inner ℂ (ς x) ((Tη (whenly (timeMesh Λ) u w)) (ς y))=
    let i:=Raise Y H Q.circuit j 0 false s u p x; let l:= Raise Y H Q.circuit j 0 false s u p y
    (readχ χ) u ((θ i.val) * (relocate K j w l.val))
#print Steams.mk
omit V Q Qc C
-- Generic links along arc; budget t-step; parameter d price; syntax real support
structure Switch {a:Axis}(Q':Hilbert)(F:OS.Semigroup Q' a)(x y:Q')(d t: ℝ≥0)(c:ℝ): Prop where
 price : 0 < c ∧ 0< d ∧ d < t
 floor: c < ‖inner ℂ x ((F.E d-F.E t) y)‖
 strictμ: c < ‖inner ℂ ((P F) x) ((F.E d-F.E t) ((P F) y))‖
 north (s:ℝ≥0) : F.E s x∉ F.ground ∧ 0< ((spectralP F).diagonal (F.E s x)).real (Set.Ioi 0) ∧ F.E s y∉ F.ground∧ 0<((spectralP F).diagonal (F.E s y)).real (Set.Ioi 0)
 epoch (v:ℝ) : ∃ u:ℝ, u ≠ v ∧ c/2< ‖inner ℂ x ((F.edge u-F.edge v) y)‖ ∧ c/2 < ‖inner ℂ ((P F) x) ((F.edge u-F.edge v) ((P F) y))‖
 continuousE(z:Q'): Continuous (fun (i:ℂ)=> Spectral.Alps.balcony F i z)
 holo : AnalyticOnNhd ℂ (balcony F) {z|0<z.im}
 noBelow : (spectralP F).region (Set.Iio (0:ℝ))=0
 spectrum : (Spectral.Alps.evolve F).Spectrum (spectralP F)
 unitaryArc (z:ℂ)(p:0 ≤ z.im)(x : Q'): inner ℂ x (balcony F z x) = ∫ t:ℝ, Complex.exp ((t:ℂ)*z*Complex.I) ∂(spectralP F).diagonal x
 atom : (spectralP F).region {0}=F.orth
#print Switch.mk
lemma departure {a:Axis}(Q':Hilbert)(F:OS.Semigroup Q' a)(x y:Q')(d t:ℝ≥0) (c:ℝ)(p:c>0)(g:d > 0)(v:d<t)(h:c< ‖inner ℂ x ((F.E d-F.E t) y)‖): Switch Q' F x y d t c:=by
 obtain ⟨l,l'⟩:= fail_cost F x y d t (norm_pos_iff.mp (lt_trans p h)); refine ⟨⟨p,g,v⟩,h,?_,?_,?_,balcony_cont F,balcony_holo F,bright_region F, Spectral.Alps.moment F,fun z hp x=> Spectral.Alps.balcony_law F x hp,Spectral.Alps.atom_px _⟩
 · have he := Spectral.Alps.split_cost F x y ((d:ℝ)*Complex.I) ((t:ℝ)*Complex.I); rw [balcony_high, balcony_high] at he; exact he ▸ h
 · intro i; let t₁:= strict_w F x l i; let t₂:= strict_w F y l' i; exact ⟨t₁,(Spectral.Alps.margin F _).1 t₁,t₂,(Spectral.Alps.margin F _).1 t₂⟩
 intro i; obtain ⟨d,h,h'⟩:= Spectral.Alps.reach F x y d t c i h; refine ⟨d,?_,h,h'⟩; rintro rfl; rw [sub_self] at h; simp at h; linarith -- tune
private lemma from_t {a:Axis}(Q':Hilbert)(F:OS.Semigroup Q' a)(x y:Q')(d t:ℝ≥0) (c:ℝ) (b v:ℂ)(hp:0<c)(v₁:0<d)(g:d<t)(k:inner ℂ x (F.E d y)=b)(l:inner ℂ x (F.E t y)=v)(e:c < ‖b-v‖): Switch Q' F x y d t c := departure _ _ _ _ _ _ _ hp v₁ g (by rw [ContinuousLinearMap.sub_apply,inner_sub_right,k,l]; exact e)
include V Q Qc C X
-- height identity for any marks. not assuming spatial continuity. includes cons convolution along `raise` (not just all levels for SAME position).
lemma slide_height (t:ℕ)(p:s ≤ t)(w:ℕ) : inner ℂ (ς x) ((Tη (whenly (timeMesh Λ) t w)) (ς y))=(readχ χ) t ((θ (Raise Y H Q.circuit j 0 false s t p x).val) * (relocate K j w (Raise Y H Q.circuit j 0 false s t p y).val)) :=by
 let f:=Raise Y H Q.circuit j 0 false s t p x; let g:= Raise Y H Q.circuit j 0 false s t p y; let u:=tick Y H t j 0 false (2*w) g; let z:=bornTest Y H j false t f u
 have he:z.val= θ f.val* (U (w:ℤ)) g.val:= by change θ f.val*u.val= _; rw [show u.val=(U (w:ℤ)) g.val from timed_apply Y H j false t w g]
 have hf:=(affirmation Y H V Q Qc j false C X t f u).trans (phase_read Y H V Q Qc j C t χ z).symm; change inner ℂ _ _ = (readχ χ) t z.val at hf
 have hh:= when_clock Y H V Q Qc j C t X g w  -- order `S` (not appearing) ?
 let p' := fun q:F₊ s => path Y H V Q Qc j false C X s t p q
 -- avoid rw massive goals. HH maps g projection. use congrArg₂
 let W' := Tη (whenly (timeMesh Λ) t w); have hu: W' (ς y)= (ς₁ t) u:= (congrArg W' (p' y).symm).trans hh; refine (congrArg₂ (inner ℂ) (p' x).symm hu).trans (hf.trans (congrArg ((readχ χ) t) he))
include hX hY p v ehX ehY
lemma drives : ∃ x y:F₊ s, Steams Y H V Q Qc j C z s X x y f g S T:=by
 obtain ⟨x,y,l,o,v₀,v₁,g,g'⟩:= wakes_x Y H V Q Qc j C z s p v hX hY ehX ehY; refine ⟨x,y,⟨l,v₀,g⟩,⟨o,v₁,g'⟩, temporal_eq Y H V Q Qc j C z s p v X hX hY x y l o, mean_t Y H V Q Qc j C z s p v X hX hY x y l o, fun u w p=> slide_height Y H V Q Qc j C s X x y u p w⟩ -- U notation conflict
local notation "ξ" i:max=> f*(U (i:ℤ)) g
omit ehX ehY
-- price requirement at positive physical continuum time. `W₀ w` scaling. Keep exact lower; connect real arc estimates via departure. Inputs witness ANY seam. Signature.
lemma steamsCost {c:ℝ}(b:0<c)(t: Steams Y H V Q Qc j C z s X x y f g S T)(w:ℕ)(u:0<w)(p:c< ‖u₀ (f*g) -u₀ (ξ w)‖) : Switch X.H (J) (ς x) (ς y) (W₀ 1) (W₀ (1+w)) c:=by
 let F:= J; let d₀:= W₀ 1; let d₁:= W₀ (1+w); let X':=ς x; let Y':=ς y
 have he: relocate K j (0:ℤ) g=g:= relocate_zero K j (Tower.aux_test hY.widen)
 have hl: d₀< d₁:= lt_of_not_ge (fun u'=> (by have h:=(when_le (timeMesh Λ) s (1+w) 1).1 u'; omega))
 have h₁: inner ℂ X' (F.E d₀ Y')= u₀ (f*g) := (t.slide 0).trans (congrArg u₀ (congrArg (f*·) he))
 have h₂: inner ℂ X' (F.E d₁ Y')= u₀ (ξ w):= t.slide w
 exact from_t X.H F X' Y' d₀ d₁ c (u₀ (f*g)) (u₀ (ξ w)) b (when_pos (timeMesh Λ) s 1 (by omega)) hl h₁ h₂ p
end Curtain
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern.Curtain
#print axioms Switch
#print axioms departure
#print axioms Steams
#print axioms drives
#print axioms steamsCost
#print axioms slide_height
