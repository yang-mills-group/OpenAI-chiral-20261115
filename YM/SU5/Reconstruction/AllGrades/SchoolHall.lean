import YM.SU5.Reconstruction.AllGrades.Wander
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open WindRose PolarArchives ConePrice SelectionAnalysis Chambers Brazier
variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "mK"=> marks (timeMesh Λ)
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Ω₀"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped a false (C a)
local notation "F₊"=> Domain Y H G false (flank a 0)
local notation "Sm" m:max=> strip a (-(m:ℝ)) (m:ℝ)
local notation "Qt" m:max=> flank a (m:ℝ)
local notation "bM" d:max=> strip a (-d) d
local notation "A₀"=> atlasAt Y H V G
local notation "Pt" m:max=> Pub Y H a m
local notation "Bk" d:max f:max => (((badge Y H V G D a b d (atlasAt Y H V G)) f))
local notation "Px" u:max f:max=> ticket Y H G u f
local notation "rF"=> studio (tent Y H) a 0 b
local notation "rW"=> studio (tent Y H) a 0 false
lemma stripSupport_min (Z:Set RSpace)(hv:IsCompact Z):∃ d:ℝ,0≤d∧ Z⊆strip a (-d) d:=by
 obtain ⟨u,A'⟩:= (hv.image (continuous_apply a)).bddAbove; obtain ⟨v,B⟩:= (hv.image (continuous_apply a)).bddBelow
 refine ⟨max 0 (max u (-v)),le_max_left ..,fun i t=>?_⟩
 have ht:=mem_image_of_mem (fun x:RSpace=>x a) t
 change -_≤ i a∧ i a≤ _; constructor; swap; · exact (A' ht).trans ((le_max_left ..).trans (le_max_right ..))
 linarith [le_max_right u (-v), le_max_right 0 (max u (-v)), (show v≤ i a from B ht)]
lemma coincide_at (f:Dome (tent Y H))(s:ℕ):∃ d:ℝ,0≤d∧ f∈ insideAt Λ l K false (strip a (-d) d) s:=by
 let S:=( (marque (tent Y H)).1 f.property).paid.choose
 have h:InTest K true S false f.val := _root_.Classical.choose_spec (((marque (tent Y H)).1 f.property).paid)
 obtain ⟨d,d',hd⟩:= stripSupport_min a (bufferedHull Λ l s S) (compact_hull ..)
 exact ⟨d,d',(mem_insideAt ..).2 ⟨⟨_,h,(supported_iff ..).2 hd⟩,nofun⟩⟩
lemma smoothEarn (d:ℝ)(m:mK)(h:d< (m:ℝ))(t:0≤d): Disjoint (strip a (-d) d) (mirrorE a 0 '' flank a (m:ℝ)) ∧ Disjoint ((strip a (-d) d) ∪ mirrorE a 0 '' flank a (m:ℝ)) (flank a (m:ℝ)) :=by
 have hz : ∀ x∈ mirrorE a 0 '' flank a (m:ℝ), x a ≤ -(m:ℝ):=by rintro _ ⟨x,g,rfl⟩; simp [mirrorE]; exact g
 refine ⟨disjoint_left.mpr (fun x t v=>?_ ),disjoint_left.mpr (fun x v u=>?_ )⟩ -- bind implicit? sets
 · linarith [hz _ v,(show -d≤ x a from t.1)]
 replace u:(m:ℝ)≤x a:=u; rcases v with w|w;· linarith [(show x a≤ d from w.2)]
 linarith [hz _ w]

-- apportion with actual probes
noncomputable def pour (x:rF) : Dome (tent Y H):= ⟨W x.val x.val,printedS Y H a b x x⟩
noncomputable def tapK (x:rF): Domain Y H G false univ:= ⟨Px s (pour Y H a b x),ticket_loose ..⟩
local notation "T₀"=> tapK Y H G a b s
lemma shapes_at (x:studio (tent Y H) a 0 b) {d:ℝ} (v: pour Y H a b x∈ insideAt Λ l K false (strip a (-d) d) s)(m:mK)(w:d ≤ (m:ℝ)): (T₀ x).val∈ Domain Y H G false (Sm m):= by
 apply ticket_mem Y H G (insideAt_mono _ v)
 rintro y g; exact ⟨le_trans (neg_le_neg w) g.1,g.2.trans w⟩
noncomputable def loan (x:rF)(y:rW):rF:=by
 let p:=atSouth Y H a b x; let q:= atSouth Y H a false y; let B:= p.choose ∪ q.choose; have ht:= InTest.mul ((p.choose_spec.1).mono (Finset.subset_union_left (s₂:=q.choose))) ((q.choose_spec.1).mono Finset.subset_union_right); rw [Bool.xor_false] at ht; exact ⟨x.val*y.val,⟨B,ht,fun i u=> (Finset.mem_union.mp u).elim (p.choose_spec.2 i) (q.choose_spec.2 i)⟩⟩
noncomputable def educate (m:mK)(h:0 < m)(s:ℕ)(y:Dome K)(p:y ∈ insideAt Λ l K false (Qt m) s): rW:= by
 let Z:= y.val; refine ⟨Z,?_⟩; have q: y.val ∈ purpose K (meshface (Λ:=Λ) 0 s) a false:= (positive_today Y H a s y).1 (insideAt_mono (show flank a (m:ℝ)⊆flank a 0 from fun x h'=> (show (0:ℝ)≤ (m:ℝ) from h.le).trans (show (m:ℝ) ≤ x a from h')) p)
 obtain ⟨K',hq,ht⟩:= (((purpose_ok ..).1 q).1 : ∃ S, InTest K true S false y.val ∧ Tower.region a _ _ S); rw [area0] at ht; exact ⟨K',hq,ht⟩
lemma root_bill (t:ℕ)(e':s≤ t) (x:rF) (m:mK)(p:0 < m)(u:F₊)(g:Dome (tent Y H))(w:g∈ insideAt Λ l K false (flank a (m:ℝ)) t)(e:(Pt m) u.val=Px t g){d:ℝ}(v:pour Y H a b x∈ insideAt Λ l K false (bM d) s)(h:d<(m:ℝ))(j₁:0≤d):
    ∀ q: flipMark a (tent Y H) ((Pt m) u.val) * (T₀ x).val * (Pt m) u.val∈ Domain Y H G false univ,
    courseValue Y H V G ⟨flipMark a (tent Y H) ((Pt m) u.val)*(T₀ x).val* (Pt m) u.val,q⟩ =
      let r:= loan Y H a b (hP e' x) (educate Y H a m p t g w); inner ℂ (Bk t r) (Bk t r):=by
 intro q; dsimp only
 let U₁:= flank a (m:ℝ); let U₂:= mirrorE a 0 '' U₁
 let f:= pour Y H a b x
 let u':= educate Y H a m p t g w; let y':= hP e' x
 let Z:=spreadTo Y H G s t f; let v':Z∈ insideAt Λ l K false (bM d) t:= inside_spread Y H G v e'
 let X:=aureole K a 0 g* Z*g; have k:aureole K a 0 g∈ insideAt Λ l K false U₂ t:= mirror_inside Y H a g _ w
 obtain ⟨b',H'⟩:= smoothEarn a d m h j₁ -- args order?
 have hz: (aureole K a 0 g*Z)∈ insideAt Λ l K false ((bM d)∪ U₂) t:= (insideAt Λ l K false ((bM d)∪U₂) t).mul_mem (insideAt_mono Set.subset_union_right k) (insideAt_mono Set.subset_union_left v')
 have H₁: flipMark a (tent Y H) ((Pt m) u.val)*(T₀ x).val* (Pt m) u.val=Px t X:=by unfold X; rw [e,flipMark_ticket,ticket_separated Y H G hz w H',ticket_separated Y H G k v' b'.symm,ticket_spread Y H G e']; rfl
 rw [show (⟨_,q⟩:Domain Y H G false univ)= ⟨Px t X,ticket_loose ..⟩ from Subtype.ext H₁,course_ticket_val,measures_here]
 change E t (Θ a 0 u'.val * Z.val * u'.val)= E t (W (y'.val*u'.val) (y'.val*u'.val)); unfold Z; rw [spreadTo_val,show f.val=poleForm K a 0 b x.val x.val from rfl, commissioned Y H V G D a b e']; exact congrArg (E t) (Garret.party a 0 (atSouth Y H a b y').choose_spec.1 (atSouth Y H a false u').choose_spec.1)


end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.root_bill
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.educate
