import YM.SU5.Reconstruction.AllGrades.Variety
import YM.SU5.Reconstruction.AllGrades.HighWire
import YM.SU5.Reconstruction.Quanta.Registrar
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
local notation "S"=>studio (tent Y H) a 0 b
#check studio_p
private lemma poleAt0 (F:studio (tent Y H) a 0 b): ∃ T:Finset Cover,InTest (tent Y H) true T b F.val ∧ Tower.region a 0 ((tent Y H).ℓ) T:=F.property
noncomputable def homePlane (s t:ℕ)(p:s≤t): S →ₗ[ℂ] S where
 toFun f:= ⟨l₀ b s (t-s) f.val, by
    obtain ⟨B,e,h⟩:= poleAt0 Y H a b f; let K':=volumeAround Λ l (t-s) B; have hs:= survives Y H V s G D e (t-s); exact ⟨K',hs,(by have ht:=parades Y H a 0 h (t-s); rw [mul_zero] at ht; exact ht)⟩⟩
 map_add' _ _:=Subtype.ext (flight_plus Y H V s G D ((poleAt0 Y H a b _).choose_spec.1) (t-s) ((poleAt0 Y H a b _).choose_spec.1))
 map_smul' _ _:=Subtype.ext (flight_scale Y H V s G D ((poleAt0 Y H a b _).choose_spec.1) (t-s) _)
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
lemma home_label {s t:ℕ} (p:s≤ t)(f:S): (hP p f).val=l₀ b s (t-s) f.val :=rfl
lemma home_join {s t u:ℕ}(p:s≤ t)(q:t≤u)(f:S): hP q (hP p f)=hP (le_trans p q) f:=by
 apply Subtype.ext; simp_rw [home_label]; unfold Garret.launch
 conv_lhs => arg 4; rw [←Nat.add_sub_of_le p]
 rw [←joined,show t-s+(u-t)=u-s by omega]
lemma home_zero (s:ℕ)(f:S): hP (le_refl s) f=f:=by apply Subtype.ext; rw [home_label,Nat.sub_self]; rfl
local notation "W"=> poleForm (tent Y H) a 0 b
lemma commissioned {s t:ℕ} (p:s≤ t)(x y:S): stream Y H G.refine s (t-s) (W x.val y.val)= W (hP p x).val (hP p y).val:=by
 obtain ⟨T,v,u⟩:=poleAt0 Y H a b x; obtain ⟨B,w,h⟩:=poleAt0 Y H a b y
 let V₀:= (axial K a 0 v)
 have hp:= luminous Y H V s G D V₀ (t-s) w (mirror_detached Λ l u h)
 have hv:= InTest.mul (V₀.mono (Finset.subset_union_left (s₂:=B))) (w.mono Finset.subset_union_right)
 rw [Bool.xor_self] at hp hv
 unfold poleForm; change (l₀ false s (t-s) _) = _
 let i:= flight_halo Y H V s G D v (t-s) a 0; rw [mul_zero] at i; rw [flight_scale Y H V s G D hv, hp,i]; rfl
-- Consumer applies either ROOT or THIS registered character. VERY same D for both. No election substitution.
structure Inspector where
 pulse : ℕ→Family (tent Y H)→ℂ
 plus(s:ℕ){F F':Family (tent Y H)}(p:TestFamily (tent Y H) true F)(q:TestFamily (tent Y H) true F'): pulse s (F+F')=pulse s F+pulse s F'
 scale(s:ℕ){F:Family (tent Y H)}(p:TestFamily (tent Y H) true F)(q:ℂ): pulse s (q • F)= q • pulse s F
 parity(s:ℕ)(x:Axis)(e: ℤ){F:Family (tent Y H)}(p:TestFamily (tent Y H) true F): pulse s (chime (tent Y H) x (2*e) F)=pulse s F
 record(s n:ℕ){F:Family (tent Y H)}(p:TestFamily (tent Y H) true F):pulse (s+n) (stream Y H G.refine s n F)=pulse s F
 gram_price (s:ℕ)(a:Axis)(b:Bool)(x:studio (tent Y H) a 0 b):0≤pulse s (poleForm (tent Y H) a 0 b x.val x.val)
-- room
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
lemma atSouth (x:S):∃ T:Finset Cover,InTest (tent Y H) true T b x.val ∧ Tower.region a 0 ((tent Y H).ℓ) T:=poleAt0 Y H a b x
lemma printedS (x y:S):TestFamily (tent Y H) true (W x.val y.val):= aux_test (NorthTapes.statement a 0 (poleAt0 Y H a b x).choose_spec.1 (poleAt0 Y H a b y).choose_spec.1)
noncomputable def mapRoof : S→ₗ⋆[ℂ] S→ₗ[ℂ] ℂ where

 toFun x:= {
      toFun:=fun y=> Ω s (W x.val y.val)
      map_add':=fun y f=>by change Ω s (W x.val (y.val+f.val))=_; unfold poleForm; rw [mul_add, smul_add]; exact P.plus s (printedS Y H a b x y) (printedS Y H a b x f)
      map_smul':=fun c y=>by change Ω s (W x.val (c • y.val))=_; unfold poleForm; rw [Algebra.mul_smul_comm,smul_comm]; exact P.scale s (printedS Y H a b x y) c }
 map_add' R b':= LinearMap.ext fun f=>by
    change Ω s (W (R.val+b'.val) f.val)=_+_; unfold poleForm; rw [mirror_plus,add_mul,smul_add]; exact P.plus s (printedS Y H a b R f) (printedS Y H a b b' f)
 map_smul' c R:= LinearMap.ext fun f=>by change Ω s (W (c • R.val) f.val)= (star c) • _; unfold poleForm; rw [mirror_scale,Algebra.smul_mul_assoc,smul_comm]; exact P.scale s (printedS Y H a b R f) _
noncomputable def carrier : Fleet (S) where
 raise:= homePlane Y H V G D a b
 cash:= fun s=> mapRoof Y H G a b s P
 pos s F:=P.gram_price ..
 spends {s t} h x y:= by change Ω s (W x.val y.val) = Ω t _; have h':= P.record s (t-s) (printedS Y H a b x y); rw [Nat.add_sub_of_le h,commissioned Y H V G D a b h] at h'; exact h'.symm -- Nat.add_sub? check
 seed:=home_zero Y H V G D a b
 joint:=home_join Y H V G D a b
local notation "F₊" => carrier Y H V G D a b P
noncomputable abbrev Works : Hilbert:= (F₊).Room
lemma link_raised {s t:ℕ}(p:s≤ t): (F₊).raise _ _ p=homePlane Y H V G D a b s t p:=rfl
noncomputable def badge : S →ₗ[ℂ] Works Y H V G D a b P:= (F₊).load s
local notation "Bp" s:max => badge Y H V G D a b s P
lemma measures_here(x y:S): inner ℂ ((Bp s) x) ((Bp s) y)= Ω s (W x.val y.val):= (F₊).paysHere s x y
lemma measures_forever {s t u:ℕ}(p:s≤u)(q:t≤u)(x y:S) : inner ℂ ((Bp s) x) ((Bp t) y)= Ω u (W (hP p x).val (hP q y).val) :=(F₊).pays x y p q
lemma badges_join {s t:ℕ}(p:s≤t)(x:S):(Bp s) x= (Bp t) (hP p x):= (F₊).rise p x
lemma badges_roll : Dense (⋃ i:ℕ,Set.range (Bp (i+s))):=(F₊).dense s
lemma badges_ext{M:Type*}[NormedAddCommGroup M][NormedSpace ℂ M][CompleteSpace M]{X Z: (Works Y H V G D a b P)→L[ℂ] M}(p:∀ i:ℕ,s ≤ i →∀ x:S, X ((Bp i) x) = Z ((Bp i) x)):X=Z:=(F₊).limit_ext s p
lemma inspector_seed (x:S):0≤ Ω s (poleForm K a 0 b x.val x.val):=P.gram_price ..

private lemma tweak (J:Calibration)(A:Side): Heat.gaugeShift A 0=0:=by simp [Heat.gaugeShift]
noncomputable def atlasAt : Inspector Y H G where
 pulse := E
 plus s {_ _} p t:= E_add Y H V s p t
 scale s {_} x c:= E_scale Y H V s x c
 parity s j z {_} ht:= PhaseChoice.shift_eFull Y H V j ht (2*z)
 record s n {_} p:= (proceeds Y H G.history.circuit s n p.paid.choose_spec).2
 gram_price s a b x:=by obtain ⟨S',p,q⟩:=atSouth Y H a b x; rw [←tweak K Λ.block] at q; simpa only [Heat.gaugeShift, mul_zero] using NorthTapes.election0 Y H V s a 0 p q

variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "gV" => price Y H V G C j χ
noncomputable def voterAt : Inspector Y H G where
 pulse:= fun s=> gV s false
 plus s {_ _} p q:= price_add Y H V G C j χ s p.paid.choose_spec q.paid.choose_spec
 scale s {_} p q:= price_smul Y H V G C j χ s p.paid.choose_spec q
 parity s a z {_} p:= price_slide Y H V G C j χ s a z p.paid.choose_spec
 record s n {_} p:= context_lift Y H V G C j χ p.paid.choose_spec
 gram_price s a b x:=by obtain ⟨S',p,q⟩:=atSouth Y H a b x; rw [←tweak K Λ.block] at q; simpa only [Heat.gaugeShift, mul_zero] using price_aligned Y H V G C j χ s a 0 p q
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.badges_roll
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.measures_forever
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.atlasAt
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.voterAt
