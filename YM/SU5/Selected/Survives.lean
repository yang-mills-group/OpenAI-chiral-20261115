import YM.SU5.Selected.Interpret

/-!
# The native mixed-test selection problem, resolved on the elected extension

This is in the **multi-resolution Euclidean** hierarchy. Interpretation:
correlation between the physical pair's gauge and chiral matter in precisely
the sense of nonfactorization of the Satin law (Parcel). Applies to selected
vacuum component in the actual spectrum of the compressed history. Does not
supply conclusions in a prospective continuum spacetime reconstruction (which
would require e.g. specifying its observables and preserving these readings).
Does not require purchasing all-scale uniform resource per fixed observing
insertion. Does not use histories of other models or legislatures. Doesn't
compare systems defined by different physical rules; doesn't claim dynamics
of confinement etc. Includes exact SCOPE of the singlet criterion. In
particular the nonfactorization uses charged-extension marginals, and in the
fixed-separation assertion the interaction is a single observable (see
`Fixture`). The pure/no-split result is in B (positive functionals on
stationC), see also joint ground test.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
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
open Theory
variable (D : Axis) (R : ∀ j:Axis, Arena Y H G.history.circuit j 0 false)
local notation "T" j:max=> bank Y H V G j false (R j) D (R D)
local notation "A₀"=>catalog Y H V G D false (R D)
local notation "S₀" j:max=>stationC Y H V G j false (R j)

noncomputable def restore {J:Calibration}(f:observable J true) : observable J false:=⟨f.val,f.property.1,by simp⟩
noncomputable def observe {J:Calibration} {f:Family J} (g: TestFamily J true f) : observable J false:=⟨f,g,by simp⟩ -- shadow macro K
variable (x:Resident (catalog Y H V G D false (R D)))
local notation "X"=> markE Y H V G false D (R D)

noncomputable def evaluate (s:ℕ)(f:Family (tent Y H)) := if h:TestFamily K true f then markE Y H V G false D (R D) x s (observe h) else 0
local notation "Mx"=>evaluate Y H V G D R x
lemma evaluates (s:ℕ) (f:observable (tent Y H) false) : (Mx s f.val)=X x s f := dif_pos f.property.1
open CF.Pannier.Chancel
lemma consistency (T₀:Finset Cover) (s:ℕ) : Scopes (tent Y H) T₀ (Mx s) := by
  constructor
  · unfold evaluate; rw [dif_pos TestFamily.oneT]; exact normalizedAt Y H V G false D (R D) x s rfl
  · intro f g p q; let x' := aux_test p; let y:=aux_test q
    unfold evaluate; rw [dif_pos (x'.add y),dif_pos x',dif_pos y]; exact addAt Y H V G false D (R D) x s rfl
  · intro f p z; let x' := aux_test p; unfold evaluate; rw [dif_pos (x'.scale _),dif_pos x']; exact scaleAt Y H V G false D (R D) x s _ rfl
  intro a f t p q h; let x':=aux_test p; let y:=aux_test q
  unfold evaluate; rw [dif_pos x',dif_pos y]; apply congrArg (fun a:A₀=>eye x a); exact Subtype.ext (cap_ward Y H V G D false (R D) T₀ s (observe x') (observe y) p q h)

-- cap (not the reading) of Lode is already zero; therefore the alternatives where even the compressed products would produce the same expectation as uncompressed coincident joint reading for ALL these ingredients do not actually hold.
lemma erased (s:ℕ) (a:observable (tent Y H) false) {u:ℕ} {v:Fin u → Cover} {z:SU.Slot} {t:Finset Cover}(h:Injective v)
    (p:a.val∈ Lode K (Window.family z) v t) : seal₀ Y H V G D false (R D) s a=0 := by
  refine byEye _ (fun x => ?_)
  exact ((evaluates Y H V G D R x s a).symm).trans
    ((consistency Y H V G D R x t s).footprint h p)
where
 byEye {Tt:Type} [CommCStarAlgebra Tt] (a:Tt) (h:∀ x:Resident Tt, eye x a=0):a=0:=by
  apply (gelfandStarTransform Tt).injective; ext1 x; rw [map_zero]; exact h x

structure ExtremeReceipt : Prop where
  rank (j:Axis) : (T j).FixedPhase x
  only_vac (j:Axis)(v : fiberH Y H V G j false (R j) D (R D) x)
    (space : ∀ u:Trans j,∀ i, fiberOp Y H V G j false (R j) D (R D) x (shiftOp Y H V G j false (R j) u i) v=v)
    (time : ∀ i, fiberOp Y H V G j false (R j) D (R D) x (heatOp Y H V G j false (R j) i) v=v):
    ∃ c:ℂ,v=c • fiberVec Y H V G j false (R j) D (R D) x
  normed (j:Axis):‖fiberVec Y H V G j false (R j) D (R D) x‖=1
  no_split (j:Axis) (F J:(S₀ j) →ₚ[ℂ] ℂ) (a b:ℝ) (h:0<a) (t:0<b) (p:F 1=1) (q:J 1=1)
    (e:∀ i,fiberState Y H V G j false (R j) D (R D) x i=(a:ℂ)*F i+(b:ℂ)*J i): F=fiberState Y H V G j false (R j) D (R D) x ∧ J=fiberState Y H V G j false (R j) D (R D) x
  invariant (j:Axis) : ∀ u∈approach Y H V G j false (R j),
    fiberOp Y H V G j false (R j) D (R D) x u (fiberVec Y H V G j false (R j) D (R D) x)=fiberVec Y H V G j false (R j) D (R D) x

lemma extremal_usual : ∀ᵐ x∂(residents Y H V G false D (R D)), ExtremeReceipt Y H V G D R x := by
  filter_upwards [ae_all_iff.mpr (fun j:Axis=> almostGround Y H V G j false (R j) D (R D))] with x hx
  refine ⟨hx,fun j x' v t=>Transaction.show_fixed _ _ (hx j) x' ?_,fun j=>Transaction.show_norm _ _,fun j _ _ a b h t p q e=>Transaction.cannot_split _ x (hx j) p q a b h t e, fun j u v=> Transaction.show_queue (T j) x _ v⟩
  intro i hi; rcases hi with ⟨x,rfl⟩|⟨⟨a,b⟩,rfl⟩
  · exact t _
  exact v a b

structure Seen (s : ℕ) (z : SU.Slot) (q d w:ℕ) (o:Cover) (f:observable K true) (a:ℝ) : Prop where
  fixture : Fixture Y H V G z q d w o s f a
  station (j:Axis) (t:S₀ j) : inner ℂ (fiberVec Y H V G j false (R j) D (R D) x)
        (fiberOp Y H V G j false (R j) D (R D) x t (fiberVec Y H V G j false (R j) D (R D) x))= fiberState Y H V G j false (R j) D (R D) x t
  read (r:ℕ)(j: Axis)(c:Veranda Y H (s+r) j false (upward Y H G.history false (restore f) s r)) :
    inner ℂ (fiberVec Y H V G j false (R j) D (R D) x)
        (fiberOp Y H V G j false (R j) D (R D) x (boxElement Y H V G j false (R j) (s+r) c.span c.fwd c.pos) (fiberVec Y H V G j false (R j) D (R D) x))= Mx s f.val
  scopes (s:ℕ)(Tq: Finset Cover) : Scopes K Tq (Mx s)
  positive : 1/4≤ ‖Mx s f.val‖
  separates : ¬ CF.Pannier.Chancel.Parcel (tent Y H) (Window.family z) (booty o d q) (Sen o (payout d q w)) (Mx s)
  component : ExtremeReceipt Y H V G D R x
  margin (g:Family K→ℂ)(u:Scopes K (Sen o (payout d q w)) g)
    (p: CF.Pannier.Chancel.Parcel (tent Y H) (Window.family z) (booty o d q) (Sen o (payout d q w)) g) : 1/4 ≤ ‖Mx s f.val-g f.val‖
  -- explicit product detection rather than rule failure. Bounded by these inequalities: upper read of pure matter ZERO, strict lower on one product with gauge.
  assay : ∃ (a:Family K) (F:PairsC→ℂ), (a:Family K)∈ Lode K (Window.family z) (booty o d q) (Sen o (payout d q w)) ∧
    Coeff false (Sen o (payout d q w)) F ∧ Mx s a=0 ∧ ‖Mx s (scalar K F*a)‖ > 0

theorem choose (s:ℕ)(z:SU.Slot) {q d w:ℕ} {o:Cover} {f:observable K true}{a:ℝ}
    (p:Fixture Y H V G z q d w o s f a) : ∃ x, Seen Y H V G D R x s z q d w o f a := by
  have h:=p.actual
  let A' := seal₀ Y H V G D false (R D) s (restore f)
  obtain ⟨x,u,t⟩ := weighty Y H V G false D (R D) A' (1/4)
    (h.trans_eq (congrArg norm (Vacancy.inspected (F:=restore f) Y H V s G.history G.clipped D false (R D)).symm)) (extremal_usual Y H V G D R)
  let M := evaluate Y H V G D R x
  let w' : M s f.val= X x s (restore f):= evaluates Y H V G D R x s (restore f)
  have hE:1/4≤‖M s f.val‖:=w'.symm ▸ (show 1/4≤ ‖X x s (restore f)‖ from t)
  let v:= consistency Y H V G D R x (Sen o (payout d q w)) s
  have hv : ¬CF.Pannier.Chancel.Parcel K (Window.family z) (booty o d q) (Sen o (payout d q w)) (M s) := by
    intro g; rw [show M s f.val=0 from v.detects p.anchors.1 g p.dressed, norm_zero] at hE; norm_num at hE
  refine ⟨x,p, fun j b=> fiber_mean Y H V G j false (R j) D (R D) x b, ?_, fun s t=>consistency Y H V G D R x t s, hE,hv,u,?_,?_⟩
  · intro r j c
    exact (placed_sampling Y H V G j false (R j) D (R D) x (s+r) _ c).trans ((at_refine Y H V G false D (R D) x s (restore f) r).trans w'.symm)
  · intro G' u t
    rw [show G' f.val=0 from u.detects p.anchors.1 t p.dressed, sub_zero]
    exact hE
  unfold CF.Pannier.Chancel.Parcel at hv; push Not at hv
  obtain ⟨a,u,f,t,h⟩ := hv
  refine ⟨a,f,u,t,v.footprint p.anchors.1 u,norm_pos_iff.mpr ?_⟩
  rw [show M s a=0 from v.footprint p.anchors.1 u,mul_zero] at h; exact h

lemma there_is {C Z:ℝ} (D:Axis)(z:SU.Slot)(o:Cover){q d w:ℕ}
    (p:Papal.Cornet Y H q d w C Z) : ∀ᶠ s in atTop, ∃ (x:Resident (catalog Y H V G D false (R D))) (f:observable K true) (a:ℝ), Seen Y H V G D R x s z q d w o f a:= by
  filter_upwards [freeze_probe Y H V G z o p] with s ⟨f,a,t⟩
  obtain ⟨x,u⟩:= choose Y H V G D R s z t; exact ⟨x,f,a,u⟩

/-- This uses no hypothesis assuming Passage to Minkowski or estimates being made on an opaque
`Parcel` object. Actual C*-pure and grid-joint-ground component of the same elected Universal law
E, with nonfactorization in the specified sense of the represented local correlated variables. -/
theorem chosen_mixed (ε η:ℝ)(u:0<η)(D:Axis) :
    ∃ (Λ:Preparation)(l:ℕ), ε<Λ.x ∧ Λ.d≤η ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H: Real.exp 1≤Λ.x) (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (q d w:ℕ)
        (i k:ℕ→ℕ)(I:ℕ→Family (tent Y H)→ℕ→ℂ) (E:ℕ→Family (tent Y H)→ℂ)
        (V:Universal Y H i k I E) (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
        (R:∀j:Axis,Arena Y H G.history.circuit j 0 false),
        ∀ (o:Cover) (z:SU.Slot), ∃ (s:ℕ) (x:Resident (catalog Y H V G D false (R D))) (f:observable (tent Y H) true) (a:ℝ), Seen Y H V G D R x s z q d w o f a := by
  obtain ⟨P',l,Z,p₀,p₁,p₂,H',Y',q,d,w,C,p₃,a,b,J,E,V',⟨G⟩,_⟩:= Papal.mixed_law_with_ground ε η u
  let T':= fun j=> Classical.choice (voyage_H Y' H' V' G.history.circuit j 0 false)
  exact ⟨P',l,p₀,p₁,p₂,H',Y',q,d,w,a,b,J,E,V',G,T',fun x i=>(there_is Y' H' V' G T' D i x p₃).exists⟩
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.extremal_usual
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.erased
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.chosen_mixed
#check @YM.CF.Buffered.Afterglow.Tower.PhaseChoice.chosen_mixed
