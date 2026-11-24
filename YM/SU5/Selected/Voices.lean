import YM.SU5.Selected.Held

/-! Faithful presentation of chosen GNS space: only Field (and choir) needed for dense span.
Data WRT marked valuations. `replica` inputs are actually coherent; applies strict=false to
include gauge charge extension. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
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
open MeshClock Set
local notation "M"=> timeMesh Λ
local notation "St"=> stationC Y H V G j strict C
local notation "Uk"=> shifts Y H V G j strict C
local notation "Ux"=> shiftOp Y H V G j strict C
local notation "Bx"=> boxes Y H V G j strict C
local notation "Be"=>boxElement Y H V G j strict C
local notation "Qe"=>heatOp Y H V G j strict C

namespace Acting
variable (T:Acting Y H V G j strict C)(s : ℕ)
local notation "V₀"=>T.ground
local notation "X"=>T.space
local notation "PS"=>T.showL
local notation "Qx"=>clock Y H V G j strict C T
local notation "Vx"=>Acting.lattice Y H V G j strict C T
local notation "O" s:max x:max p:max=> watches Y H V G j strict C T s _ x p
lemma still_engine {q:St} (h:q.val∈Submonoid.closure (Uk)) : PS q V₀=V₀:=by
  have he {b:A→L[ℂ]A} (p:b∈Submonoid.closure Uk) : ∃ x:St,x.val=b∧ PS x V₀=V₀ := by
    induction p using Submonoid.closure_induction with
    | mem x p=>
      obtain ⟨a,v,rfl⟩:=p
      exact ⟨_,rfl,T.vacuum_space Y H V G j strict C a v⟩
    | one=> exact ⟨1,rfl,by rw [map_one]; rfl⟩
    | mul _ _ _ _ b c=>
      obtain ⟨x,rfl,u⟩:=b; obtain ⟨y,rfl,v⟩:=c
      exact ⟨x*y,rfl,by rw [map_mul]; change PS x (PS y V₀)=_; rw [v,u]⟩
  obtain ⟨a,f,p⟩:= he h
  rw [← (Subtype.ext f : a=q)]; exact p

-- every vector in Field is an Entry already on its rung at every sufficiently big width.
private theorem fits (q:Fₛ s) : ∃ i:ℕ,0 < i∧∃ x:Entry Y H s j strict i,x.val=q:=
 ((eventually_gt_atTop (0:ℕ)).and (field_entry Y H j strict s q)).exists
include T C
lemma width_same {u w:ℕ}(x:Entry Y H s j strict u)(p:0<u)(y:Entry Y H s j strict w)(q:0<w)
    (e:x.val=y.val) : (O s x p) V₀=(O s y q) V₀ := by
  wlog h:u ≤ w generalizing u w x y
  · exact (this y q x p e.symm (le_of_not_ge h)).symm
  obtain ⟨c,rfl⟩:= Nat.exists_eq_add_of_le h
  have ht : Be s (u+c) y q= Be s u x p * Qe (whenly M s c):=Subtype.ext (shape_right Y H V s G.history G.clipped j strict C u u x p c y (congrArg (fun a:Fₛ s=>a.val) e.symm))
  unfold watches; rw [ht,map_mul]; change _= PS _ (Qx _ V₀); rw [vacuum_time]

noncomputable def solo (q:Fₛ s): X:= watches Y H V G j strict C T s _ (fits Y H j strict s q).choose_spec.2.choose (fits Y H j strict s q).choose_spec.1 V₀
local notation "P₀" s:max a:max=>solo Y H V G j strict C T s a
lemma solo_info (x:Fₛ s){u:ℕ}(e:Entry Y H s j strict u)(p:0<u)(h:x = e.val): P₀ s x = (O s e p) V₀ := by
  unfold solo; apply T.width_same Y H V G j strict C s _ _ _ _
  exact ((fits Y H j strict s x).choose_spec.2.choose_spec).trans h
noncomputable def voice : (Fₛ s) →ₗ[ℂ] X where
 toFun := solo Y H V G j strict C T s
 map_add' x y:= by
    obtain ⟨u,h,⟨p,p'⟩,⟨q,q'⟩,r,e⟩ := ((eventually_gt_atTop (0:ℕ)).and ((field_entry Y H j strict s x).and
      ((field_entry Y H j strict s y).and (field_entry Y H j strict s (x+y))))).exists
    rw [solo_info Y H V G j strict C T s _ p h p'.symm, solo_info Y H V G j strict C T s _ q h q'.symm,
      solo_info Y H V G j strict C T s _ r h e.symm]
    have he: r.val=p.val+q.val:=by rw [p',q']; exact e
    have hr : Be s u r h=Be s u p h + Be s u q h :=Subtype.ext (box_add Y H V G j strict C s u p q r h (congrArg (fun t:Fₛ s=>t.val) he))
    unfold watches; rw [hr,map_add]; rfl
 map_smul' c x:= by
    obtain ⟨u,h,⟨p,p'⟩,q,q'⟩:=((eventually_gt_atTop (0:ℕ)).and ((field_entry Y H j strict s x).and (field_entry Y H j strict s (c•x)))).exists
    rw [solo_info Y H V G j strict C T s _ p h p'.symm, solo_info Y H V G j strict C T s _ q h q'.symm]
    unfold watches
    have he:q.val=c • p.val:=p'.symm ▸ q'
    rw [show Be s u q h=c • Be s u p h from Subtype.ext (box_scale Y H V G j strict C s u p q h c (congrArg (fun t:Fₛ s=>t.val) he)),map_smul]; rfl
local notation "γ" s:max x:max=>voice Y H V G j strict C T s x
lemma notes {i:ℕ}(h:0 < i)(x:Entry Y H s j strict i): γ s x.val=(O s x h) V₀:=solo_info Y H V G j strict C T s x.val x h rfl

lemma climbs (x:Fₛ s)(t:ℕ)(p:s≤t): γ t (Raise Y H G.history.circuit j 0 strict s t p x)=γ s x:=by
  obtain ⟨u,h,x,rfl⟩ := fits Y H j strict s x
  let Q:=furnished Y H s G.history j strict u x t p
  have hw:=same_box Y H V G j strict C T t p x h
  change γ t Q.val= _
  rw [T.notes Y H V G j strict C s h, T.notes Y H V G j strict C t (Nat.mul_pos (pow_pos Λ.R.L.property _) h)]
  exact congrArg (fun a:(X).Op=>a V₀) hw.symm
lemma unison : (γ s (unity Y H j 0 strict s))= V₀:= (notes Y H V G j strict C T s Nat.zero_lt_one (SlabMark.identity Y H s j strict 1)).trans
  ((congrArg (fun x : (X).Op => x V₀) (blank_clock Y H V G j strict C T (s:=s) Nat.zero_lt_one)).trans (vacuum_time ..)) -- Field submodule no One

-- action of boxes. for `t≥s`, promote operator as in T.same_box, then use act_voice.
lemma act_voice(u:ℕ)(x:Entry Y H s j strict u)(p:0<u)(a:Fₛ s):
    (O s x p) (γ s a)=γ s (slabT Y H s j strict u x a):=by
  obtain ⟨w,h,y,rfl⟩ := fits Y H j strict s a
  let f := edit Y H s j strict u w x y
  have hv: slabT Y H s j strict u x y.val=f.val := Subtype.ext ((slab_eq ..).trans (editor ..).symm)
  rw [hv,T.notes Y H V G j strict C s (show 0<u+w from by omega) f,T.notes Y H V G j strict C s h y]; exact congrArg (fun x:(X).Op=>x V₀) (box_product ..)

lemma clock_voice (u:ℕ)(x:Fₛ s) : Qx (whenly M s u) (γ s x)=γ s (tick Y H s j 0 strict (2*u) x) := by
  rcases Nat.eq_zero_or_pos u with rfl|p
  · rw [when_zero,clock_zero, Nat.mul_zero, show tick Y H s j 0 strict 0 x=x from ?_]; rfl
    apply Subtype.ext; change chime K j (Heat.gaugeShift Λ.block ((0:ℕ):ℤ)) _=_
    rw [show Heat.gaugeShift Λ.block ((0:ℕ):ℤ)=0 by unfold Heat.gaugeShift; norm_num]
    exact Tower.wake _ _ (field_test Y H s j 0 strict x).paid.choose_spec
  let y:= SlabMark.identity Y H s j strict u
  rw [← T.blank_clock Y H V G j strict C (s:=s) p, act_voice]
  apply congrArg _; apply Subtype.ext; exact one_mul _ -- order
lemma space_voice (a:Trans j) (v:ℤ) (x:Fₛ s) :
    Vx a (notch M s v) (γ s x)=γ s (sail Y H s j 0 strict (a:Axis) a.property (2*v) x):=by
  obtain ⟨u,p,x,rfl⟩ := fits Y H j strict s x
  let t:=notch M s v; let y:=alongS Y H s j strict u x a v; change Vx a t (γ s x.val)=γ s y.val
  rw [T.notes Y H V G j strict C s p x,T.notes Y H V G j strict C s p y]
  have h:Vx a t * O s x p=O s y p * Vx a t:=T.box_shift Y H V G j strict C x p a v
  change (Vx a t * O s x p) V₀=_; rw [h]; exact congrArg (O s y p) (vacuum_space ..)
end Acting
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.solo_info
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.climbs
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.clock_voice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.space_voice
