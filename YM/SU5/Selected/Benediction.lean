import YM.SU5.Selected.PhysicalPhase
/-!
# Gram of the positive Euclidean color room. Identifying phase in THAT interpretation

No separability assumption on continuum fields, only on earned-operator ensemble. At each level,
representatives can cancel in the supercommutative chiral mark even algebra before conditioning;
the positivity check is at its actual size reading, not a norm-preserving embedding theorem for those
marks. Prove actually the Gram selected reconstructed at the origin of each axis on the whole
cross-resolution well (upwards and with SU invariant boundary anticancel) is represented on
`ColorHil`, with **dense** label vacuum conditions; this physical system includes the determining
Euclidean polynomial observables as inserted in the actual law. The space is allowed to be
smaller than the full cloud extension space `PortionHil` (actually may also be equal, not asked),
and we don't assert yet these spaces or the later analytic continuation have locality/time smearing
then (those require more than Euclidean determining matter support).
-/
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
set_option maxHeartbeats 140000
open Tapestry.Exhibition Tapestry.Altitude Set
section
open scoped Pointwise
variable {I:Type}{H:Hilbert}{A:Type} [CStarAlgebra A] (V:H)(W: Submodule ℂ H)
local notation "S" b:max=> (StarAlgebra.adjoin ℂ b).topologicalClosure
include W V
lemma fill_all (A' : Set A) (F : (S A') →⋆ₐ[ℂ] H.Op) (d:DenseRange (fun x=> F x V)) (c:Continuous (fun x=>F x V))
    (h:∀ z∈Submonoid.closure (A' ∪ star A'), ∃ b:S A', b.val=z ∧ F b V∈ W) : Dense (W:Set H):=by
  let T:= (S A'); let D:= W.comap ((ContinuousLinearMap.apply ℂ H V).toLinearMap.comp F.toLinearMap); let K:= T.subtype.toLinearMap
  have ht : Submodule.span ℂ (Submonoid.closure (A'∪star A') : Set A)≤ D.map K:= by apply Submodule.span_le.mpr; intro u p; obtain ⟨b,t,v⟩:= h u p; exact ⟨b,v,t⟩
  let P:= StarAlgebra.adjoin ℂ A'; let f:P→ T:= StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure P)
  have p:DenseRange f:= denseRange_inclusion_iff (StarSubalgebra.le_topologicalClosure P)|>.2 Subset.rfl
  apply (d.comp p c).mono; rintro _ ⟨i,rfl⟩; have h:(f i).val∈ (StarAlgebra.adjoin ℂ A').toSubalgebra.toSubmodule:= i.property; rw [StarAlgebra.adjoin_eq_span] at h
  obtain ⟨b,v,t⟩:=ht h; change F (f i) V∈ W; rwa [← (show b=f i from Subtype.ext t)]
omit W
lemma fly_through (g : I → A) (F:A →⋆ₐ[ℂ] H.Op) (p:∀i, F (g i) V=V) (l:List I) (x:A): F (x*(l.map g).prod) V=F x V:=by
  rw [map_mul]; change F x (F _ V)=_; apply congrArg; induction l with|nil=>simp |cons i l h=> rw [List.map_cons,List.prod_cons,map_mul]; exact (congrArg (F (g i)) h).trans (p i)
lemma fly_one (F:A →⋆ₐ[ℂ] H.Op) : F 1 V=V:=by rw [map_one]; rfl
end
namespace Spine
variable (P : Spine) (R : P.Register) (j : Axis)
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "V"=> P.law
local notation "K"=> P.calibration
local notation "Ω"=> P.par
local notation "L"=>P.width
local notation "Qt"=> P.projection.clipped
local notation "π"=> P.history
local notation "C₀"=> P.room j
local notation "M"=> timeMesh P.par
local notation "S"=> P.neutralSlabs j
local notation "Sn"=>P.Physical j
local notation "B"=> P.Slabs j
local notation "δ" s:max f:max=> P.voxTest j s f
local notation "V₀" t:max=> P.Vox j t
local notation "x_b"=> P.Spectrum0 j
local notation "E"=> P.Test
local notation "S₀"=> enclave K
variable (x : P.Spectrum0 j)
local notation "θ"=> P.portion j x
local notation "φ"=> P.restrictPortion j x
local notation "Φ"=> P.colorSpace j x
local notation "Λ"=> P.PortionHil j x
local notation "U"=> P.gnsIn j x
local notation "A"=> P.ColorHil j x
local notation "ω"=> P.colorZero j x
local notation "ψ"=> P.emptyV j x
abbrev door (s w : ℕ) (p:0<w)(f:P.Card j s w)(e:P.voxTest j s f.val∈ enclave K): P.Physical j :=
  ⟨P.atSide j s w p f,P.makesIt j (Set.mem_insert_of_mem _ (P.adverts j p f e))⟩
lemma totalCost (f:E)(e:f∈ enclave K) (s:ℕ): ∃ (i:ℤ)(w:ℕ)(p:0<w)(b:P.Card j s w)(u:P.voxTest j s b.val∈ enclave K), δ s b.val=P.shifts j i f ∧ P.shadow j (P.door j s w p b u).val=P.reading j s f := by
  let a:= Classical.choice (anyporch Y H s j false (P.obs f))
  have p:δ s a.fwd.val=P.shifts j a.rise f:=Subtype.ext a.yes
  exact ⟨a.rise,a.span,a.pos,a.fwd, p ▸ (P.shifts_keep j a.rise e), p,(P.boxes_here j s a.span a.pos a.fwd).trans (by change P.reading j s (δ s a.fwd.val)=_; rw [p]; exact P.shifted_read ..)⟩
abbrev naturalVox (s:ℕ):={x:P.Vox j s//P.voxTest j s x∈ enclave K}
lemma plant_id (s w:ℕ)(p:0<w)(f:P.Card j s w)(e:P.voxTest j s f.val∈ enclave K) : U (Φ (P.door j s w p f e) ω)= P.stateVox j x s f.val := (P.identifies j x (P.door j s w p f e)).trans (P.from_entry j x s w p f).symm
lemma occupied_phys {s:ℕ}(f:P.naturalVox j s): ∃ y: (P.ColorHil j x), U y=P.stateVox j x s f.val:= by
  obtain ⟨b,t,k,p⟩:= P.fits j s f.val
  have h:δ s k.val∈ enclave K:=by rw [p]; exact f.property
  exact ⟨Φ (P.door j s b t k h) ω,(P.plant_id j x s b t k h).trans (congrArg (P.stateVox j x s) p)⟩
noncomputable def province (s:ℕ)(f:P.naturalVox j s): P.ColorHil j x:= (P.occupied_phys j x f).choose
lemma coincides {s:ℕ}(f:P.naturalVox j s): U (P.province j x s f)= P.stateVox j x s f.val:= (P.occupied_phys j x f).choose_spec
lemma awake (s w:ℕ) (p:0<w)(f:P.Card j s w)(e:P.voxTest j s f.val∈ enclave K) : P.colorSpace j x (P.door j s w p f e) (P.colorZero j x)= P.province j x s ⟨f.val,e⟩:=by
  exact (U).injective ((P.plant_id j x s w p f e).trans (P.coincides j x (⟨f.val,e⟩:P.naturalVox j s)).symm)
lemma firstVox (s:ℕ) : P.voxTest j s (unity Y H j 0 false s)∈ enclave K := Subalgebra.one_mem _ -- ..
lemma identified0 : P.province j x 0 ⟨unity Y H j 0 false 0,P.firstVox j 0⟩ = P.colorZero j x:=by
  let i:=unity Y H j 0 false 0; exact (U).injective ((P.coincides j x (⟨i,P.firstVox j 0⟩ : P.naturalVox j 0)).trans ((P.voxel_stays j x).trans (P.present0 j x).symm))
-- densenness via word decomposition for Slabs' projected mesh rig.
noncomputable def colorSpan : Submodule ℂ (P.ColorHil j x):= Submodule.span ℂ (⋃ s:ℕ, Set.range (P.province j x s))
local notation "L₀"=> P.colorSpan j x
lemma goColor {s:ℕ} (y:P.naturalVox j s) : P.province j x s y ∈ P.colorSpan j x:= Submodule.subset_span (Set.mem_iUnion.mpr ⟨_,Set.mem_range_self _⟩)
lemma goColor0 : P.colorZero j x∈ P.colorSpan j x:= by rw [← P.identified0]; exact P.goColor j x _
lemma stasis (g:Grid j) : P.colorSpace j x (P.walksColor j g) (P.colorZero j x)=P.colorZero j x:= by
  apply (U).injective; exact (P.moveTransit j x g _).trans ((P.present0 j x).symm ▸ (P.move_vac j x g)) -- notation
local notation "Z" g:max=> P.walksColor j g
local notation "s₀" l:max=> (List.map (P.walksColor j) l).prod
lemma prodN_val (b g : P.Physical j): (b*g).val=b.val*g.val:= rfl
lemma moves_list (l : List (Grid j)) : (s₀ l).val=(l.map (P.movesOf j)).prod:= by induction l with| nil=>rfl| cons i l h=> simp only [List.map_cons,List.prod_cons,P.prodN_val]; rw [h]
private lemma castable (b:Sn)(t : b=1) : Φ b ω ∈ P.colorSpan j x :=by
  subst b; apply Set.mem_of_eq_of_mem _ (show ω∈ ((P.colorSpan j x) : Set A) from P.goColor0 j x); exact fly_one («H»:=A) ω Φ
private lemma also_mem (b:Sn){i w:ℕ}(p:0<w)(f:P.Card j i w)(e:P.voxTest j i f.val∈ S₀)(t: b=P.door j i w p f e): Φ b ω∈ P.colorSpan j x:= by
  subst b; exact Set.mem_of_eq_of_mem (s:=(L₀:Set A)) (P.awake j x i w p f e) (P.goColor j x ⟨f.val,e⟩)
lemma passport (b:Sn) (t:b.val∈insert 1 (P.admitted j)):Φ b ω∈ P.colorSpan j x := by
  rcases mem_insert_iff.mp t with h|p; · exact castable P j x b (Subtype.ext h)
  obtain ⟨s,w,p,f,h,v⟩:=p; exact also_mem P j x b p f v (Subtype.ext h)
lemma lift_priced {y:P.Slabs j} (t:y∈ P.flyingForm j): ∃ b:P.Physical j,b.val=y∧ Φ b ω ∈ P.colorSpan j x:=by
  obtain ⟨f,v,l,h⟩:=t; let z:Sn:=⟨f,P.makesIt j v⟩; let b:=z*s₀ l; have p:b.val=y:=by unfold b; rw [P.prodN_val,P.moves_list]; exact h
  have he:Φ b ω= Φ z ω:= fly_through («H»:=A) (ω) (P.walksColor j) Φ (P.stasis j x) _ _
  exact ⟨b,p,Set.mem_of_eq_of_mem (s:=(L₀:Set A)) he (P.passport j x z v)⟩
lemma native_dense : Dense ((P.colorSpan j x): Set (P.ColorHil j x)):= fill_all («H»:=A) (ω) (P.colorSpan j x) (P.authorized j) Φ (gns_dense φ) (gns_operator_cont φ) (fun _ p=> P.lift_priced j x (P.flies j p))


variable (Q:Set RSpace)
local notation "W" Vv:max s:max=> well Ω K L true Vv s
local notation "T" => P.Effect
local notation "D"=> P.talks R
local notation "D₁"=> vistaDressing Y H D
local notation "d" n:max=>vistaFinish Y H n D
local notation "σ"=> P.spirits R j x
-- Purchase exactly at the axis-0 plane (contains *all s* on the process).
noncomputable def corePlane : Sunlight P.par where
  start:=0
  marks _:=0
  aligned _ _:= by unfold Scaled; ring
  shifted _ _:= ⟨0,by unfold gaugeShift; ring⟩
open Sunlight
local notation "z"=> P.corePlane
local notation "ζ"=> flank j ((z).hinge Ω)
local notation "c" a:max=> (z).cloister Ω L j K a
lemma core_hinge : P.corePlane.hinge Ω=0:=by unfold Sunlight.hinge markZ; simp [corePlane]
lemma complete_glare : P.corePlane.arena Ω = Set.univ := by ext; simp [arena,corePlane]
abbrev quarters := well Ω K L true (flank j (P.corePlane.hinge Ω)) (P.corePlane.arena Ω)
abbrev reachable (s:ℕ):= well Ω K L true (flank j (P.corePlane.hinge Ω)) ((P.corePlane.arena Ω) ∩ Set.Iic s)
local notation "C"=> P.quarters j
local notation "C₁" s:max=> P.reachable j s
lemma inPositive {f:P.Effect}{s:ℕ}(e:f∈P.reachable j s):f ∈ Sunlight.cloister Ω L j z K s:= (well_spec ..).1 e|>.1
lemma reaches {f:T} {n s:ℕ}(p:f∈ C₁ s)(h:s≤n): f∈ C₁ n:= wellGrows Ω K L true ζ ζ ((z).arena Ω ∩ Set.Iic s) ((z).arena Ω∩ Set.Iic n) (fun i x=> ⟨x.1, Nat.le_trans (show i ≤ s from x.2) h⟩) Subset.rfl p
lemma colorHorizon (y:C): ∃ s : ℕ, y.val ∈ C₁ s:= declaredGate Ω K L true ζ _ y.property -- syntax fix
lemma enact (n:ℕ)(f:T)(p:f∈ C₁ n) : ∃ b:P.naturalVox j n, δ n b.val=(d n) f:=by
  have hp:=(glass Y H D j z)
  have hv:= P.inPositive j p
  obtain ⟨Vv,q,e⟩:= crownShelter Ω L n (D₁) (auxiliaryPad K) hp.lantern ζ hp.onward hv
  have h:Tapestry.Ledge Ω L Vv j ((z).marks n):=((z).rents Ω L j n (Nat.zero_le n)).1 e -- name likely not Tapestry.
  let a:= P.positiveVox j n Vv ((d n) f) q (show Tower.region j 0 (K).ℓ Vv from h)
  have ht:= finishCoherent Y H n D f p (gateIssued Ω K L true ζ _ n p)
  exact ⟨⟨a,ht⟩,rfl⟩
noncomputable def cupUse (n:ℕ)(f:T)(p:f∈ C₁ n) : P.ColorHil j x:= P.province j x n (P.enact R j n f p).choose
lemma usesFormula {n:ℕ}(f:T)(p:f∈ C₁ n)(b:P.naturalVox j n)(e:δ n b.val=(d n) f): P.cupUse R j x n f p=P.province j x n b := by
  suffices h : (P.enact R j n f p).choose=b by exact congrArg (P.province j x n) h
  exact Subtype.ext (Subtype.ext (congrArg (fun f : P.Test=> f.val) ((P.enact R j n f p).choose_spec.trans e.symm)))
lemma useAdvance (n:ℕ)(y:T)(p:y∈C₁ n)(v:y∈ C₁ (n+1)): P.cupUse R j x n y p=P.cupUse R j x (n+1) y v:= by
  let t:=n+1; obtain ⟨b,e⟩:=P.enact R j n y p; obtain ⟨a,h⟩:=P.enact R j (n+1) y v
  have hg: a.val=Raise Y H (π).circuit j 0 false n t (by unfold t; omega) b.val:=by
    apply Subtype.ext
    have ht: vistaFinish Y H (n+1) D y=P.promote n R ((d n) y):= Decking.joins D₁ n y _ (gateIssued Ω K L true ζ _ n p)
    have hf := congrArg Subtype.val (h.trans (ht.trans (congrArg (P.promote n R) e.symm)))
    change a.val.val=stream Y H P.projection.refine n ((n+1)-n) b.val.val; rw [Nat.add_sub_cancel_left]
    exact hf.trans (P.promotes_to n R _)
  rw [P.usesFormula R j x y p b e,P.usesFormula R j x y v a h]; apply (U).injective; rw [P.coincides,P.coincides,hg,P.refine_vox]
lemma useFurther {s t:ℕ}(e:s≤t)(y:T)(p:y∈C₁ s): P.cupUse R j x s y p = P.cupUse R j x t y (P.reaches j p e):=by
 induction t,e using Nat.le_induction with|base=>rfl|succ t h ih=> exact ih.trans (P.useAdvance R j x t y _ _)
noncomputable def operatorWord (f:P.quarters j) : P.ColorHil j x:= P.cupUse R j x (P.colorHorizon j f).choose f.val (P.colorHorizon j f).choose_spec
lemma realizes (f:P.quarters j)(n:ℕ)(p:f.val∈P.reachable j n) : P.operatorWord R j x f=P.cupUse R j x n f.val p:=
  (P.useFurther R j x (le_max_left _ n) f.val _).trans (P.useFurther R j x (le_max_right _ n) f.val p).symm
lemma realizedGram (f g:C): inner ℂ (P.operatorWord R j x f) (P.operatorWord R j x g)= P.spirits R j x ((P.corePlane.oppose Ω j K f.val)*g.val):=by
  obtain ⟨s,p⟩:= P.colorHorizon j f; obtain ⟨t,q⟩:= P.colorHorizon j g
  let n:=max s t; have hp:=P.reaches j p (le_max_left s t); have ht:=P.reaches j q (le_max_right s t); obtain ⟨a,h⟩ := P.enact R j n _ hp; obtain ⟨b,u⟩:= P.enact R j n _ ht
  rw [P.realizes R j x f n hp,P.realizes R j x g n ht,P.usesFormula R j x _ hp a h,P.usesFormula R j x _ ht b u]
  have hx:T= T:= rfl
  rw [← (U).inner_map_map,P.coincides,P.coincides,P.gram_at,P.reflected_hat_at R j x j (z) n (Nat.zero_le n) (P.inPositive j hp) (P.inPositive j ht),P.single_agrees]
  rw [h,u]; rfl
-- every single positive label in physical algebra yields color vector.
abbrev accord (s:ℕ)(b:P.naturalVox j s):= pinhole P.Test s (P.voxTest j s b.val)
lemma pointed {s:ℕ}(b:P.naturalVox j s) : P.accord j s b ∈ P.reachable j s:=by
  apply oneSlotWell Ω K L true ζ ((z).arena Ω ∩ Set.Iic s) s (show s∈_ from ⟨show s∈ (z).arena Ω from Nat.zero_le s,Nat.le_refl s⟩) ?_ b.property
  obtain ⟨t,h⟩:= (purpose_ok ..).1 b.val.property; obtain ⟨Vv,t,h⟩:=(t:∃ S': Finset Cover, InTest K true S' false b.val.val ∧ Tower.region j (meshface («Λ»:=P.par) 0 s) (K).ℓ S')
  rw [area0] at h; exact ⟨Vv,t,((z).rents Ω L j s (Nat.zero_le _)).2 h⟩
lemma already {s:ℕ}{y:T}(e:y∈P.reachable j s): y∈P.quarters j := wellGrows Ω K L true _ _ _ _ Set.inter_subset_left (by rfl) e
lemma quarterFull : Dense ((Submodule.span ℂ (Set.range (P.operatorWord R j x))): Set (P.ColorHil j x)):=by
  apply (P.native_dense j x).mono; apply Submodule.span_le.mpr; rintro a t; obtain ⟨n,p⟩:=mem_iUnion.mp t; obtain ⟨y,rfl⟩:=p
  let Y':=P.accord j n y; let f: P.quarters j:=⟨Y',P.already j (P.pointed j y)⟩; apply Submodule.subset_span; exact ⟨f,(P.realizes R j x f n (P.pointed j y)).trans (P.usesFormula R j x Y' (P.pointed j y) y ((D₁).outcrop (auxiliaryPad K) n _).symm )⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.usesFormula
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pointed
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.stasis
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.lift_priced
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.realizedGram
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.quarterFull
