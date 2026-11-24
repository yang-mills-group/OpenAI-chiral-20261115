import YM.SU5.Aria.Footpath
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set TopologicalSpace Metric

/-! # Case of consecutive doors. P.Test, so the footprint is still compared (not
free-GNS frame arithmetic). Convenience API. h strictly-positive width (implement with
1 separately allowed for zero *gap*, not zero leaf price). -/
variable (P: Spine) (j:Axis)
local notation "H"=>P.large
local notation "Y"=>P.run
local notation "V"=>P.law
local notation "K"=>P.calibration
local notation "L"=>P.par.R.L.val
local notation "A"=>P.Test
local notation "T"=>timeMesh P.par
local notation "D" s:max f:max=>P.voxTest j s f
local notation "ρ" p:max=>P.shifts j p
local notation "B" s:max w:max hw:max=>P.Box j s w hw
local notation "M" s:max n:max=>whenly (timeMesh P.par) s n

structure InCase (s w:ℕ)(F:P.Test) : Prop where
 colorC:F∈ enclave P.calibration
 knows:∃ g:P.Card j s w,P.voxTest j s g.val=F

namespace InCase
variable {P}{j}{s t w v:ℕ}{X Z:P.Test}(A0:P.InCase j s w X)
noncomputable def card : P.Card j s w:= A0.knows.choose
lemma entry : P.voxTest j s A0.card.val=X:= A0.knows.choose_spec
lemma allC {f:P.Card j s w} (h:P.voxTest j s f.val=X): A0.card=f:=Subtype.ext (Subtype.ext (congrArg (fun x:P.Test=>x.val) (A0.entry.trans h.symm)))
variable (x:P.Spectrum0 j)
local notation "Φ"=> P.colorSpace j x
local notation "V₀" => P.Physical j
local notation "Χ" => P.ColorHil j x
noncomputable def rations (hw:0<w): P.Physical j:= P.door j s w hw A0.card (by rw [A0.entry]; exact A0.colorC)
noncomputable def charges(hw:0<w) : (P.ColorHil j x).Op:= P.colorSpace j x (A0.rations hw)
theorem cap (hw:0<w): ‖A0.charges x hw‖ ≤ ‖P.Box j s w hw A0.card‖:= NonUnitalStarAlgHom.norm_apply_le (P.colorSpace j x) (A0.rations hw)
lemma cases_eq_door (hw:0<w) (f:P.Card j s w)(h:P.voxTest j s f.val=X): A0.rations hw=P.door j s w hw f (by rw [h]; exact A0.colorC) :=Subtype.ext (congrArg (P.atSide j s w hw) (A0.allC h))

lemma sized (P:Spine)(j:Axis) (s w:ℕ){X:P.Test} (h:X∈enclave P.calibration){S:Finset Cover}(U: InTest P.calibration true S false X.val) (p:Between P.calibration j 0 (ruler P.par.block*w) S): P.InCase j s w X:=
 let V':= P.positiveVox j s S X ((Tapestry.locates ..).mpr U) (fun i x=> (p i x).1)
 ⟨h, (⟨V',S,U,p⟩:P.Card j s w),rfl⟩
-- Conversely get S.
include A0 in
lemma aSize : ∃ S:Finset Cover, InTest P.calibration true S false X.val ∧ Between P.calibration j 0 (ruler P.par.block*w) S :=by
 rw [← A0.entry]; exact A0.card.property
lemma ofVox (P:Spine)(j:Axis){s w:ℕ}{X:P.Test}(f:P.Card j s w)(h:P.voxTest j s f.val∈enclave P.calibration)(e:P.voxTest j s f.val=X): P.InCase j s w X:=⟨e ▸ h,_,e⟩
lemma units(P:Spine)(j:Axis)(s w:ℕ): P.InCase j s w 1:=⟨Subalgebra.one_mem _, SlabMark.identity P.run P.large s j false w,rfl⟩
theorem rations_units(P:Spine)(j:Axis)(s w:ℕ)(hw:0<w) : (units P j s w).rations hw=P.risesColor j (whenly (timeMesh P.par) s w):=by
 rw [(units P j s w).cases_eq_door hw (SlabMark.identity P.run P.large s j false w) rfl]; exact Subtype.ext (Subtype.ext (SlabMark.ticket_birth P.run P.large P.law s P.history P.projection.clipped j false (P.room j) w hw))
lemma zeros(P:Spine)(j:Axis)(s w:ℕ): P.InCase j s w 0:=sized P j s w (Subalgebra.zero_mem _) (S:=∅) (show InTest _ _ _ _ (0:Family _) from InTest.zero) (fun _ f=>by simp at f)
theorem rations_zero (hw:0<w) : (zeros P j s w).rations hw=0:=Subtype.ext (Subtype.ext (P.box_zero j s w hw _ (congrArg Subtype.val ((zeros P j s w).entry))))
include A0
lemma scale (z:ℂ): P.InCase j s w (z • X):=by
 obtain ⟨S,h,q⟩:= A0.aSize; exact sized P j s w (Subalgebra.smul_mem _ (A0.colorC) _) (show InTest _ _ _ _ (z • X.val) from InTest.smul _ h) q
lemma append (p:P.InCase j s w Z): P.InCase j s w (X+Z):=by
 obtain ⟨S,h,q⟩:= A0.aSize; obtain ⟨T',v,g⟩:=p.aSize
 exact sized P j s w (Subalgebra.add_mem _ A0.colorC p.colorC) (S:=S∪T') (show InTest _ _ _ _ (X.val+Z.val) from (h.mono subset_union_left).add (v.mono subset_union_right)) (fun i x=>(mem_union.mp x).elim (q i) (g i))
lemma except (p:P.InCase j s w Z): P.InCase j s w (X-Z):=by rw [sub_eq_add_neg,← neg_one_smul ℂ Z]; exact A0.append (p.scale _)
lemma rations_linear (p:P.InCase j s w Z){X':P.Test}(q:P.InCase j s w X')(z:ℂ)(hw:0<w)(e:X'=z • X+Z): q.rations hw=z • A0.rations hw+p.rations hw:= by
 apply Subtype.ext; apply Subtype.ext; apply P.box_linear j s w hw A0.card p.card q.card; change (D s q.card.val).val=z • (D s A0.card.val).val+(D s p.card.val).val; rw [q.entry,A0.entry,p.entry]; exact congrArg Subtype.val e
lemma rations_add (p:P.InCase j s w Z) (hw:0<w) : (A0.append p).rations hw=A0.rations hw+p.rations hw:=by have h:=(rations_linear A0 p (A0.append p) 1 hw (by rw [one_smul])); have h1: (1:ℂ) • A0.rations hw=A0.rations hw:= @MulAction.one_smul ℂ (P.Physical j) _ (show Module ℂ (P.Physical j) from inferInstance).toDistribMulAction.toMulAction _; rw [h1] at h; exact h
lemma rations_scale (z:ℂ)(hw:0<w): (A0.scale z).rations hw=z • A0.rations hw:=by
 simpa only [add_zero,rations_zero] using (rations_linear A0 (zeros P j s w) (A0.scale z) z hw (by rw [add_zero]))
lemma rations_except (p:P.InCase j s w Z)(hw:0<w): (A0.except p).rations hw=A0.rations hw-p.rations hw:=by
 -- via rations_linear p instead (target x':= X-Z)
 have hx:= rations_linear p A0 (A0.except p) (-1) hw (by rw [neg_one_smul]; abel)
 rw [neg_one_smul] at hx; rw [hx]; abel
lemma charges_add (p:P.InCase j s w Z)(hw:0<w): (A0.append p).charges x hw=A0.charges x hw+p.charges x hw:= by unfold charges; rw [rations_add A0 p hw]; exact (P.colorSpace j x).map_add' _ _
lemma charges_scale (z:ℂ)(hw:0<w): (A0.scale z).charges x hw=z • A0.charges x hw:=by unfold charges; rw [rations_scale A0 z hw]; exact (P.colorSpace j x).toLinearMap.map_smul' _ _
lemma charges_except (p:P.InCase j s w Z)(hw:0<w): (A0.except p).charges x hw=A0.charges x hw-p.charges x hw:=by unfold charges; rw [rations_except,map_sub]

-- consecutive only
lemma linked (p:P.InCase j s v Z): P.InCase j s (w+v) (X*P.shifts j (w:ℤ) Z):=by
 let f:= edit P.run P.large s j false w v A0.card p.card
 refine ⟨Subalgebra.mul_mem _ A0.colorC (P.shifts_keep j _ p.colorC),f,?_⟩
 exact (Subtype.ext (editor ..): P.voxTest j s f.val=D s A0.card.val * P.shifts j (w:ℤ) (D s p.card.val)).trans (by rw [A0.entry,p.entry])
lemma rations_linked (p:P.InCase j s v Z)(hw:0<w)(hv:0<v): (A0.linked p).rations (add_pos hw hv)=A0.rations hw*p.rations hv:=by
 let f:= edit P.run P.large s j false w v A0.card p.card
 have he:P.voxTest j s f.val=X*P.shifts j (w:ℤ) Z:=(Subtype.ext (editor ..): P.voxTest j s f.val=D s A0.card.val * P.shifts j (w:ℤ) (D s p.card.val)).trans (by rw [A0.entry,p.entry])
 rw [(A0.linked p).cases_eq_door _ f he]; exact Subtype.ext ((P.concat j s w v hw hv A0.card p.card).symm)
lemma charges_linked (p:P.InCase j s v Z)(hw:0<w)(hv:0<v): (A0.linked p).charges x (add_pos hw hv)=A0.charges x hw*p.charges x hv:=by unfold charges; rw [rations_linked _ _ hw hv,map_mul]
lemma climb (h:s≤t) : P.InCase j t (P.par.R.L.val^(t-s)*w) (P.conveying s (t-s) X):=⟨P.refine_keeps s X A0.colorC _,furnished Y H s P.history j false w A0.card t h,(P.convey_vox j A0.card h).symm.trans (congrArg (P.conveying _ _) A0.entry)⟩
theorem charges_climb (h:s≤t)(hw:0<w): (A0.climb h).charges x (mul_pos (pow_pos P.par.R.L.property _) hw)=A0.charges x hw:=by
 unfold charges; apply congrArg (P.colorSpace j x)
 rw [(A0.climb h).cases_eq_door _ (furnished Y H s P.history j false w A0.card t h) ((P.convey_vox j A0.card h).symm.trans (congrArg (P.conveying _ _) A0.entry))]; exact Subtype.ext ((P.upper_tab j s w hw A0.card t h).symm)
omit A0 in
theorem charges_units (hw:0<w) : (units P j s w).charges x hw=(P.physicalEnergy j x).E (M s w):=by unfold charges; rw [rations_units]; rfl

lemma charges_eq {v y : ℕ}{Z:P.Test}(p:P.InCase j y v Z)(e:s=y)(k:w=v)(a:X=Z)(hw:0<w): A0.charges x hw=p.charges x (k ▸ hw):=by subst v; subst y; subst X; rfl
-- Pad integers incl 0 edges. `charges` as engine on [0,w].
lemma padIn (l r:ℕ) : P.InCase j s (l+w+r) (P.shifts j l X):=by
 have h:= ((units P j s l).linked A0).linked (units P j s r); rwa [one_mul,map_one,mul_one] at h
lemma charges_back (l:ℕ) (hw:0<w) (p:P.InCase j s (l+w) (P.shifts j l X)) : p.charges x (by omega)=(P.physicalEnergy j x).E (M s l)*A0.charges x hw:=by
 let E:= P.physicalEnergy j x; rcases Nat.eq_zero_or_pos l with c|y
 · subst l; rw [when_zero, show (P.physicalEnergy j x).E 0=(1:(P.ColorHil j x).Op) from (P.physicalEnergy j x).eZero,one_mul]; exact charges_eq p x A0 rfl (by omega) (by rw [Nat.cast_zero,P.shifts_zero]) _
 have h:0<l+w:=add_pos y hw; have hh:= (charges_linked (units P j s l) x A0 y hw); have hg:=charges_units (s:=s) x y; rw [hg] at hh; exact (charges_eq p x _ rfl rfl (by rw [one_mul]) _).trans hh
lemma charges_fore (r:ℕ)(hw:0<w)(p:P.InCase j s (w+r) X): p.charges x (by omega)=A0.charges x hw*(P.physicalEnergy j x).E (M s r) :=by
 rcases Nat.eq_zero_or_pos r with e|y
 · subst r; rw [when_zero,show (P.physicalEnergy j x).E 0=(1:(P.ColorHil j x).Op) from (P.physicalEnergy j x).eZero,mul_one]
 have hh:= charges_linked A0 x (units P j s r) hw y; have hg:=charges_units (s:=s) x y; rw [hg] at hh; exact (charges_eq p x _ rfl rfl (by rw [map_one,mul_one]) _).trans hh
lemma charges_pad (l r:ℕ) (hw:0<w): (A0.padIn l r).charges x (by omega)=(P.physicalEnergy j x).E (M s l) * A0.charges x hw * (P.physicalEnergy j x).E (M s r):=by
 let p: P.InCase j s (l+w) (P.shifts j l X):= Nat.add_zero _ ▸ A0.padIn l 0 -- `let Prop`
 have hu:0 < l+w:=by omega
 rw [charges_fore p x r hu (A0.padIn l r), charges_back A0 x l hw p]
end InCase
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.InCase.charges_pad
#print axioms Spine.InCase.rations_except
#print axioms Spine.InCase.charges_scale
#print axioms Spine.InCase.cap
#print axioms Spine.InCase.charges_climb

#print axioms Spine.InCase.charges_except
#print axioms Spine.InCase.charges_add
