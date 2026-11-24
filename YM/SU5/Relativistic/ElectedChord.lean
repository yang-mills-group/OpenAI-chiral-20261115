import YM.SU5.Relativistic.Backing
import YM.SU5.Relativistic.Whirl
import YM.SU5.Relativistic.Preparing

/-! # Surviving positivity for the halfspace of ODD inputs, in THIS selected character
   Distant unselected-sector boundary of the color orientation isometry; reflection conjugation
   here needs a Koszul calculation--f*g*g*y isn't an outsourced positive measure. -/
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
variable {S:Finset Cover} {f:Family (tent Y H)} (h:InTest (tent Y H) true S true f) (s:ℕ)
local notation "μ"=> mirror K j (0:ℤ)
include t h
lemma residentPrice (r: Tower.region j 0 (tent Y H).ℓ S): 0 ≤ ψ s (Complex.I • (mirror K j 0 f*f)):=by
 -- boundary in d=j on display-resident orientation χ j. holds also for x by Across.
 let F:= Complex.I • (mirror K j 0 f*f)
 have U: InTest K true (reflectedBox j 0 S ∪ S) false F:= InTest.smul _ (((axial K j _ h).mono subset_union_left).mul (h.mono subset_union_right))
 let K':Dome K:= ⟨F,aux_test U⟩; let z:Ξ:= pinhole D₀ s K'
 obtain ⟨M,p'⟩ := display_receives Y H D.univ_ G.history G.clipped j false (c j)
 obtain ⟨y,e⟩:= p'.onto.surjective (χ j)
 obtain ⟨A,p⟩:= prepares Y H D G j c M p' y
 have he:p' = p':= rfl
 let x' : Marks K false :=⟨F,aux_test U,nofun⟩
 have hy: ψ s x'.val = onDrawing Y H V G D j c (SameCharacter.resident Y H V G j false (c j) (M.character y)) z := by
    rw [← selected_here Y H D G d j c x s x', e]
    have hp:= costs_pinhole Y H D G j c (χ j) s K'
    change (φ s) x'= _; refine Eq.trans ?_ hp.symm
    rw [evaluates Y H V G j c (SameCharacter.resident Y H V G j false (c j) (χ j)) s x',SameCharacter.sameReading] -- defeq maybe
 rw [show Complex.I • (mirror K j 0 f*f)=x'.val from rfl,hy]
 apply ge_of_tendsto (p.focus z (curve.mpr ⟨s,short_pinhole s K'⟩))
 filter_upwards [eventually_ge_atTop s] with k hk
 let a:=A k; let m:= a.t; let Qm:=vistaFinish Y H m D; let g:=Future.boundary Y H j a
 let w:=m-s; have ht:s ≤ m:= hk.trans a.arrival; have hm:s+w=m:=by omega
 let R':= Future.kernelPath Y H j a
 have hv:z∈ shorter D₀ m:= climbs D₀ ht (short_pinhole s K')
 have h0:Qm (z*g)=(Qm z)*R':= Decking.last (vistaDressing Y H D) (auxiliaryPad K) z m hv _
 change 0≤ vistaTake Y H D (z*g)
 rw [vistaCall Y H m (z*g) D ((shorter D₀ m).mul_mem hv (short_pinhole m R'))]; change 0 ≤ E m (Qm (z*g)).val; rw [h0]
 let U':= (P s w) f
 have Hv: InTest K true (volumeAround Λ l w S) true U':= t.allSupport Y H V Q u s w h
 let N:= volumeAround Λ l w S
 let z':= (Future.emit Y H j a).val
 have hg:= Future.emit_extent Y H j a
 let W:= Future.opening Y H j a; have gz: Tower.region j 0 (K).ℓ W :=by
    intro i s; have he:= Future.op_far Y H j a i s
    have p: 0 ≤ ruler Λ.block * (Future.wait Y H j a:ℤ):=mul_nonneg (le_trans zero_le_one (ruler_gene _)) (by positivity); exact le_trans (by linarith only [p]) he
 have hz:Tower.region j 0 (K).ℓ N:=by
    have he: Tower.region j (Heat.gaugeShift Λ.block 0) (K).ℓ S:=by simpa [gaugeShift] using r
    have h:= future_climb Y H j 0 he w
    intro i s; specialize h i s; unfold Heat.gaugeShift at h; push_cast at h; simp at h; exact le_trans (by omega) h
 have g':(Qm z).val=Complex.I • (mirror K j 0 U'*U'):=by
    trans stream Y H G.refine s w ((vistaFinish Y H s D z).val); swap
    · rw [show (vistaFinish Y H s D z).val= x'.val from congrArg Subtype.val (show vistaFinish Y H s D z=K' from (by unfold z vistaFinish; rw [Decking.outcrop]; rfl)),show x'.val=F from rfl,←t.originally Y H V Q u s w (aux_test U)]
      unfold F; let hx:=axial K j 0 h
      have hw:InTest K true (reflectedBox j 0 S ∪ S) false (mirror K j 0 f*f):=(hx.mono subset_union_left).mul (h.mono subset_union_right)
      have he:= t.allCrossing Y H V Q u s w hx h (mirror_detached Λ l r r)
      change stream Y H (fun s=> T s false) s w (mirror K j 0 f*f)=_ at he
      rw [t.ampAll Y H V Q u s w hw,he,t.allTurning Y H V Q u s w h,planeAt,mul_zero]
    exact Eq.trans (congrArg (fun t=> ((vistaFinish Y H t D z).val)) hm.symm) (finish_upwards Y H D G s (short_pinhole s K') w)
 have hb: Disjoint (reflectedBox j 0 S) S:=Tower.Selected.detached_disjoint (mirror_detached Λ l r r)
 let Jr:=U'*z'
 have uQ:InTest K true (N ∪ W) true Jr:=(Hv.mono subset_union_left).mul (hg.mono subset_union_right)
 have hZ:(Qm z*R').val= Complex.I • (mirror K j 0 Jr*Jr):=by
    change (Qm z).val * ((μ z') * z')=_ -- notation use μ
    rw [g',Algebra.smul_mul_assoc]
    unfold Jr; rw [mirror_times]
    have hv: U' * (mirror K j 0 z')= mirror K j 0 z'*U':=(by simpa only [Sector.grainB,Bool.and_false,Bool.false_eq_true,ite_false,one_smul] using signMark K Hv (axial K j 0 hg)) -- :tune exact
    simp only [mul_assoc]; rw [←mul_assoc U',hv,mul_assoc]
 have hw: Tower.region j 0 (K).ℓ (N∪W):= fun i h => (mem_union.mp h).elim (hz i) (gz i)
 have hp: Heat.gaugeShift Λ.block 0=0:=by unfold gaugeShift; ring
 rw [hZ,← hp]; exact chargedGram Y H m V uQ (hp.symm ▸ hw) -- careful rewrite complex 0, occurrence
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
