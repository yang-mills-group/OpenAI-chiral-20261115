import YM.SatinExist.ShiftE
import YM.SatinExist.Taint
import YM.SatinExist.Cameo
import SatinThinBeam
import SatinThinMill
-- Raze sell at finite registration. Toward unpadding on MANY *Operators*.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open TopologicalSpace Germ Alliance
namespace Spine
open Aria Set TopologicalSpace Metric Casting
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j) (D:P.Apron)(n w:ℕ)
local notation "K"=> P.calibration
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> P.VMark
local notation "κ"=> P.laysM
local notation "ψ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "ω"=> P.colorZero j x
local notation "Φ"=> P.colorSpace j x
local notation "T" t:max=> whenly (timeMesh P.par) n t
local notation "X"=>P.ColorHil j x
local notation "Χ"=>P.ManyF j x
local notation "υ" v:max=>P.voxTest j n v
local notation "Π"=> P.pillar j x
local notation "u" w:max=> SlabMark.identity P.run P.large n j false w
variable {Q:Type*}[DecidableEq Q](p:0 < w)
include p
-- coated value here. linear via cert
abbrev PrismS (F:P.Test)(A:(X).Op) : Prop:= ∃ (G:P.Card j n w)(h:υ G.val∈enclave K), υ G.val=F ∧ A= Φ (P.door j n w p G h)
local notation "ν₀"=> P.PrismS j x n w p
lemma prismS_astr {i r:P.Test}{X' Y:(X).Op}(a:ℂ)(v:P.PrismS j x n w p i X')(q:P.PrismS j x n w p r Y): P.PrismS j x n w p (a • i+r) (a • X'+Y):=by
 obtain ⟨F,hf,rfl,rfl⟩:=v; obtain ⟨G,hG,rfl,rfl⟩:=q; let U:= a • F.val+ G.val
 let V:= P.door j n w p F hf; let S:=P.door j n w p G hG
 have he:(υ U)= a • (υ F.val)+(υ G.val):=Subtype.ext rfl
 have hu: υ U∈ enclave K:= by rw [he]; exact Subalgebra.add_mem _ ((enclave K).smul_mem hf _) hG
 obtain ⟨D,t,uA⟩:=F.property; obtain ⟨E',v',uB⟩:=G.property
 let V':P.Card j n w:=⟨U,D∪E',((InTest.smul a t).mono subset_union_left).add (v'.mono subset_union_right),fun i h=> (mem_union.mp h).elim (uA i) (uB i)⟩; let B:= P.door j n w p V' hu
 have hB:B=a • V+S:=Subtype.ext (Subtype.ext (box_linear P j n w p F G V' a rfl))
 exact ⟨V',hu,he, ((congrArg (⇑Φ) hB).trans ((P.class_subplus j x _ _).trans (congrArg (· + Φ S) (P.class_subscale j x _ _)))).symm⟩
lemma prism_null : P.PrismS j x n w p 0 0 := by
 let F:= u w; let h: υ F.val∈ enclave K:= (enclave K).one_mem
 let V:=P.door j n w p F h
 have hv: ν₀ (υ F.val) (Φ V):=⟨F,h,rfl,rfl⟩
 simpa only [neg_one_smul,neg_add_cancel] using P.prismS_astr j x n w p (-1) hv hv
lemma prism_screen (S:Finset Q)(z:Q→ℂ)(F:Q→P.Test)(Y:Q→ (P.ColorHil j x).Op)(h:∀ i∈ S,ν₀ (F i) (Y i)): ν₀ (∑ i∈ S,z i • F i) (∑ i∈ S,z i • Y i):=by
 classical
 induction S using Finset.induction_on with
 | empty=> simp; exact P.prism_null j x n w p
 | insert i L t ih=>
    rw [sum_insert t,sum_insert t]; exact P.prismS_astr j x n w p _ (h i (mem_insert_self ..)) (ih (fun j r=> h j (mem_insert_of_mem r))) -- syntax
lemma values_too {P':P.Test} {A B:(X).Op}(pA:P.PrismS j x n w p P' A)(pB:P.PrismS j x n w p P' B): A=B:=by
 obtain ⟨F,hA,t,rfl⟩:=pA; obtain ⟨G,hB,q,rfl⟩:=pB
 have he:F=G:=Subtype.ext (Subtype.ext (congrArg (fun x:P.Test=>x.val) (t.trans q.symm))); subst F; rfl
omit p
local notation "O₀" t:max F:max=> P.pillar j x F (-t) t 0
variable (I:Finset Q)(z:Q→ℂ)(A:Q→P.Apron)
-- price at half-box $m$, not increasing furthermore; buy only where seam strictly qualified for all.
lemma petitions (p:0<w)(g:∀ i∈ I,(A i).s≤ n)(d:D.s≤n)(he:D.realWidth P j < (T w:ℝ))(hs:∀ i∈ I,(A i).realWidth P j<(T w:ℝ))(Y:D.full P n=∑ i∈ I,z i • (A i).full P n) : P.pillar j x D (-(T w:ℝ)) (T w:ℝ) 0= ∑ i∈ I,z i • P.pillar j x (A i) (-(T w:ℝ)) (T w:ℝ) 0:=by
 let r:Cover:= fun _=> (w:ℤ)
 let C:= P.vtile n r
 let y:= κ C
 let t:ℝ:= T w; let V(D:P.Apron):= P.raze j x D 0 (T (w+w):ℝ) C
 let F(D:P.Apron):=P.chartAll r (D.full P n)
 have hx: y j=t:= natural_time (timeMesh P.par) ..
 have hp:0< w+w:=add_pos p p
 have q(D:P.Apron)(d:D.s≤n)(h:D.realWidth P j<t): P.PrismS j x n (w+w) hp (F D) (V D):= by
    refine P.shelf_door j x D n (w+w) r d hp ?_ ?_
    · change 0< y j - D.realWidth P j; rw [hx]; exact sub_pos.mpr h
    change y j + D.realWidth P j<((T (w+w)):ℝ); rw [hx,when_add,NNReal.coe_add]; exact add_lt_add_right h t
 obtain qA:=P.prism_screen j x n _ hp I z (F∘A) (V∘A) (fun i t=> q _ (g i t) (hs i t))
 have hx':P.PrismS j x n _ hp (∑ i∈ I,z i • F (A i)) (V D):=by
    have hu:= q D d he; have hz:F D= ∑ i∈ I,z i • F (A i):=by unfold F; rw [Y,map_sum]; exact sum_congr rfl fun i _=> map_smul ..
    rw [← hz]; exact hu
 have Jv:= P.values_too j x n (w+w) hp hx' qA
 let c:=P.kiosk j x
 let X':= P.cartage j x
 let D'(D:P.Apron):= O₀ t D
 let S(D:P.Apron):=P.pillar j x D 0 (T (w+w):ℝ) y
 have ht(D:P.Apron): c (V D)=S D:= P.kiosk_pillar ..
 obtain ⟨U,f⟩:=P.kioskL j x; have hg:S D=∑ i∈ I,z i• S (A i):=by
    have hV(d:P.Apron):S d=U (V d):= (ht d).symm.trans (f _).symm
    simp_rw [hV]; rw [Jv,map_sum]; exact sum_congr rfl fun i _=> map_smul ..
 have hs(A:P.Apron):D' A= X' (-y)*S A*X' y:=by
    let T':= (T (w+w):ℝ); have he:=P.travels_door j x A 0 T' y (-y); rw [Pi.neg_apply,neg_add_cancel,neg_neg,hx,add_zero] at he; rw [show -t+T'=t from ?_] at he; exact he
    unfold t T'; rw [when_add,NNReal.coe_add]; ring
 change D' D=_; rw [hs D,hg,Finset.mul_sum,Finset.sum_mul]; exact sum_congr rfl fun i _=> by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,← hs (A i)] -- orientation
lemma petitions_r (p:0<w)(g:∀ i∈ I,(A i).s≤ n)(d:D.s≤n)(he:D.realWidth P j < (T w:ℝ))(hs:∀ i∈ I,(A i).realWidth P j<(T w:ℝ))(Y:D.full P n=∑ i∈ I,z i • (A i).full P n)(t:ℝ)(v:(T w:ℝ) ≤ t) : O₀ t D= ∑ i∈ I,z i • O₀ t (A i):=by
 let r:ℝ:= T w; let V:= (ν).E (t-r).toNNReal
 have hp(A:P.Apron)(u':A.realWidth P j<r): O₀ t A= V*(O₀ r A)*V:=by
    have ht:= P.bigger_door j x A (-t) t (-r) r 0 (neg_le_neg v) v (by unfold Apron.time_panel; rw [Pi.zero_apply]; linarith) (by unfold Apron.time_edge; rw [Pi.zero_apply]; linarith);
    rw [show -r- -t=t-r by ring] at ht; exact ht
 have hx: O₀ r D=_:= petitions P j x D n w I z A p g d he hs Y; rw [hp D he, hx, Finset.mul_sum, Finset.sum_mul]; exact sum_congr rfl fun i v=> by rw [hp (A i) (hs i v),Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
