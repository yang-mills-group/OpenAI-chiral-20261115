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
local notation "u" w:max=> SlabMark.identity P.run P.large n j false w
local notation "φ₀" k:max p:max F:max q:max=>P.colorSpace j x (P.door j n k p F q)
lemma tubePulse (p:0<w): E (T w)= φ₀ w p (u w) (show υ (u w).val ∈ enclave K from one_mem (enclave K)):=by
 change Φ (P.risesColor j _) = Φ _
 apply congrArg (fun y:P.Physical j=> Φ y)
 exact Subtype.ext (Subtype.ext (ticket_birth P.run P.large P.law n P.history P.projection.clipped j false (P.room j) w p).symm)
lemma editPulse {r s:ℕ}(p:0<r)(q:0<s)(F:P.Card j n r)(G:P.Card j n s)(v:υ F.val∈enclave K)(e:υ G.val∈enclave K):∃ (U:P.Card j n (r+s))(w:υ U.val∈enclave K), υ U.val=(υ F.val)*P.shifts j (r:ℤ) (υ G.val)∧ φ₀ (r+s) (add_pos p q) U w= (φ₀ r p F v)*(φ₀ s q G e):=by
 let U:= edit P.run P.large n j false r s F G; have he: υ U.val=(υ F.val)*P.shifts j (r:ℤ) (υ G.val):=Subtype.ext (editor ..);
 let V:= P.door j n; have h: υ U.val∈ enclave K:=he ▸ (Subalgebra.mul_mem (enclave K) v (P.shifts_keep j _ e));
 refine ⟨U,h,he,?_⟩; let A:P.Physical j:= P.door j n r p F v; let B:P.Physical j:= P.door j n s q G e; change Φ _ = Φ A*Φ B; rw [←map_mul]; apply congrArg (fun p:P.Physical j=>Φ p); exact Subtype.ext (P.concat ..).symm
local notation "dw"=> D.zoom P n j
variable (r:Cover) (t:D.s≤n)(p:0<w)
local notation "c"=> P.vtile n r
local notation "b"=> Apron.time_panel P j (P.laysM (P.vtile n r)) D
local notation "b'"=> Apron.time_edge P j (P.laysM (P.vtile n r)) D
include t p
lemma shelf_door (v:0< b)(V:b' < (T w:ℝ)): ∃ (F:P.Card j n w)(h:υ F.val ∈ enclave K), υ F.val=P.chartAll r (D.full P n) ∧
   P.raze j x D 0 (T w:ℝ) c=φ₀ w p F h:=by
 obtain ⟨g,s,t',k⟩:= D.transported P j x n t r
 let i:= r j-(dw:ℤ); let l:= r j+(dw:ℤ)
 have hp: bell Μ n i=b:=P.begins j (fun _ :Unit=>D) (fun _=>r) n () t
 have hq: bell Μ n l=b':=P.endsAt j (fun _:Unit=>D) (fun _=>r) n () t
 have hb: bell Μ n (0:ℤ)=0:=by unfold bell; ring
 have he: 0 < i:=lt_of_not_ge (fun h=> v.not_ge ((hp.symm.trans_le ((bell_le Μ n _ _).2 h)).trans_eq hb))
 have bt(c₀:ℕ):↑(T c₀) =bell Μ n (c₀:ℤ):= (natural_time Μ n c₀).symm
 have hu:l < (w:ℤ):= lt_of_not_ge (fun h=> V.not_ge (by rw [←hq,bt]; exact (bell_le Μ n _ _).2 h ))
 let f:=i.toNat; let d:= (w-l:ℤ).toNat;
 have hx:0<f:=by unfold f; omega
 have hV:0<d:=by unfold d; omega
 have hl:(f:ℤ)=i:=Int.toNat_of_nonneg he.le; have hD:(d:ℤ)=w-l:=Int.toNat_of_nonneg (sub_nonneg.mpr hu.le)
 let m:=dw+dw; have hm:0 < m:=add_pos (D.zoomP ..) (D.zoomP ..)
 have hw:f+m+d=w:=by unfold i l at *; unfold m; omega
 let vK:= one_mem (enclave K); let M:=P.raze j x D 0 (T w:ℝ) c
 obtain ⟨A,xA,tA,eA⟩:= P.editPulse j x n hx hm (u f) g (show υ (u f).val ∈ enclave K from vK) s
 obtain ⟨B,hX,tB,eB⟩:= P.editPulse j x n (add_pos hx hm) hV A (u d) xA (show υ (u d).val ∈ enclave K from vK)
 have h0: υ B.val=P.chartAll r (D.full P n):=by
    change υ B.val=υ A.val*(P.shifts j _ 1) at tB; rw [tB,tA,t',map_one,mul_one,P.shifts_sum, show (f:ℤ)+_ = 0 from (by unfold i at *; omega)]; change 1 * _=_; rw [one_mul]; exact P.shifts_zero ..
 have hPaid : M=φ₀ (f+m+d) (add_pos (add_pos hx hm) hV) B hX:=by
    have h1: b=(T f:ℝ):=by rw [bt,hl,hp]
    have h2:(T w:ℝ) - b'=(T d:ℝ):=by rw [bt w,←hq, bt d,hD,P.bell_sub]
    let aL:=E (T f)
    let aR:=E (T d)
    let Y:=φ₀ m hm g s
    have U:E (b-0:ℝ).toNNReal=aL:=congrArg E (by rw [sub_zero,h1,Real.toNNReal_coe])
    have Q:E ((↑(T w):ℝ) - b').toNNReal=aR:= congrArg E (by rw [h2,Real.toNNReal_coe])
    have Z:M=aL*(Y*aR):=congrArg₂ (· * ·) U (congrArg₂ (· * ·) k Q)
    have x₀:aL=φ₀ f hx (u f) (show υ (u f).val ∈ enclave K from vK):=P.tubePulse j x n f hx; have x₁:aR=φ₀ d hV (u d) (show υ (u d).val ∈ enclave K from vK):=P.tubePulse j x n d hV
    exact Z.trans ((mul_assoc aL Y aR).symm.trans ((congrArg₂ (·*·) ((congrArg₂ (·*·) x₀ (rfl : Y=Y)).trans eA.symm) x₁).trans eB.symm))
 have goal {m:ℕ}(F:P.Card j n m)(h:υ F.val ∈ enclave K)(p':0 < m)(eq:m=w)(r':υ F.val=P.chartAll r (D.full P n))(t:M=φ₀ m p' F h): ∃ (F:P.Card j n w)(h:υ F.val∈enclave K), υ F.val=P.chartAll r (D.full P n) ∧ M=φ₀ w p F h:=by -- induction eq use eq? w,M dependent
    subst m; exact ⟨F,h,r',t⟩
 exact goal B hX _ hw h0 hPaid
-- compression map
noncomputable def kiosk (A:(X).Op) : (Χ).Op := (P.wealth j x).comp (A.comp (P.enter j x).toContinuousLinearMap)
omit t p
lemma kiosk_header (g:Γ)(A:(X).Op) : P.kiosk j x (P.charter j x g A)=P.tableau j x (P.laysM g) A:=by
 let P':=P.wealth j x; let U:=P.enter j x; let τ:=P.truck j x; let S:= P.cartage j x; ext1 y; unfold kiosk charter tableau; simp only [ContinuousLinearMap.comp_apply];
 change P' (P.truck j x g (A (P.truck j x (-g) (P.enter j x y))))=S _ (P' (A (U _)))
 rw [P.cart_and,P.lays_neg]
 have u'(t:X): P' (τ g t)=S (κ g) (P' t):=by
    unfold S; rw [P.uses_cart]; exact (P.roll_motion j x (g ∘ Subtype.val) t).symm
 exact u' _
lemma kiosk_heat (L R:ℝ≥0)(A:(X).Op): P.kiosk j x ((E L).comp (A.comp (E R)))= ((ν).E L).comp ((P.kiosk j x A).comp ((ν).E R)):=by
 ext y; change P.wealth j x (E L (A (E R (P.enter j x y))))= (ν).E L (P.wealth j x (A _))
 rw [← P.soleHeat]; exact P.bankHeat ..
lemma kiosk_pillar (s t:ℝ)(g:Γ): P.kiosk j x (P.raze j x D s t g)=P.pillar j x D s t (κ g):=by
 unfold pillar raze; rw [P.kiosk_heat,P.kiosk_header]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
