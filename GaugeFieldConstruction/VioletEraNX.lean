import GaugeFieldConstruction.Prax3
import GaugeFieldConstruction.Fars
import GaugeFieldConstruction.Raim3
import GaugeFieldConstruction.WonderEarnNX
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open TableF TableF.Lenten TableF.Lenten.Layout
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
open XGarden.Shield
open Leaf
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c c' e g a' h:ℝ}
variable (F:Elm n Unit d a c)(F': Elm n Unit d a' c')(R:Loom n)(k:ℕ)(t:ℝ)
local notation "Vx" => MealD F' R k t
variable (u:Roof n t d k R)(q:0<d)
variable (P:BudgetPoint)(μ:ℕ)(σ:I→Seat n)(Z:I→Paper n)(s:Finset I){v K h g:ℝ}(ι:hud_T 7 K)(b:0 ≤v)(f:coinH K v)
variable (U:∀ i∈s, DonauNX μ (Py.KeyUp P) (σ i) h (Z i) g) (ψ:∀ i∈s, portable (Z i))
local notation "Ακ"=> PapyrusFNX F R k t μ σ P Z -- P order before σ?
variable (Da: Ids n)
-- payouts.Currencies.
local notation "Δμ" i:max=> Escort v d h c' i
variable {δ:ℝ}{J J':ℕ}(p: pure_Rim F)(H:dry_E F') (z:Tyrant k J (3*δ) a)(w:Tyrant k J' δ a')
variable (ha:0<a)(hb:0<a')(hp:Hann P k t)(hv:1≤h)(hN:2*(P.B+1)<(More n).val)(kP:24≤P.B)(j0:ℕ)(hk:0<j0)
local notation "Pδ"=>low_η P.B d P.threshold
variable (dℓ:0≤low_η P.B d P.threshold)(dx:low_η P.B d P.threshold ≤1)
variable (L:ℕ)(x : (πBirth+16*ζd)*2*(Yaw.χ (ThermalH L):ℝ)≤ (P.B:ℝ)*(δ/2)) (y:ζd*2*(Yaw.χ 0:ℝ)≤j0*(δ/2))
local notation "pΩ"=> PressureNX μ v d a c (3*δ) h k J g
local notation "qΩ"=> PressureNX μ v d a c (3*δ) h k J g
local notation "Ex"=> Vx
local notation "rΞ"=> Ghost_P δ (Δμ J') 8 pΩ L
local notation "mΞ"=> Ghost_M δ (Δμ J') 8 pΩ L
local notation "aV"=>Quips qΩ 0 8 δ j0 L
local notation "QΩ"=> book_S d a' c' v F' h
local notation "Qi"=> fun i:I=> pay_ANX μ (σ i) F v h g
local notation "QV"=>fun (_:I) (_:L3 n)=>crestP*g
open Py Py.Rate.Pitching.Focus XGarden.MastTin.MintB Isle
open Riant
variable (X:XE I (InkD n) n)(Kf:KK I (Copy n) n)(W0:Finset I→Vow.Pax n)(Q0: Finset I→ Vow.Cusp n)
variable (D:List I)(N:ℕ)(ξ:D.toFinset⊆s)(dg: Force_M P.B σ N) (pD:D.Nodup)
variable (Z₁ Z₂ Z₃ Z0 B E E' T A:ℝ) (pu:PoolAge N k L t B (Ghost_P δ (Escort v d h c' J') 8 (PressureNX μ v d a c (3*δ) h k J g) L) (Ghost_M δ (Escort v d h c' J') 8 (PressureNX μ v d a c (3*δ) h k J g) L) (low_η P.B d P.threshold) (Quips (PressureNX μ v d a c (3*δ) h k J g) 0 8 δ j0 L) d Z0 δ E E' T A P) (pw:FrostHx P σ Kf W0 Q0 h (zero_lt_one.trans_le hv) (cipherK k) Z₁ Z₂ Z₃ (πBirth+7*ζd) 8)(he:Z₂+Z₃+ chi_f P.order*Z₁ ≤ Z0)(pB:P.power=2)
variable (hm:0≤Ghost_M δ (Escort v d h c' J') 8 (PressureNX μ v d a c (3*δ) h k J g) L)(hπ:0 ≤Quips (PressureNX μ v d a c (3*δ) h k J g) 0 8 δ j0 L)
variable (hS:ThermalH L*P.B≤ P.B+cape_B P.B)(hs:2*(ThermalH L*P.B)< (More n).val)
local notation "Vt"=> Book3 P σ Kf W0 Q0 Vx L Ακ Da D
include dg pD
include u q ι b f U ψ z w Da p H hp hv x y ha hb kP hk hN dℓ dx dg ξ pD pu pw he pB hm hπ hS hs
set_option maxHeartbeats 240000 in
lemma VitastroNX : let G:=Book3 P σ Kf W0 Q0 (MealD F' R k t) L (PapyrusFNX F R k t μ σ P Z) Da D; Horn4 σ (G.pureX) G.B P h (zero_lt_one.trans_le hv) 8 πBirth T k ∧ BookT (SecK P (zero_le_one.trans hv) n) (fun i j=> G.B (i,j)) P.B (realm_C σ) πBirth 8 E' ∧
 (∀ (i:I), i∈ D→ Folio_K P (σ i) (fun j=>G.pureX ({i},j)) 0 L πBirth h A)∧ (∀ (p:PI I n),G.pureX p ≠0→∃ i∈D,i∈p.1)∧ (∀ (p:KI I n),G.B p≠0→∃ i∈D,i∈p.1) :=by
    intro G; have he':=receiptN_X F F' R k t u q P μ σ Z s ι b f U ψ Da p H z w ha hb hp hv hN kP j0 hk dℓ dx L x y
    let C₁:=A
    obtain ⟨Λ,Lw,E0,V,Y₀,Hξ,hL,z'⟩:= Genesis P σ Kf W0 Q0 _ _ _ _ _ _ h (zero_lt_one.trans_le hv) pw (by norm_num)
    let C: I→L3 n→Factor3 n:=PapyrusFNX F R k t μ σ P Z; let O:= Qi; let Q:= QΩ; let M:= Vx
    let τ:=Eta4 N P.B; let α:= rΞ; let Φ:= Flow4 N P.B; let QQ:=Q; let Xκ:= Rio.advanceC α τ* Z0+Rio.stolon P.B B τ α*Φ
    have hx:=pu.cold
    have hy:Nor.reserveT (KeyUp P).power P.order P.B ζd* Xκ ≤ E ∧ Nor.reserveT P.power P.order P.B ζd* Xκ ≤ E':=by rw [show (KeyUp P).power=3 from rfl,pB,hp.canon]; exact hx
    have hΛ(y):postG pastMask (Lw+E0) (March P.B (πBirth+7*ζd)) y+pointX cloudK Λ (March P.B (πBirth+7*ζd)) y ≤ Z0:= (z' y).trans he
    let u3:0 ≤ B:=pu.birth.1
    have v3: Boot4 P.B B (Eta4 N P.B) α Z0 (Flow4 N P.B) := pu.birth.2
    have uX:=FoCap P σ D N dg pD
    have hu:= Harbor_p P σ Kf W0 Q0 M L k C 8 h πBirth α δ (Δμ J') N j0 Da (a0:=πBirth) (m:=mΞ) (b:=Quips qΩ 0 8 δ j0 L) (t:=low_η P.B d P.threshold) O Q s QV he' (by norm_num) hv (T:=Λ) (X:=Lw) (Y:=E0) (η:=τ) (Ω:=B) (C₀:=Z0) V Y₀ Hξ hL (by norm_num [πBirth]) D ξ uX dg.2 hS rfl u3 hπ hm v3 hΛ le_rfl E E' T hy pu.cash pu.hot
    have hW(p':PI I n)(v:G.pureX p'≠0):∃ i∈D,i∈p'.1∧ p'.2.val.1=σ i:=by
       by_cases k':G.Y p'=0
       · have hv:G.X p' ≠0:=fun h=> v (by change G.X p'+G.Y p'=0; simp [h,k'])
         obtain ⟨j,v,s,hζ,w⟩:=plumeL P σ Kf W0 Q0 M L C Da D p' hv; refine ⟨j,v,?_,?_⟩
         · rw[←w]; exact mem_singleton_self _
         rw[←w]; exact rfl
       obtain ⟨i,d,q,x,y,z⟩:= FullWidth P σ Kf W0 Q0 M L C Da p' hs D k'; refine ⟨i,d,x,y.symm⟩
    refine ⟨hu.1,hu.2.1,?_,fun p q=>by obtain ⟨i,x,y,t⟩:= hW p q; exact ⟨i,x,y⟩,muted3 P σ Kf W0 Q0 M L C Da (D:=D)⟩ -- tune
    intro i t'; have pV:i∈s:=ξ (List.mem_toFinset.mpr t'); have pQ:=U i pV
    let K: RegBudget n:= fun j=>G.pureX ({i},j)
    have kV(p:Scree.Hub n)(v:K p ≠0): p.val.1=σ i :=by
       obtain ⟨j,a,h,w⟩:= hW ({i},p) v; exact w.trans (congrArg σ (mem_singleton.mp h))
    refine ⟨assignT (P:=P) K (σ i) πBirth A (zero_le_one.trans hv) (Shelf_sal _ (hu.2.2 i) pu.cram) kV,?_⟩
    intro p₀ u₀
    have he: G.pureX ({i},p₀)=0:=by
       unfold Rio.pureX; rw[Pi.add_apply]
       by_cases h:G.X ({i},p₀)=0; swap
       · obtain ⟨j,x,y,w,t⟩:=plumeL P σ Kf W0 Q0 M L C Da D _ h; have hx:p₀=spark3 M (C j) P L y:= (congrArg Prod.snd t).symm ; exact False.elim (u₀.not_gt (hx.symm ▸ point_pad M _ _ _ y.2.1 (show (C j y.1).pure=false from rfl) hs)) -- syntax
       rw [h,zero_add]; by_contra e; obtain ⟨i,p',v,x,t,w⟩:= FullWidth P σ Kf W0 Q0 M L C Da ({i},p₀) hs D e; exact u₀.not_gt w
    rw[he]; split; exact AlphaØ.symm; rfl
    -- AlphaY zero

#print axioms VitastroNX
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
