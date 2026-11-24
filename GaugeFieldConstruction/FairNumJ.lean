import GaugeFieldConstruction.TurnBridgeJ
import GaugeFieldConstruction.FineAlJ
import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k:ℕ) {P' V: Side} {f r t v :ℕ}
local notation "B"=> P.block
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "X_" s:max=> RootBook Y i k s
local notation "µ" s:max=> city (Ω s)
variable {I J G:Type} [Fintype I] [Fintype J][LinearOrder I][LinearOrder J] [LinearOrder G]
variable (p:(Y.voyage i).kick≤ k)
local notation "ν"=> Y.uv k
local notation "θ"=> P.R.L
variable (w:I→G)(X: HousingJ Y i G)(K:G→Prop)(t:f ≤Y.uv k)(E: List I→Orbit (side Y i f)→ Phys (side Y i f))(A:I→Mark (side Y i (Y.uv k)))
variable {N:Side}
variable (σ:I→Seat (side Y i f))(R:I→I→ℂ)
variable (vP:κWork G (Seat (side Y i f)) w σ)
local notation "κ0"=> RevenueT Y i k
local notation "ƒ"=> convoy Y i k t
local notation "Gc"=> city (side Y i (Y.uv k))
-- scalar shift law offset taps
variable (F: Finset I→ RegBudget (side Y i f))(Z:Finset I→ForceBudget (side Y i f))(V:I→ℂ)
local notation "Λt"=> RootBook Y i k f
local notation "Ux"=> (Y.voyage i).CapeT f
abbrev Ask (σ:I→Seat (side Y i f))(F: Finset I→ RegBudget (side Y i f))(Z:Finset I→ForceBudget (side Y i f)) := TraceJ P.U (RootBook Y i k f) ((Y.voyage i).CapeT f) σ F Z
-- choice.paid orientation $κ.C0 comparator*. expose sign later.
local notation "ΦT"=>Ask Y i k σ F Z
abbrev ιShank (W:I→ℂ)(Q: List I→ Orbit N→Phys N)(L0:List I)(i:Orbit N): Phys N:=∑ j∈ L0.toFinset.powerset,(List.map W (Roots.wingX L0 j)).prod • Q (wingR L0 j) i
abbrev ΔArz {E:Type}[Ring E][Algebra ℂ E](A:I→E)(W:I→ℂ):I→E:=fun i=> A i+ W i • 1
variable {g:ℂ}
lemma inputRunV (u:Key I→ℂ)(q:River u)(x:Orbit (side Y i f)) : River fun z:Key I=> denZ (BreathJ Λt σ F Z (u z) z) P.U Ux x:=by
 let K:= Λt; let A:=Ux
 let R(z):= K.F+ WritV σ F z; let T (z):= K.K+ WritV σ Z z; let S(_:Key I):= K.slip; let L(z):= K.v+u z
 change River fun z=> denZ (color_b K K.beta (R z) (S z) (T z) (L z)) P.U Ux x
 have hPhi{E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{f:Key I→E}(p:River f): Law_C σ 0 [] f f:=⟨p,p,fun i u=>by rw [List.sublist_nil.mp u]; exact rfl⟩
 have vPhi {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](a:E)(P:Finset I→E):River (fun z:Key I=>a+ WritV σ P z):= dub_V (zeroR a) (tip_bank _ _ fun i _=>lift_b i _).1 -- tune
 let http:= pulse_H (U:=P.U) P.V σ 0 [] (by simp[ψS]) K A R R S S T T L L x
 refine (http ?_ ?_ ?_ (hPhi (dub_V (zeroR _) q))).1
 · intro i j; apply hPhi; unfold R WritV; simp_rw [Pi.add_apply,Finset.sum_apply, Pi.smul_apply]; exact vPhi _ (fun k=>F k i j)
 · exact fun i t=> hPhi (zeroR _)
 intro i j; apply hPhi; unfold T WritV; simp_rw [Pi.add_apply, Finset.sum_apply,Pi.smul_apply]; exact vPhi _ (fun k=>Z k i j)
lemma axis_ζ (L:List I)(p:L.Nodup): ΦT (rideN V) L= ιShank V (ΦT 0) L:=by
 funext x
 let fT(z:Key I):=denZ (BreathJ Λt σ F Z ((0:Key I→ℂ) z) z) P.U Ux x; let H:= ContinuousLinearMap.lsmul ℂ ℂ (E:=Phys (side Y i f)) -- arg tune name
 let T (z:Key I):= denZ (BreathJ Λt σ F Z (rideN V z) z) P.U Ux x
 have q : River fT:=inputRunV Y i k σ F Z 0 (zeroR _) x
 let X:=Complex.exp ∘ rideN V
 have r: River X:=by unfold X; rw [Complex.exp_eq_exp_ℂ]; exact (rideFlow V).exp_V
 have v:T=GJ.pulseV H X fT:=by
    funext i'; unfold T GJ.pulseV fT BreathJ; rw [show (0:Mew.Key I→ℂ) i'=0 from rfl,add_zero]; exact vig_v P.V _ _ _ _ _ _ -- argument _
 change tipI T L=_; rw [v,distrD H r q]; exact Finset.sum_congr rfl (fun i' h'=> by unfold X; rw [tipFire V (Roots.wingX L i') ((wing_sub _ _).nodup p)]; rfl)
 exact p
-- pure polynomial order works also noncomm.E
lemma stakeW {E:Type}[Ring E][Algebra ℂ E](A:I→E)(W:I→ℂ)(L0:List I)(u:L0.Nodup): (L0.map (ΔArz A W)).prod=∑ j∈ L0.toFinset.powerset,(List.map W (Roots.wingX L0 j)).prod • (List.map A (wingR L0 j)).prod:= by
 induction L0 with
 | nil=> simp only[List.toFinset_nil,powerset_empty,sum_singleton]; exact (one_smul _ _).symm -- tune
 | cons i l ih=>
    have hx:=List.nodup_cons.mp u; have hv:i∉l.toFinset:=by simpa using hx.1
    rw[List.map_cons,List.prod_cons, ΔArz,ih hx.2, add_mul,Finset.mul_sum, Finset.mul_sum,List.toFinset_cons,powerset_insert,sum_union,sum_image]; rotate_left
    · intro a₁ h₁ b₁ h₂ w; have ha:i∉ a₁:=fun v=> hv (mem_powerset.mp h₁ v); have hb:i∉ b₁:= fun v=>hv (mem_powerset.mp h₂ v); simpa [ha,hb] using congrArg (fun s:Finset I=>s.erase i) w -- tune
    · apply Finset.disjoint_left.mpr; intro j v w; obtain ⟨k,t,rfl⟩:=mem_image.mp w; exact hv (mem_powerset.mp v (mem_insert_self ..))
    apply congrArg₂ (· + ·) ?_ ?_
    · apply sum_congr rfl; intro j g; have he:i∉ j:= fun p=> hv (mem_powerset.mp g p); rw [show Roots.wingX (i::l) j=Roots.wingX l j from (by simp [Roots.wingX,he]),show wingR (i::l) j=i::wingR l j from (by simp [wingR,Roots.wingX,he]),List.map_cons,List.prod_cons, Algebra.mul_smul_comm]
    apply sum_congr rfl; intro j g; rw [show Roots.wingX (i::l) (insert i j)= i::Roots.wingX l j from (show Roots.wingX (i::l) _=_ from (by
            rw [show Roots.wingX (i::l) (insert i j)=i::Roots.wingX l (insert i j) from (by simp [Roots.wingX]), wingπ _ _ _ hx.1])),show wingR (i::l) (insert i j)=wingR l j from ?_, List.map_cons,List.prod_cons, Algebra.smul_mul_assoc,one_mul,mul_smul] -- order
    rw [show wingR _ _=wingR l (insert i j) from (by simp [Roots.wingX,wingR]),wingRπ _ _ _ hx.1]
variable (p0:Entourage Y i k w X K t E A)
lemma tier_day (L: List I): ιShank V E L=∑ j∈L.toFinset.powerset,(List.map V (Roots.wingX L j)).prod • E (wingR L j) :=by funext i; unfold ιShank; rw [Finset.sum_apply]; rfl
include p p0 vP
lemma αPlanet : Entourage Y i k w X K t (ιShank V E) (ΔArz A V):=by
 letI :LinearOrder (Finset I):= LinearOrder.lift' _ (Fintype.equivFin (Finset I)).injective
 let G:= ΔArz A V; have hx(L:List I)(h:galaJ w L)(j:Finset I):galaJ w (wingR L j):= List.Pairwise.sublist ((wing_sub L jᶜ).map _) h -- tune
 have hv':= p0.stamped; refine ⟨⟨fun i'=> (hv'.owns _).addM (PostSupport.of ((AtSupport.oneM _).smulM _)),fun j v'=> (hv'.slit j v').addM (PostSupport.of ((AtSupport.oneM _).smulM _))⟩,fun l v=> ?_,fun l v C W h=>?_⟩
 · rw [tier_day]; exact rackTJ _ _ (fun i _=> multV (p0.lease _ (hx l v i))) -- Fintype Finset.LinearOrder instance? 
 have he:=h.2.mono (subset_univ _); let U:= convoy Y i k t W; have ht:safeJ U:= PostSupport.of (convoy_all Y i k p t le_rfl he)
 have pu:= List.Nodup.of_map σ (gala_ψ Y i w σ vP _ v)
 rw [tier_day, cost_vJ, stakeW A V l pu,Finset.mul_sum]; rotate_left
 · exact fun i _=>multV (p0.lease _ (hx l v i))
 · exact he.env
 simp_rw [Algebra.mul_smul_comm]; rw [decid_JT Y i k p]; rotate_left -- tune
 · intro i' _; exact (ht.mulM (cons_JT Y i k A hv'.owns _)).smulM _
 refine Finset.sum_congr rfl (fun j v'=> ?_)
 rw [spunT]; exact (ring_scale (f:=f) Y i W (α:= E (wingR l j)) _).trans (congrArg (fun z:ℂ=> _ • z) (p0.fare _ (hx l v j) C W ⟨Disjoint.mono_right (show (List.map w (wingR l j)).toFinset⊆(l.map w).toFinset from (fun i t=> List.mem_toFinset.mpr (((wing_sub l jᶜ).map w).subset (List.mem_toFinset.mp t)))) h.1,h.2⟩)) -- lemma name check
#print axioms axis_ζ
#print axioms stakeW
#print axioms αPlanet
#check distrD
#check lift_b
#check Law_C
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
