import ZecaSnow
import ZecaBraid
import YM.SU5.Diva.Tailor
import YM.SU5.Lamour.Matinee
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open Lamour.Bridge CF.Pannier.Chancel
variable {Z θ b v t ε R C ξ:ℝ} {n a y z' k:ℕ}
universe u0
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Lamour.Bridge.Celeste.Morn
open YM.CF.Lamour.Bridge YM.CF.Velvet
open YM.CF.Lamour
open Sonnet
variable {F F':Weaver} -- fix
variable {N:Side}{d r j:ℕ} {A:Finset Cover} {D E:ℝ}
open Tower.SlabMark
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

open Tower Frost
variable {J K:ℕ→ℕ} {I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E0:ℕ → Buffered.Family (tent Y H)→ℂ}
variable (V:Universal Y H J K I E0)
variable {dF:ℕ→Buffered.Family (tent Y H)→ Buffered.Family (tent Y H)}
 {a₀ b₀:ℕ→ℕ}(Q:Coherent (i:=J) (k:=K) (E:=E0) Y H dF a₀ b₀)
 (Qt:Clipped Y H (J ∘ a₀) (K ∘ b₀))
 (O: IcePath Y (J ∘ a₀) (K ∘ b₀))
variable (j:Axis)(U:Arena Y H Q.circuit j 0 false)
local notation "K₀"=>tent Y H
local notation "π" i:max=>J (a₀ i)
local notation "ζ" i:max=>K (b₀ i)

lemma flurry_law(B:Side)(R r p:ℕ): ∀ᶠ w:ℕ in atTop, ∃ θ, 0<θ ∧ flurry B R r p w θ:=by
 let D:=frostD R r p
 filter_upwards [eventually_ge_atTop (max D (Again.plusAgain B D))] with w t
 have b(n:ℕ):n≤ spanSites B n:= Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) B.property)
 let A:=((8*spanSites B (2*w))^4:ℕ)
 let v:= max (A:ℝ) 1
 have hv:0<v:=by unfold v; positivity
 refine ⟨v⁻¹,by positivity,(le_max_left ..).trans (t.trans (b _)),(le_max_right ..).trans (t.trans ?_),?_⟩
 · linarith only [b (2*w)]
 change v⁻¹*(A:ℝ) ≤ 1
 exact (mul_le_mul_of_nonneg_left (le_max_left ..) (inv_nonneg.mpr hv.le)).trans_eq (inv_mul_cancel₀ hv.ne')

include O
lemma crystal_law (t₁: Voice F A) (hp:Geometry P)(t₀:P.Attic)(h:∃ g,Procurement P.K.j g P.d)(v:0<D)(f:Clarity F P.K.j (D/4)):
 ∀ᶠ w in atTop, ∀ᶠ s in atTop, ∀ (e:Entry Y H s j false (2*w)) (z:0<2*w),
    e.val.val = SlabMark.relocate K₀ j w (household K₀ F) →
    ‖boxOp Y H V s Q Qt j false U (2*w) e z‖≤2*(Real.exp 1*D):=by
 let X:=insert 0 A; have t:Voice F X:= t₁.mono (subset_insert ..); let r:=breadth 0 X; let d:=X.card; obtain ⟨C,qC,W⟩:= t.1.rent
 obtain ⟨n,k,g,e,u,w,hK⟩:= choose_optic (P.kJ.symm ▸ (by decide : 1 ≤ (4:ℕ))) (180*d) qC v
 filter_upwards [flurry_law P.block (tent Y H).ℓ r k] with u' hu'
 obtain ⟨ε,hp',t'⟩:=hu'
 obtain ⟨a,v'⟩:=h; obtain ⟨x,hx,vx,F0,Hr⟩:= choose_floor P.K.j (by rw [P.kJ]; decide) (show 0< ε*(8/9) from (by positivity)) hK.zephyr; obtain ⟨ξ,cX,pX⟩:= ((t.1.fee _ hK.zephyr).and self_mem_nhdsWithin).exists; have H':Meringue.{0} Y k r (180*d) e ξ C D ε:= salon Y hK hx vx v' F0 (by rw [show ε/9=ε*(8/9)/8 by ring]; exact Hr) hp' hp t₀ (show 0<ξ from pX) qC v r;
 filter_upwards [H'] with s q
 let B:= SlabMark.relocate K₀ j u' (household K₀ F)
 intro e' z he'
 have hz:0<u':=by omega
 have sale: ∀ᶠ i in atTop,∀ g:Ferry Y s (π i) (ζ i),
       SparseAt Y H s (π i) (ζ i) g j (2*u') B (Real.exp 1*D):=by
    have ht: Tendsto (J ∘ a₀) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    have he:= (count_la Y s).comp ht
    filter_upwards [ht.eventually q,he.eventually (ownsHalo (j:=P.K.j) (by rw [P.kJ]; decide)),he.eventually f,he.eventually (breadthMoney 0 X)] with i yi ya yf yw g
    let N:= count Y s (π i)
    have hh:= ya (Vale.val_e ..)
    apply snow_sparse Y H v g hz t' (snowRate Y H v hp' t' hh (yi (ζ i) g.depth g.enters)) hh j _
        (aux_test (t.1.narrow K₀).widen) (dBook N X)
    rw [show distribute Y H s (π i) (household K₀ F)=F N from resideA F _ _ _,
       show (0:Seat N)=wrap (More N) (0:Cover) from (map_zero _).symm]
    exact ⟨⟨W N,cX N⟩,t.2 N,t.1.bounded N, card_image_le,yw,
     mem_image_of_mem _ (mem_insert_self ..),yf (Vale.val_e ..) _⟩
 obtain ⟨T,g,g'⟩:=e'.prop
 apply mosaic_norm Y H V s Q Qt j false U _ e' z strictMono_id O g' (stayQueue Y H g) (show 0<Real.exp 1*D by positivity)
 rw [he']; exact sale
where resideA(F:Weaver)(A N:Side)(q:A=N): (q ▸ F A)=F N:=by subst N; rfl

end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.crystal_law
