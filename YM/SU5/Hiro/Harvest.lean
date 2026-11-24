import YM.SU5.Diva.Tailor
import YM.SU5.Lamour.Matinee
import YM.SU5.Hiro.Bonbons
import YM.SU5.Diva.Jewel
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
-- δ-frequent ballot exterior. Halt condition allowed AFTER λ purchase (arbitr accuracy within same world).
-- adapt stall proof. F now mark, ρ changes at all levels.
abbrev amplitude (C:ℝ)(F:Weaver) : Prop:=∀ (N:Side)(x:Fields N), ‖F N x‖≤ C
def flexTrans (F:Weaver)(A:Finset Cover)(j:ℕ)(ζ ε:ℝ)(N:Side)(M:Tulip.Male):Prop:=∀ X:Fields N,Rightful (dBook N A) X.1 1 ζ→ Rightful (dBook N A) X.2 1 ζ → ∀ x:Wave (Single N),Sea (spar j M (1:Pane N)) x → ‖alleyR (mateK N) x (F N X)‖≤ ε
def Layover (F:Weaver)(A:Finset Cover)(Y:Course P (VolumeCape.Dream.Nimbus l))(J K:ℕ→ℕ)(s:ℕ)(ζ ε:ℝ):Prop:=∃ᶠ i in atTop,∃ᶠ k in atTop, flexTrans F A P.K.j ζ ε (count Y s (J i)) (gram Y s (J i) (K k)).J.M
variable {J K:ℕ→ℕ} {I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E0:ℕ → Buffered.Family (tent Y H)→ℂ}
variable (V:Universal Y H J K I E0)
lemma bigger_palette {B:Finset Cover}{M:Tulip.Male}(F:Weaver)(e:flexTrans F A j v ε N M)(p:A⊆ B):flexTrans F B j v ε N M:= fun Y x y=>e Y (loft_rightful x le_rfl (image_subset_image p)) (loft_rightful y le_rfl (image_subset_image p))
include V
lemma layover_win (hC:0≤C)(hp:Geometry P)(t₀:P.Attic)(h:∃ g,Procurement P.K.j g P.d)(pX:0<ξ) (v:0<D) (A:Finset Cover) : ∀ᶠ s in atTop,∀ F:Weaver, Voice F A→ amplitude C F → Layover F A Y J K s ξ (D/4) → ‖E0 s (household (tent Y H) F)‖ ≤ 4*Real.exp 1*D:=by
 let X:=insert 0 A; let r:=breadth 0 X; let d:=X.card
 obtain ⟨n,k,g,e,u,w,hK⟩:= choose_optic (P.kJ.symm ▸ (by decide : 1 ≤ (4:ℕ))) (180*d) hC v
 let ε:= sealK d k r P.block (reserve P l); have hp':0<ε:= seal_pos ..
 obtain ⟨a,v'⟩:=h; obtain ⟨x,hx,vx,F0,Hr⟩:= choose_floor P.K.j (by rw [P.kJ]; decide) (show 0< ε*(8/9) from (by positivity)) hK.zephyr; have H':Dessert.{0} Y k r (180*d) e ξ C D ε:= suffers Y hK hx vx v' F0 (by rw [show ε/9=ε*(8/9)/8 by ring]; exact Hr) hp' hp t₀ (show 0<ξ from pX) hC v r;
 filter_upwards [many_moments Y H hC (2*(r+k)) H' v hp'.le (sealed Y H d k r)] with s qs; intro F t W h; let E':=household (tent Y H) F; let t:= t.mono (S := A) (show A⊆ X from subset_insert ..)
 let ht:=t.1.narrow (tent Y H); let pL:=V.together s E' (Tower.aux_test ht.widen)
 apply le_of_tendsto_of_frequently pL.periods.norm
 refine ((show ∃ᶠ i in atTop, ∃ᶠ k in atTop, _ from h).and_eventually ((V.pick.grow_i.tendsto_atTop.eventually qs).and (((count_la Y s).comp V.pick.grow_i.tendsto_atTop).eventually (breadthMoney 0 X)))).mono (fun i t'=> ?_)
 apply le_of_tendsto_of_frequently (pL.inner (J i)).norm
 refine (t'.1.and_eventually (V.pick.grow_k.tendsto_atTop.eventually (t'.2.1))).mono (fun l u=> ?_)
 let N:= count Y s (J i); let Z:= dBook N X; let o:= wrap (More N) (0:Cover); let A:=Sonnet.mk (F N) Z o
 have he:A.Cash P.K.j r d (gram Y s (J i) (K l)).J.M e ξ C D:= ⟨W N,t.2 N,t.1.bounded N, card_image_le,fun y q=> t'.2.2 q,mem_image_of_mem _ (mem_insert_self ..),bigger_palette F u.1 (subset_insert ..)⟩
 let y:=u.2 A he (fun _=>from_here _ he); change ‖compass Y _ _ s (send Y H _ s _)‖≤_; apply y.trans'; apply le_of_eq; congr 2; exact resideA F _ N (terrain Y H (Y.ir _) s)
where resideA(F:Weaver)(A B:Side)(g:A=B): (g ▸ F A)=F B:=by subst B; rfl
omit V
lemma mirrorLayover (t:HaloTw j N)(F:Weaver)(i:Axis)(k:ℤ)(M:Tulip.Male)(f:flexTrans F A j v ε N M):flexTrans (fluent i k F) (Tower.reflectedBox i k A) j v ε N M:=by
 intro X p p' x u; rw [d_Book_flip] at p p'; let Z:= fun _:Fields N=>F N (reflFields i k X)
 rw [show fluent i k F N X=reflMark i k Z (1,1) from rfl, mirror_fare i k t u u,norm_star]; exact f (reflFields i k X) (Rightful.land (S:=dBook N A) (i₀:=i) (s₀:=k) (U:=X.1) p) (Rightful.land (S:=dBook N A) (i₀:=i) (s₀:=k) (U:=X.2) p') _ u
lemma travelLayover (t:HaloTw j N)(F:Weaver)(i:Axis)(k:ℕ)(B:Side)(M:Tulip.Male)(f:flexTrans F A j v ε N M):flexTrans (takeoff B F i k) (onFlight B A i k) j v ε N M:=by
 let h:=mirrorLayover t _ i (Heat.gaugeShift B k) M (mirrorLayover t F i 0 M f); rw [Tower.support_translation,sub_zero] at h; exact h
lemma concatLayover {B:Finset Cover}(h:Heather 0 d r C ε j N) (M:Tulip.Male)(uN:flexTrans F A j ξ D N M)(vN:flexTrans F' B j ξ D N M)(u:0≤D)
 (q: A.card ≤ d) (t:B.card ≤ d)(f:Voice F A)(g:Voice F' B)(hp:∀ x,‖F N x‖≤ C)(ht:∀ x,‖F' N x‖≤ C)(e:Distant (r+1) (dBook N A) (dBook N B)) : flexTrans (F*F') (A∪B) j ξ (ε + D^2) N M:=by
 intro X p p' x i; let E:=alleyR (mateK N) x; let a:= F N X; let b:= F' N X; have hZ:‖E (a*b)-E a*E b‖≤ε:= h M _ _ (card_image_le.trans q) (card_image_le.trans t) e _ _ _ (hp _) (ht _) ((f.1.bounded N).allV X) ((g.1.bounded N).allV X) i
 change ‖E (a*b)‖≤_; refine (norm_le_norm_sub_add _ (E a* E b)).trans (add_le_add hZ ?_); rw [norm_mul,sq]; exact mul_le_mul (bigger_palette _ uN subset_union_left X p p' x i) (bigger_palette _ vN subset_union_right X p p' x i) (norm_nonneg _) u
include V
lemma himalayas (pC:0≤C)(j:Axis)(e:0<ε)(u:ε≤1/2)(A: Finset Cover):∀ᶠ k in atTop,∀ s:ℕ,∀ F:Weaver,Voice F A→ amplitude C F→Layover F A Y J K s ξ ε → Layover (father P.block j F k) (claret P.block A j k) Y J K s ξ ε :=by
 have h:1 ≤ P.K.j:=by rw [P.kJ]; decide
 obtain ⟨k,hK⟩:= fragments h A.card C pC (ε/2) (half_pos e)
 filter_upwards [tower_epoch P.block A j (k+1)] with i hx s F t G z
 let W:= onFlight P.block A j i; let Q:= takeoff P.block F j i; let F':=fluent j 0 Q;
 have p: ∀ᶠ N:Side in atTop,Even N.val→∀ M, flexTrans F A P.K.j ξ ε N M → flexTrans (father P.block j F i) (claret P.block A j i) P.K.j ξ ε N M:=by
    filter_upwards [hK,ownsHalo h,distantBook hx] with N p h ht he M gX
    have ht':= t.tract j (Heat.gaugeShift P.block i)
    have hM:= travelLayover (h he) F j i P.block M gX
    refine fun X v w x p'=>le_trans (concatLayover (p he) M (mirrorLayover (h he) Q j 0 M hM) hM e.le (queue_bound (a:=j) P.block A i) card_image_le (B:=W) (ht'.turn j 0) ht' (fun x=> (normReflect ..).trans_le (normTake N (G N) _ _ _)) (fun x=> normTake N (G N) _ _ _) ht X v w x p') (useful _ e u) -- timeout tune
 unfold Layover at *; exact (z.and_eventually (((count_la Y s).comp V.pick.grow_i.tendsto_atTop).eventually p)).mono fun i z=> z.1.mono fun k t=> z.2 (Vale.val_e ..) _ t
lemma bigRegion (U:Geometry P)(q:P.Attic)(g:∃ i,Procurement P.K.j i P.d)(pX:0<ξ)(pC:0≤C)(A:Finset Cover)(j:Axis)(v:0<ε)(w:ε≤1/2):∃ k, Tower.region j 0 (reserve P l) (onFlight P.block A j k) ∧ ∀ᶠ s in atTop,∀ F:Weaver, Voice F A → amplitude C F → Layover F A Y J K s ξ ε →
 ‖E0 s (household (tent Y H) F)‖≤4*Real.exp 1*(4*ε) ∧ ‖E0 s (household (tent Y H) (father P.block j F k))‖≤4*Real.exp 1*(4*ε):=by
 obtain ⟨k,hx,u⟩:= ((himalayas (ξ:=ξ) Y H V pC j v w A).and (prepareLaunch P.block A j (reserve P l))).exists
 refine ⟨k,u,?_⟩
 have ht: ε = 4*ε/4:= by ring
 have hp:0 <4*ε:=by positivity
 filter_upwards [layover_win Y H V pC U q g pX hp A,layover_win Y H V (mul_nonneg pC pC) U q g pX hp (claret P.block A j k)] with s e f F t G L
 have hu(N:Side)(x: Fields N): ‖takeoff P.block F j k N x‖≤C:=normTake N (G N) x j _
 exact ⟨e F t G (ht ▸ L), f _ (t.favor P.block j k) (fun N x=> (norm_mul_le _ _).trans (mul_le_mul ((normReflect _ _ x j 0).trans_le (hu N _)) (hu N x) (norm_nonneg _) pC)) (ht ▸ hx s F t G L)⟩
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.bigRegion
