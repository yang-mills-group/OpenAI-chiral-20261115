import GaugeFieldConstruction.Cery
import GaugeFieldConstruction.Lintop
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
variable {N:Side}{P:BudgetPoint}{o:Seat N}{K H:Vow.Pax N}{h a v k b d:ℝ}{r l L n:ℕ} (Tp:Ids N)(M:Tulip.Male)
-- canonical.Core.Clock. root halo (actual supplied).
open Ione QuadClock Beau Salt
open scoped YM.CF.Mew
section
variable {F E: Vow.Pax N}
-- ongoing compilation.
structure SiteFee (p:BudgetPoint)(F:Vow.Pax N)(o:Seat N)(h:ℝ):Prop where
    pays:Turf F
    acts(X:Scree.Hub N)(x:X.val.1=o)(T: Ids N):∃ b,PressB (KeyUp p) X (CosetE (F (lagE X)) T) h b
lemma SF_Q (x:Crafts P o F h a b): SiteFee P F o h:=by
 obtain ⟨u,p,q,l⟩:= x.pays
 refine ⟨x.turf,fun i v T=>⟨u i,?_⟩⟩; have l:=p T i; rw [Penned,if_pos v] at l; exact l
variable (X:Scree.Hub N)
lemma SF_h (p:SiteFee P F o h)(t:X.val.1=o) (q:0 ≤ h): ∃ b,PressB (KeyUp P) X (heart Tp X F) h b:=by
 let A:= Intake X
 let V(i:Aura N):=CosetE (F i) Tp
 have he(i)(v:i∈A):∃ s,PressB (KeyUp P) X (V i) h s:=by
    obtain ⟨p₀,p₁⟩:= (mem_filter.mp v).2; obtain ⟨b,hp⟩:=p.acts (Socket X i) ((Spot_o X i).trans t) Tp
    rw [Spot_y X p₀] at hp; refine ⟨_,cut_further hp ?_ (Spot_o ..) q⟩; rw [Spot_Y X p₀]; exact p₁
 choose! W ht using he
 rw [show heart Tp X F=∑ i∈A,V i from (by funext i; unfold heart; rw [Finset.sum_apply]; unfold V CosetE; rw [Finset.sum_apply])]; exact ⟨_,prop_sum A V W _ _ _ ht⟩
section Ledger
variable {I:Type} (U:Finset I)(C:I→ℂ)(F:I→Vow.Pax N)(p:∀ i∈U,SiteFee P (F i) o h)
lemma Knot_F(x:Aura N): CosetE ((∑ i∈U,C i • F i) x) Tp=∑ i∈U,C i • CosetE ((F i) x) Tp:=by funext y; unfold CosetE; simp [Finset.sum_apply] -- Tune
include p
lemma SF_pool : SiteFee P (∑ i∈U,C i • F i) o h:=by
 refine ⟨?_,fun I t T=>?_⟩
 · intro x v c; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact sum_congr rfl fun i v'=>congrArg _ ((p i v').pays ..)
 rw [Knot_F]; have ht(i)(l:i∈U):∃ b,PressB (KeyUp P) I (C i • CosetE (F i (lagE I)) T) h b:=by
    obtain ⟨b,u⟩:= (p i l).acts I t T; exact ⟨_,Floral.regular_scale _ u⟩ -- tune h shadow type Kxp P.General
 choose! W hp using ht; exact ⟨_,prop_sum U _ W _ _ _ hp⟩
lemma FetchLinear (t:X.val.1=o)(q:0<h)(v:P.order=6)(w:20<N.val) : let G:=∑ i∈U,C i • F i; Fetch Tp M P h X G l n=∑ i∈U,C i • Fetch Tp M P h X (F i) l n:=by
 intro G; let A:= Intake X; let H:= Uptake X; have ht:heart Tp X G=∑ i∈U,C i • heart Tp X (F i):=by
    funext W; unfold G heart CosetE; simp_rw [Finset.sum_apply, Pi.smul_apply,Finset.smul_sum]; rw [sum_comm]
 unfold Fetch integers fract_Z Breath; simp_rw [smul_add,sum_add_distrib,Finset.smul_sum]; rw [ht,ℓExpand M X U C (fun i=>heart Tp X (F i)) (fun i u=> SF_h Tp X (p _ u) t q.le) q w v];
 apply congrArg₂ (·+·)
 · apply congrArg; rw [sum_comm (s:=U)]; apply sum_congr rfl; intro i _; unfold G FlickA; rw [Knot_F,Prop_W] -- tune
 rw [sum_comm (s:=U)]; apply sum_congr rfl; intro i y; unfold perΦ; unfold G; rw [Knot_F]; let L:=Socket X i; let E:=Enlarge L; by_cases g:Cresc l P L; swap; · unfold Ling; simp_rw [if_neg (show ¬ Cresc _ _ (Socket X i) from g)]; rw [locus_K]
 unfold Ling; simp_rw [if_pos (show Cresc _ _ (Socket X i) from g),smul_add,sum_add_distrib]; apply congrArg₂ (·+·); · exact Prop_W ..
 let F'(j):= CosetE ((F j) i) Tp; have hp(j)(u:j∈U):∃ b,PressB (KeyUp P) E (F' j) h b:=by
    obtain ⟨d,x⟩:=(mem_filter.mp y).2; obtain ⟨b,h'⟩:= (p j u).acts _ ((Spot_o X i).trans t) Tp; rw [Spot_y X d] at h'; exact ⟨b,cut_further h' subset_union_left rfl q.le⟩
 exact ℓExpand M E U C F' hp q w v
end Ledger
variable (s:Sweep N)
lemma GrossΔ (p:SiteFee P F X.val.1 h)(q:SiteFee P E (sh s X.val.1) h)(i:Aura N)(v:passingFee N s F E)(T:Ids N): Turns s (CosetE (F i) Tp) (CosetE (E (moldA s i)) T):=by
 constructor; intro x; refine (q.pays (moldA s i) (yellA s (x,Tp)) T).symm.trans ?_ -- check Turf order
 exact v ..
lemma moldW(x:Finset (Seat N))(K:Seat N): (sh s K)∈actY s x↔ K∈x:=by unfold actY sh; simp
lemma IntK(i): i∈Intake X↔ moldA s i∈ Intake (moveHub s X):=by
 rw [mem_filter,mem_filter]; rw [load_Y]; change _ ↔ _∧ sh s X.val.1∈actY s i.val ∧ actY s i.val⊆actY s (lagE X).val; rw [moldW]; simp [actY] -- tune
lemma UltK(i): i∈Uptake X ↔ moldA s i ∈ Uptake (moveHub s X):=by
 rw [mem_filter,mem_filter]; rw [load_Y]; change _ ↔ _∧ sh s X.val.1∈ actY s i.val∧ ¬ actY s i.val⊆ actY s (lagE X).val; rw [moldW]; simp [actY] -- tune
lemma Socket_via (i:Aura N)(h:X.val.1∈ i.val) : Socket (moveHub s X) (moldA s i)=moveHub s (Socket X i):=by
 unfold Socket; rw [dif_pos h,dif_pos (show (moveHub s X).val.1∈(moldA s i).val from (moldW ..).mpr h)]; rfl
lemma Enlarge_via : Enlarge (moveHub s X)=moveHub s (Enlarge X):=by
 apply Subtype.ext; apply Prod.ext; · rfl
 change actY s X.val.2∪(Zhub (sh s X.val.1)).val.2=actY s _; rw [←move_Φ]; unfold actY; simp only [show (Enlarge X).val.2=X.val.2 ∪ _ from rfl,Finset.map_union]; rfl
-- Nonwrapping requirement all short.Port >= post. Buy with actual path. Census post.Diameter.U and L both.
abbrev CapeLen(N:Side)(p:BudgetPoint)(t:ℕ): Prop:= 24≤p.B ∧ 10*((t+1)*(4*p.B+2)+2*p.B) < (More N).val
lemma CapeL (u:CapeLen N P L)(h:coverNumber P.B X.val.2 ≤ L+1): Nonwrapping X.val.2 X.val.1:=by
 intro t p; refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ((Corona.extent _ P.B p X.property).trans ?_)) u.2; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _ -- tune
lemma CapeX (p:CapeLen N P l)(t:Cresc l P X): Nonwrapping (Enlarge X).val.2 X.val.1:=by
 refine CapeL (X:=Enlarge X) p (le_trans (enL X p.1) ?_); have hp:coverNumber P.B X.val.2 ≤ coverNumber P.B X.val.2^3:=Nat.le_self_pow (by decide) _; unfold Cresc at t; omega
lemma LingΔ {T U:InkD N}(p:Turns s T U)(v:∃ b, PressB (KeyUp P) X T h b)(q:∃ b,PressB (KeyUp P) (moveHub s X) U h b)(w:CapeLen N P l)(e:0<h)(hv:100<N.val) : Zvia s (Ling T P (Enlarge X) X h M l n) (Ling U P (Enlarge (moveHub s X)) (moveHub s X) h M l n):=by
 unfold Ling; have hx:Cresc l P (moveHub s X) ↔ Cresc l P X := chose_pull _ -- tune
 by_cases hc:Cresc l P X; swap; · rw [if_neg hc,if_neg (mt hx.mp hc)]; exact locus_pass s p _
 rw [if_pos hc,if_pos (hx.mpr hc)]; obtain ⟨d,v⟩:=v; obtain ⟨b,q⟩:=q; rw [Enlarge_via]; apply Zvia.link _ (Prop_Δ _ _ _ p) (ℓΔ M s (Enlarge X) p (cut_further v subset_union_left rfl e.le) ((Enlarge_via X s) ▸ (show PressB _ (Enlarge (moveHub s X)) U h b from cut_further q subset_union_left rfl e.le)) (CapeX X w hc) e hv n) -- syntax
-- HE fetch.
lemma FetchΔ (p:SiteFee P F X.val.1 h)(q:SiteFee P E (sh s X.val.1) h)(v:passingFee N s F E)(T:Ids N)(u:CapeLen N P l)(e:0<h)(hZ:100<N.val)(z:coverNumber P.B X.val.2≤l+1) : Zvia s (Fetch Tp M P h X F l n) (Fetch T M P h (moveHub s X) E l n):=by
 let Y:= moveHub s X; let G:=moldA s; let U:=Intake X; let Z:= Intake Y; let V(i):= CosetE (F i) Tp; let W(i:Aura N):=CosetE (E i) T
 have hp(i):Turns s (V i) (W (G i)):= GrossΔ Tp X s p q i v T
 have hu:Turns s (heart Tp X F) (heart T Y E):=by
    constructor; intro i; unfold heart CosetE; simp_rw [Finset.sum_apply,map_sum]; symm; exact sum_equiv G (IntK X s) (fun j _=> ((hp j).turns i).symm)
 obtain ⟨b₀,v₀⟩:=SF_h Tp X p rfl e.le; obtain ⟨b₁,v₁⟩:= SF_h T Y q rfl e.le
 unfold Fetch integers Breath fract_Z; apply Zvia.link _ (Zvia.link _ (ℓΔ M s X hu v₀ v₁ (CapeL X u z) e hZ n) _) _ -- order?
 · apply via_sum _ _ _ G (IntK X s); intro i t; unfold FlickA; rw [Socket_via X s i ((mem_filter.mp t).2.1)]; exact Prop_Δ s _ _ (hp i) -- needs hp i
 apply via_sum _ _ _ G (UltK X s); intro i t; unfold perΦ; have ht:X.val.1∈ i.val:=(mem_filter.mp t).2.1; change Zvia s (Ling (V i) _ _ _ _ _ _ _) (Ling (W (moldA s i)) P (Enlarge (Socket _ _)) (Socket (moveHub s X) (moldA s i)) _ _ _ _); rw [Socket_via X s i ht]; apply LingΔ M (Socket X i) s (hp i) _ _ u e hZ
 · have he:= p.acts _ (Spot_o X i) Tp; rw [Spot_y X ht] at he; exact he
 have he:= q.acts _ (Spot_o Y (G i)) T; rw [Spot_y Y (moldW s _ _ |>.mpr ht)] at he; change ∃ a, PressB _ _ _ _ a; rw [←Socket_via _ _ _ ht]; exact he -- tune
#print axioms FetchΔ
end
end
end YM.CF.Oath
end
