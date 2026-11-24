import GaugeFieldConstruction.Metron
import GaugeFieldConstruction.Caliber
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
set_option autoImplicit false
set_option maxHeartbeats 400000
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
variable (Q:Scree.Hub N)
variable (t:Crafts P Q.val.1 K h 2 b)(p:0<h) (q:P.order=6)(s:P.power=2)(u:24≤P.B)(w:coverNumber P.B Q.val.2 ≤ L) (g:(Zhub Q.val.1).val.2⊆ Q.val.2) (hv:300<N.val)(e:n≤2) (hk:TarKen (KeyUp P) Q.val.1 (lagE Q) h 2 a d K)
include hk e hv g w u s q p t
abbrev IaTax (P:BudgetPoint)(L:ℕ)(t:ℝ):= Real.exp (3*(L:ℝ))*(2*chi_f P.order*Jε*t+chi_f P.order*t)
abbrev AtTax (P:BudgetPoint)(L:ℕ)(c:ℝ):= Real.exp (3*(L:ℝ))*(2*chi_f P.order*c)
lemma Deal_u : Basalt P Q.val.1 l L (integers Tp M P h Q K n) (PieceFee a) 2 (IaTax P L a+ AtTax P L b) h n M ∧∀ j≤ n,MSlot j (SealT (Zhub Q.val.1) (((integers Tp M P h Q K n).1) (Zhub Q.val.1)) (KeyUp P) h M)=MSlot j (SealT Q (heart Tp Q K) (KeyUp P) h M):=by
 let A:= Intake Q; let X:= heart Tp Q K; let P':=KeyUp P; let A₀:=ℓParcel n Q P h M X
 obtain ⟨c,r,hX,hA⟩:= cub_B Tp Q t p q s u w g hv e hk
 have hp: c ≤a:= (le_mul_of_one_le_left r (show 1 ≤ Trees.currency P.B 2 Q.val.2 from Real.one_le_exp (by positivity))).trans hA
 obtain ⟨F₀,f,r₀,b₀,t₀⟩:=t.pays
 let TQ(i:Aura N):= F₀ (Socket Q i); let C:= Trees.currency P.B 3 Q.val.2; let u0 :ℝ:=Real.exp (3*(L:ℝ)); let U:=chi_f P.order;
 have hU:C≤u0:= Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr w) (by norm_num))
 have h':= Jε₀; have hw:=spicy_f P.order; change 0≤ U at hw
 have he: PieceCost P Q c ≤ IaTax P L a:=by change C*(2*U*Jε*c+U*c) ≤ u0*(2*U*Jε*a+U*a); have ha:=r.trans hp; have hb:0 ≤ C:=(Real.exp_pos _).le; gcongr
 have hℓ: PieceFee (Trees.currency P.B 2 Q.val.2*c) ≤ PieceFee a:=mul_le_mul_of_nonneg_left hA (show 0≤ 3+2*Jε by positivity)
 have hB: Basalt P Q.val.1 l L A₀ (PieceFee a) 2 (IaTax P L a) h n M:= (piece_B hX (by norm_num: 0≤(2:ℝ)) p hv q s M e g w).sharpen hℓ he
 have ht : (∑ i∈ A,TQ i) ≤ b:=by
    apply le_trans _ t₀; let D:= A.image (Socket Q); unfold ΩBook; apply le_trans (b:=∑ x∈ D,Tollup 2 P x * F₀ x) _ (sum_le_sum_of_subset_of_nonneg (subset_univ D) fun i v u=>mul_nonneg (Real.exp_pos _).le (r₀ _)); unfold D; rw [sum_image _]; · exact sum_le_sum fun i _=>le_mul_of_one_le_left (r₀ _) (show 1 ≤ Tollup 2 P _ from Real.one_le_exp (by positivity))
    intro x a y b he; rw [←Spot_y Q ((mem_filter.mp (show x∈ A from a)).2.1),←Spot_y Q ((mem_filter.mp (show y∈A from b)).2.1),he]
 have hf(i)(Hρ:i∈A): PressB P' (Socket Q i) (CosetE (K i) Tp) h (TQ i):=by
    have hx:=f Tp (Socket Q i); rw [Penned,if_pos (Spot_o Q i),Spot_y Q ((mem_filter.mp Hρ).2.1)] at hx; exact hx
 let H(i:Aura N):= AtTax P L (TQ i)
 have hg(i)(h':i∈A): Basalt P Q.val.1 l L (FlickA Tp Q i K) 0 2 (H i) h n M:=by
    obtain ⟨e₀,g₁⟩:=(mem_filter.mp h').2; let Z:=Socket Q i; have t':Z.val.2⊆Q.val.2 := (Spot_Y Q e₀).symm ▸ g₁; have u:= cen_pr Q (hf i h') t' (Spot_o ..) p s w (a:=2) (l:=l) (r:=n) (M:=M); refine (Spot_o Q i) ▸ u.sharpen le_rfl (mul_le_mul_of_nonneg_right hU ?_); exact mul_nonneg (mul_nonneg (by positivity) (spicy_f _)) (r₀ _)
 let K0:= Breath Tp Q K; have hv':Basalt P Q.val.1 l L K0 0 2 (AtTax P L b) h n M:=by
    have ht':= Basalt.sumA A _ _ H hg p.le; exact ht'.sharpen (by simp) (by unfold H AtTax; rw [←mul_sum]; simp_rw [←mul_sum]; unfold u0 U at *; gcongr -- likely unresolved
    )
 have hZ:PieceFee a+0=PieceFee a:=add_zero _
 refine ⟨hZ ▸ hB.terms hv' p.le, fun j u=> ?_⟩
 have hp: K0.1=0:=by
    unfold K0 Breath; rw [_root_.Prod.fst_sum]; simp only [FlickA,Propulse,bury,sum_const_zero]
 rw [show (integers Tp M P h Q K n).1 = A₀.1 from (show A₀.1+ K0.1=_ from (by rw [hp,add_zero]))]; exact Parcel_root hX p hv q M j u e g
lemma Tax_C : Basalt P Q.val.1 l (l+1) (fract_Z Tp M P h Q K l n) (Etching 2 d) 2 (Flame_B P (l+1) d) h n M:=by
 obtain ⟨F₀,f,r₀,b₀,t₀⟩:=t.pays; obtain ⟨V,v,u'₀,hK⟩:=hk.exterior; let B:=Uptake Q; let I(j):= Socket Q j; let U:= Q.val.1; let P':=KeyUp P; let F(i:Aura N):=joinV (Scree.tariff P' U h) (V i); let TQ(i:Aura N):= Etching 2 (Esk P' h 2 U i (V i)); let A:= l+1
 have ht(Q):=v Q; have hv'(i: Aura N):0 ≤ F i:= sum_nonneg (fun j _=>mul_nonneg (by unfold Scree.tariff; positivity) (v _ _))
 have hx(i)(g':i∈B):Basalt P U l A (perΦ Tp i Q K P h M l n) (TQ i) 2 (Flame_B P A (F i)) h n M:=by
    obtain ⟨Hρ,h'⟩:=(mem_filter.mp g').2; let D:= I i; let z:= CosetE (K i) Tp; have he:D.val.1=U:= Spot_o Q i; have hz:D.val.2=i.val:= Spot_Y Q Hρ; have ht:= f Tp D; have hf:PressB P' D z h (F i):=by
       rw [Penned, if_pos he,show lagE D=i from Subtype.ext hz] at ht
       refine ⟨ht.term,ht.fitted,ht.measureV,ht.gaugeV,V i,v i, fun x=>?_,?_⟩
       · let hh:D=⟨(U,i.val),Hρ⟩:=Subtype.ext (Prod.ext he hz); rw [hh]; exact hK _ g' _ _ -- tune
       rw [he]
    have hh:=runlet (l:=l) hf (by norm_num:0≤(2:ℝ)) p hv q s M e u; rw [he,hz] at hh; exact hh
 have he: (∑ i∈B,F i)≤ d:=by apply le_trans _ u'₀; exact sum_le_sum fun i _=>le_mul_of_one_le_left (hv' i) (show 1≤Trees.currency P.B 2 i.val from Real.one_le_exp (by positivity)) -- Types inference Gpay
 refine (Basalt.sumA B _ _ _ hx p.le).sharpen ?_ ?_; · unfold TQ Etching PieceFee; rw [←mul_sum,←mul_sum]; have he:= Jε₀; gcongr
 let hx:=spicy_f P.order; have hy:=Jε₀; unfold Flame_B; rw [←mul_sum]; simp_rw [sum_add_distrib,←mul_sum]; gcongr -- duplicates Q variable.Concern bind
lemma fullB (e':L=l+1) : Basalt P Q.val.1 l L (Fetch Tp M P h Q K l n) (PieceFee a + Etching 2 d) 2 ( (IaTax P L a+ AtTax P L b)+Flame_B P L d) h n M:= ((Deal_u Tp M Q t p q s u w g hv e hk).1.terms (e'.symm ▸ Tax_C Tp M Q t p q s u w g hv e hk) p.le) -- tune Torus.
end
end YM.CF.Oath
end
