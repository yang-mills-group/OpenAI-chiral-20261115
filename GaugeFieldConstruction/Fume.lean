import GaugeFieldConstruction.Ei
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
variable (T: Sweep n)(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n)
local notation "Ωv"=> boxA T
open SeasonH
abbrev localSkew (F:Fork n I):Prop:=∀ i j:FinV n,Ekm n i≠ Ekm n j→∀ U:Support (More n),∀ A:Pane n,let x:=cryH F U (0:Key I) A; x i j + x j i=0
lemma slopedR (i j:FinV n)(v:Ekm n i≠ Ekm n j)(B:Op (Single n)):
 let K:=alter_M (halfP V+B) (halfP V-B); K i j+ K j i=0:=by
 intro K; rcases i with ⟨b,i⟩; rcases j with ⟨c,j⟩; have he:i≠j:=fun p=>v (congrArg (fun i:Single n=>node i.1.1) p); cases b <;>cases c<;> simp [K,alter_M,halfP,Matrix.diagonal_apply,he,Ne.symm he]
-- general a
variable {G:Type}[LinearOrder G][Fintype G]
lemma Art_skew (H:G→G→ℂ)(i j:G)(v:H i j +H j i=0): antiB (Icycle H i) (Icycle H j)=0:=by
 let B:= iceK H; have hx: antiB (B i) (B j)=0:=by unfold B iceK; rw [antiB_sum]; refine sum_eq_zero fun j _=> ?_; rw [antiB_smul,antiB_sum']; simp only [antiB_smul', antiB, take_take,smul_zero,sum_const_zero]
 have hu:=heroK H; unfold Icycle; rw [Sault.plus_α,antiB_comm (put j+B j), Sault.plus_α]; -- orient wrong tune
 change antiB (put j) _ + antiB (B j) _+ _= _; rw [show antiB (put j) (put i)=_ from put_put ..,zero_add,hu.tear,antiB_comm _ (B i),Sault.plus_α, antiB_comm _ (put j),hu.tear,antiB_comm _ (B j),hx,add_zero,add_comm,←add_smul,v,zero_smul]
lemma cyBoard (H:FinV n→FinV n→ℂ)(B:Boke n I)(z:Key I): binW (Icycle H) (cryY V z A B)= Lee B (fun i=>egest i V z A • logL (Icycle H) i.val):=by
 unfold cryY; rw [show ∀ v: PairLog (FinV n),binW (Icycle H) v=(binW (Icycle H)).toAddMonoidHom v from fun _=>rfl, sealA]; refine paidA _ _ _ fun i _=>?_ ; change binW _ (_ • _)= _; rw [map_smul]; apply congrArg (egest _ _ _ _ • ·); change (∑ j,(Pi.single i.val 1:RankU n→ℂ) j • logL (Icycle H) j)= _; rw [sum_eq_single i.val]; simp; intro k _ p; simp [p]; simp
lemma antiQ (A B C:FC G)(v:antiB A B=0)(h:antiB A C=0): Commute A (B*C):= sub_eq_zero.mp ((oakV _ _ _ (0:ℂ) (0:ℂ) (by simpa using v) (by simpa using h)).trans (by simp))
lemma Φhears (w:localSkew I F)(X Y:Vulcan I n)(p:Linca P σ X)(q:Linca P σ Y)(v:Disjoint X.seat Y.seat): let H:=Icycle (cryH F V (0:Key I) A); Commute (logL H X.val) (logL H Y.val):=by
 intro H; rcases h:X.val with _|⟨i,j⟩; exact Commute.one_left _
 rcases g:Y.val with _|⟨k,l⟩; exact Commute.one_right _; have hp:=p.legs i j h; have hh:=q.legs k l g
 have he(i j)(p0:Ekm n i∈X.seat)(p1:Ekm n j∈Y.seat): antiB (H i) (H j)=0:= Art_skew _ _ _ (w i j (fun z=> Finset.disjoint_left.mp v (z ▸ p0) p1) _ _ ) -- z ▸ direction
 exact (antiQ (H i) _ _ (he _ _ hp.1 hh.1) (he _ _ hp.1 hh.2)).mul_left (antiQ _ _ _ (he _ _ hp.2 hh.1) (he _ _ hp.2 hh.2))
lemma comm_Λ {ι κ:Type}(X:List ι)(Y:List κ)(A:ι→ FC G)(B:κ→ FC G)(p:∀ i∈ X,∀ j∈ Y,Commute (A i) (B j)):Commute (Lee X A) (Lee Y B):=by
 have he(i)(v:i∈ X):Commute (A i) (Lee Y B):=by induction Y with|nil=>exact Commute.zero_right _|cons b t ih=>rw [consA]; exact (p _ v b List.mem_cons_self).add_right (ih fun i v j u=> p i v _ (List.mem_cons_of_mem _ u))
 induction X with|nil=>exact Commute.zero_left _|cons a X h=>rw [consA]; exact (he _ List.mem_cons_self).add_left (h (fun i t=>p i (List.mem_cons_of_mem _ t)) fun i p=>he i (List.mem_cons_of_mem _ p))
variable (L L' T':List I)(h:L.Nodup)(tZ:L'.Nodup)(f:T'⊆L)(u:T'⊆L')
variable (κ:localSkew I F)(p:∀i∈T',CostP σ P (M i))(q:∀ i∈T',∀j∈T',σ i≠σ j →∀ x∈M i,∀ y∈ M j,Disjoint x.seat y.seat)
include h tZ f u κ p q
lemma Reorders (v: ψS σ T'): FairOrder I σ L L' T' F M:=by
 intro Z A l hs H; let V:=fun i=>artΨ0 I Z A H (M i); let K:=skimT I L l; let K':=skimT I L' l
 have he(m:List I)(p:m.Nodup)(x:l⊆m): (skimT I m l).Perm l:=by
    apply List.perm_of_nodup_nodup_toFinset_eq (p.filter _) (hs.nodup (List.Nodup.of_map σ v)); ext i; simp only [List.mem_toFinset,List.mem_filter,skimT,decide_eq_true_eq]; exact and_iff_right_of_imp fun p=>x p -- tune
 have hp: K.Perm l:=he _ h (List.Subset.trans hs.subset f); let W: K.Perm K':= hp.trans (he _ tZ (List.Subset.trans hs.subset u)).symm; change (K.map V).prod=(K'.map V).prod; apply List.Perm.prod_eq' (W.map V); rw [List.pairwise_map]; have hn: (K.map σ).Nodup:=(hp.map σ).nodup_iff.mpr ((hs.map σ).nodup v);
 refine (List.pairwise_map.mp hn).imp_of_mem fun {i j} pi pj hij=>?_ -- tune
 have hx:= hs.subset (hp.mem_iff.mp pi); have hy:=hs.subset (hp.mem_iff.mp pj); unfold V artΨ0; rw [cyBoard,cyBoard]; refine comm_Λ _ _ _ _ fun x a y b=> ?_; exact ((Φhears I σ _ A F P κ x y (p i hx x a) (p j hy y b) (q i hx j hy hij x a y b)).smul_left _).smul_right _ -- tune
#print axioms Reorders
end MintB
end MastTin
end YM.CF.XGarden
end
