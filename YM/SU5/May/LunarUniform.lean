import YM.SU5.May.LunarCredit
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
open SU Tulip Hygrometry Personality Rush Dial Cube Kea Emu Tilted May.Floe
attribute [local instance] opCStarAlgebra
open Rink Trail
variable (N:Side)(P:Ramp)(b:Bool)(v:Ket (Single N))
variable {D:ℕ} {X:Type*} [Fintype X]
local notation "T"=>rimB N
open Spire Buffered Window Buffered.Afterglow.Satin
abbrev treX (N:Side)(b:Bool):= (if b then (Tset N)ᶜ else Tset N)
def offerK(N:Side)(A:Finset Cover): Finset (Single N):= modesIn N (Buffered.Afterglow.Satin.region A N) -- check region namespace
abbrev tariffS (N:Side)(b:Bool)(A:Finset Cover): Finset (Single N):= treX N b ∩ offerK N A
noncomputable def facesGauge (J:Finset Cover)(b:Bool)(N:Side):= (↑(tariffS N b J):Type)
lemma cHero (S:Finset Cover) (x:Single N)(h:x∈ offerK N S):∃ u:Cover,nodeC u ∈ S∧wrap N u=x.1.1:= by obtain ⟨a,h,e⟩:= Finset.mem_image.mp ((modes_at ..).1 h); obtain ⟨b,v,p⟩:= wrap_nodes N x.1.1 a e; exact ⟨b,v ▸ h,p⟩ -- alias ember b; tune
noncomputable def lampW (J:Finset Cover)(b:Bool)(N:Side) (z: ↥(tariffS N b J)):= (cHero N J _ (Finset.mem_inter.mp z.property).2).choose
variable (S:Finset Cover)
local notation "L"=>tariffS N b S
local notation "E"=> ↑(tariffS N b S)
local notation "Ο" i:max=> lampW S b N i
lemma crystal(i: ↥(tariffS N b S)): nodeC (lampW S b N i)∈ S∧ Buffered.Lifted.index N (lampW S b N i) i.val.1.2 i.val.2=i.val:=by obtain ⟨u,h⟩:=(cHero N S i.val (Finset.mem_inter.mp i.property).2).choose_spec; exact ⟨u, Prod.ext (Prod.ext h rfl) rfl⟩ -- tune index
lemma myLetter (i: ↥(tariffS N b S)): remains b (basisKet i.val.1.2):= by apply Personality.here; obtain ⟨h,_⟩:=mem_inter.mp i.property; cases b <;> unfold treX at h; exact (mem_Tset ..).1 h; exact Finset.mem_compl.mpr fun t=> (Finset.mem_compl.mp h) ((mem_Tset ..).2 t)
-- structure with age fields
variable (z:∀ x:Cover,nodeC x∈ S→Legible P N x)(hp:withinM (treX N b) v)(g:withinM (offerK N S) v)
noncomputable def loan : Trail N P b (↑(tariffS N b S)):= {atSlot:=lampW S b N, appointment:= fun i=> i.val.2, vr:=fun i=>basisKet i.val.1.2, noted:=myLetter N b S, inK:=fun i=> z _ ((crystal N b S i).1), amountC:=fun _=> by simp}
local notation "Ξ"=>loan N P b S z
include hp g
private lemma exits (i:Single N)(p:i∉tariffS N b S): v i=0:=by by_cases h:i∉treX N b; exact (within_test ..).mp hp _ h; exact (within_test ..).mp g _ (fun t=>p (mem_inter.mpr ⟨not_not.mp h,t⟩))
omit hp g
noncomputable def readDust (i: ↥(tariffS N b S)):= v i.val/ Buffered.Lifted.winding N (lampW S b N i)
local notation "W"=>readDust N b v S
private lemma taper (i:E):‖(W) i‖= ‖v i.val‖:=by unfold readDust; rw [norm_div,Buffered.Lifted.winding,fee_norm,div_one]
include hp g z
lemma earningK : (loan N P b S z).lives (readDust N b v S)=v:=by
 have he(i:E): (W) i • cantor N ((Ξ).atSlot i) ((Ξ).appointment i) ((Ξ).vr i)= v i.val • basisKet i.val:=by
    unfold loan; simp only [canto]; rw [basisC,(crystal N b S i).2]; unfold readDust; let U':= Buffered.Lifted.winding N (lampW S b N i); have hz: U'≠0:=norm_pos_iff.mp (by rw [show ‖U'‖=1 from fee_norm _]; norm_num); rw [smul_smul, div_mul_cancel₀ _ hz]
 unfold lives; simp_rw [he]; rw [show (@univ E _)=(L).attach from rfl, sum_attach _ (fun i:Single N=> v i • basisKet i)]; apply Eq.trans ?_ (basis_expand v); refine sum_subset (Finset.subset_univ _) fun i _ t=> ?_; rw [exits N b v S hp g i t,zero_smul]
omit z hp g
noncomputable def volE:ℝ:= 4*Fintype.card SU.Slot
private lemma vol_p:0≤ volE:=by unfold volE; positivity
private lemma logbook : Fintype.card (Single N)= N.val^4*4* Fintype.card SU.Slot:= by simp only [Single,SpinIdx,Fintype.card_prod,Fintype.card_fin]; rw [site_card]
lemma readSize : (∑ i:↥(tariffS N b S),‖readDust N b v S i‖)^2 ≤ volE*(N.val:ℝ)^4* ‖v‖^2:=by
 simp_rw [taper]; rw [show (@univ E _)=(L).attach from rfl,sum_attach _ fun i:Single N=> ‖v i‖]; apply (sq_sum_le_card_mul_sum_sq ..).trans; apply mul_le_mul
 · apply (Nat.cast_le.mpr (Finset.card_le_univ _)).trans; apply le_of_eq; unfold volE; rw [logbook]; push_cast; ring -- args? needs included params
 · rw [PiLp.norm_sq_eq_of_L2]; exact sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _=>sq_nonneg _
 · exact sum_nonneg fun _ _=>sq_nonneg _
 have h:=vol_p; positivity
#print axioms readSize
end YM.CF.May.Lunar
