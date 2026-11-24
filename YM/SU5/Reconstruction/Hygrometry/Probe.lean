import YM.SU5.Reconstruction.Hygrometry.Salary
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
variable {α : Type*} {N m L B: Side} {j:ℕ}{r:ℝ}
-- false = create. Use boolean to align `Θ` μ berry (odd phase distinct).
open Buffered.Lifted Rush
abbrev remains (b:Bool) (u:Ket SpinIdx) := acts Aop u= if b then 0 else u
abbrev payroll (b:Bool) := if b then plusHalfᶜ else plusHalf
structure Personality where
 down:Bool
 color:Slot
 voice:Ket SpinIdx
 signed : remains down voice
namespace Personality
private lemma PinGrade: Aop=cutM plusHalf:= Adef.trans raising.symm
lemma here (k:SpinIdx) (b:Bool) (e:k ∈payroll b) : remains b (basisKet k):=by
 cases b
 · change acts Aop (basisKet k)=basisKet k
   rw [PinGrade,cut_basis,if_pos (show k∈plusHalf from e)]
 change acts Aop _=0; have hl:k∉plusHalf:= mem_compl.mp e; rw [PinGrade,cut_basis,if_neg hl]
lemma absent (x:Personality) (k:SpinIdx) (e:k∉payroll x.down): x.voice k=0:=by
 have he:= x.signed; unfold remains at he; rw [PinGrade] at he
 let P:=cutM plusHalf; have hu:= act_inner (cutM plusHalf) (basisKet k) x.voice; rw [(cutM_idp plusHalf).isSelfAdjoint.star_eq,he] at hu -- tune let P
 cases u:x.down
 · have hv:k∉plusHalf:= by simpa [u,payroll] using e
   rw [u,if_neg (by decide), cut_basis,if_neg hv,inner_zero_left,basis_inner] at hu; exact hu.symm
 have hv:k∈plusHalf:= by simpa [u,payroll] using e
 rw [u,if_pos rfl,cut_basis,if_pos hv,inner_zero_right,basis_inner] at hu; exact hu
lemma hymn(x:Personality):∑ i∈payroll x.down, x.voice i • basisKet i=x.voice:=by
 refine (sum_subset (subset_univ _) ?_).trans (basis_expand x.voice)
 intro i h v; rw [x.absent i v,zero_smul]
noncomputable def pureV (b:Bool)(x:Slot)(k:SpinIdx)(p:k∈payroll b):Personality:=⟨b,x,basisKet k,here k b p⟩
end Personality

-- placement. All finite Vols.
def cantor (N:Side)(x:Cover)(t:Slot)(v:Ket SpinIdx): Ket (Single N) := ∑ i, v i • basisC N x i t
noncomputable def pitch (N:Side)(x:Cover)(R:ℝ)(t:Slot)(v:Ket SpinIdx):= Emu.gain R • cantor N x t v
lemma canto (x:Cover)(t:Slot)(k:SpinIdx): cantor N x t (basisKet k)= basisC N x k t:=by unfold cantor; simp [ite_smul]
lemma pitch_sum (x: Personality)(R:ℝ)(z:Cover):
    pitch N z R x.color x.voice=∑ i ∈ payroll x.down, x.voice i • pitch N z R x.color (basisKet i):= by
 simp_rw [pitch,canto]; unfold cantor; rw [Finset.smul_sum];
 refine (sum_subset (subset_univ (payroll x.down)) ?_).symm.trans ?_ -- orientation tune
 · intro i h v; rw [x.absent i v,zero_smul,smul_zero]
 exact sum_congr rfl fun i _=> smul_comm ..

private lemma projected (z: Cover)(p:Slot)(k:SpinIdx):hint (0:Site N) z ⟨k,p,1⟩ (Kea.tax emptyC) 1=basisC N z k p:=by
 have hp : ∀ d:Candle,hint (0:Site N) z ⟨k,p,1⟩ (Kea.tax d) 1=star (newm d z p) • basisC N z k p:= fun d=>by
    rw [Emu.tax_f,basisC,smul_smul]; unfold Emu.hub Rush.wind; change (Rush.fee _* star _) • basisKet ((0+wrap N z,k),p)= _; rw [show natural (0:Site N)=0 by funext j; simp [natural],zero_add,zero_add,mul_comm]; rfl
 rw [hp]; suffices newm emptyC z p=1 by rw [this,star_one,one_smul]
 unfold newm; rw [Kea.visor]; simp [tmap,mode] -- tune
lemma down_here {k:SpinIdx}{b:Bool}(u:k∈ payroll b)(p:Slot) : signW ⟨k,p,1⟩=b :=by cases b; simp [signW,show k∈plusHalf from u]; simp [signW,show k∉plusHalf from mem_compl.mp u]

def player (N:Side)(x:Cover)(R:ℝ)(t:Personality): Reader0 (Single N):= (t.down,if t.down then -(pitch N x R t.color t.voice) else pitch N x R t.color t.voice)
lemma player_pure (z: Cover)(R:ℝ)(b:Bool)(p:Slot)(k:SpinIdx)(u:k∈payroll b): player N z R (Personality.pureV b p k u) = nac (0:Site N) (Kea.tax emptyC) 1 R (z,⟨k,p,1⟩) :=by unfold player Personality.pureV nac; dsimp only; rw [down_here u,projected,pitch, canto]
lemma pitch_tones (z: Cover)(R:ℝ)(x:Personality) : acts (tickA N) (pitch N z R x.color x.voice)=if x.down then 0 else pitch N z R x.color x.voice:=by
 rw [pitch_sum x,map_sum]
 have he(i:SpinIdx)(u:i∈payroll x.down):acts (tickA N) (pitch N z R x.color (basisKet i))=if x.down then 0 else pitch N z R x.color (basisKet i):=by
    unfold pitch; rw [canto,←projected _ x.color i,map_smul,hinge,down_here u]; split <;> simp_all
 simp_rw [map_smul]
 refine (sum_congr rfl (show ∀ i∈payroll x.down, x.voice i • _=x.voice i • (if x.down then 0 else pitch N z R x.color (basisKet i)) from fun i u=>congrArg _ (he i u))).trans ?_
 split <;> simp_all
lemma player_tones(z:Cover)(R:ℝ)(x:Personality): KeyT (player N z R x) (tickA N):=by
 unfold KeyT player; dsimp only
 cases b:x.down <;> simp [map_neg,pitch_tones,b]

/-- normalized pose cost at this point. -/
def SpinPrice (p: Wave (Single N))(A: FC (Single N)) := inner ℂ (mateK N) (acts A p)/inner ℂ (mateK N) p
lemma SpinPrice.pair (c:Wave (Single N))(A B:FC (Single N)) : SpinPrice c (A+B)=SpinPrice c A+SpinPrice c B:=by simp [SpinPrice,add_div]
lemma SpinPrice.cash (c:Wave (Single N))(A:FC (Single N))(d:ℂ):SpinPrice c (d • A)=d*SpinPrice c A:=by rw [SpinPrice,act_smul,inner_smul_right,mul_div_assoc]; rfl
lemma SpinPrice.pool (c:Wave (Single N))(S:Finset α)(F:α→ FC (Single N)):SpinPrice c (∑ i∈S,F i)=∑ i∈S,SpinPrice c (F i):=by rw [SpinPrice,act_sum,inner_sum,Finset.sum_div]; rfl

-- unconditionally at those poses.Def analytical b pair and ALL polynomial calls, irrespective of Root expectation.Cluster. Preserve CAR ordering.
variable (M:Jill.Male) {v:Wave (Single N)} (e:Even N.val)(hj: 1≤ j)(hp:Sea (latPose j M N) v)
include e hj hp
lemma reckons (Z:α→Reader0 (Single N))(p:∀ i,KeyT (Z i) (tickA N))(T:List α): SpinPrice v (rollC (ton ∘ Z) T)= Emu.runes (fun a b=> rankG (ledger N j M) (Z a) (Z b)) T:= by
 let A:=rollC (ton ∘ Z) T
 have he:= Emu.frown (clad_service M e hj) (tickB N) hp Z p T; rw [quant_one, skyGlow] at he; -- quant_one inside pRead too tune
 unfold Emu.pRead at he; simp only [mul_one, quant_one, act_one] at he
 unfold SpinPrice; rw [he]; exact mul_div_cancel_left₀ _ (can_spend e hj hp)
omit e hj hp
lemma duo {α:Type*}(R:α→α→ℂ)(p q:α): Emu.runes R [p,q]= R p q:= by simp [runes, spinC, offer, claps,picks, cites,besideX,Fock.cval,extendsU]
end YM.CF.Hygrometry
