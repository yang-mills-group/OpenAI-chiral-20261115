import YM.CF.Tarn.Tag
import YM.CF.Souk.Rayon
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable {H:Support c}{M N:Monk G S}{j:ℕ}
-- pins
variable {r:ℕ}{w:LinkS S j}{o:Site c}
def grove(S:StepData c f)(i:Bond f):= (pinPos i).image S.ratio.parent
lemma grove_x(i:Bond f) : ((grove S i: Support c): Set (Site c)) = Next.SectorChange.points S i:=by unfold grove pinPos Next.SectorChange.points; rw [image_insert,image_singleton, coe_insert,coe_singleton]
lemma grove_n (S:StepData c f)(i:Bond f): (grove S i).Nonempty:= ⟨S.ratio.parent i.1, mem_image.mpr ⟨_,mem_insert_self ..,rfl⟩⟩
def plant(S:StepData c f)(o:Site c)(w:LinkS S j):ℝ:= if o∈grove S (w 0) then ((grove S (w 0)).card:ℝ)⁻¹ else 0
lemma plant_s(S:StepData c f)(w:LinkS S j): ∑ o:Site c,plant S o w=1:=by
 unfold plant; rw [← sum_filter]; let Z:=grove S (w 0); rw [show univ.filter _=Z from ?_,sum_const,nsmul_eq_mul]; exact mul_inv_cancel₀ (by exact_mod_cast (card_pos.mpr (grove_n S _)).ne')
 ext; simp; rfl -- tune
lemma plant_v : |plant S o w| ≤1:=by unfold plant; split; rw [abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (show 0 < _ from card_pos.mpr (grove_n S _))); simp
abbrev finW(o: Site c)(S:StepData c f)(x:ℝ)(j:ℕ): Finset (LinkS S j):= univ.filter fun w=>o∈grove S (w 0) ∧ CodeZ S x w
lemma latticeFieldEstimatesC(hx: CodeZ S x w)(hp:o∈grove S (w 0))(i:Fin (j+2)) : separation o (S.ratio.parent (w i).1) ≤ 1+i.val*(3*radiusB x):=by
 have he(j):S.ratio.parent (w j).1∈Next.SectorChange.points S (w j):=Set.mem_insert _ _
 induction i using Fin.induction with
 | zero=>
    simp only [Fin.val_zero,zero_mul,add_zero]; rw [← mem_coe,grove_x] at hp; rcases Set.mem_insert_iff.mp hp with h|h
    · rw [h]; simp
    rw [Set.mem_singleton_iff.mp h,separation_comm]; exact Work.E03.parent_step S _ _
 | succ i ih=> apply (separation_triangle o (S.ratio.parent (w i.castSucc).1) _).trans; apply (Nat.add_le_add ih (hx.2 i _ (he _) _ (he _))).trans; simp_rw [Fin.val_castSucc,Fin.val_succ,Nat.add_mul]; omega
lemma packed(o:Site c)(r:ℕ)(hr:1+(j+1)*(3*radiusB x) ≤ r) :(finW o S x j).card ≤ (Fintype.card Axis*S.patch.L.val^4*(r+r+1)^4)^(j+2):=by
 let V:Finset (Bond f):= univ.filter (fun i=> separation o (S.ratio.parent i.1) ≤ r); let I:= finW o S x j
 have hh(w)(u:w∈I) (i:Fin (j+2)): (w:LinkS S j) i∈ V:= mem_filter.mpr ⟨mem_univ _, (latticeFieldEstimatesC ((mem_filter.mp ‹w∈I›).2.2) ((mem_filter.mp ‹w∈I›).2.1) i).trans ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (show i.val ≤ j+1 from by omega)) _).trans hr)⟩ -- binder syntax
 let Y(w:I):Fin (j+2)→V:=fun i=> ⟨w.val i,hh w.val w.property i⟩; have hy: Injective Y:= fun _ _ h=> Subtype.ext (funext fun i=>congrArg Subtype.val (congrFun h i))
 have h: I.card ≤ V.card^(j+2):= by simpa [LinkS,Run] using Fintype.card_le_of_injective _ hy
 apply h.trans; apply pow_le_pow_left'; exact le_trans (fine_count V (pavilion r o) (fun i h=> (theatre ..).mpr ((mem_filter.mp h).2))) (Nat.mul_le_mul_left _ ((Corona.halo_size ({o}:Support c) r).trans_eq (by simp))) -- tune
variable(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(M:Monk G S)
def beds (r:ℕ)(i:Site c):ℝ:=∑ w:LinkS S r, plant S i w*pave T x q d l w M
def Quill (i:Site c):ℝ:=∑ r∈Finset.range 3,beds T x q d l M r i
lemma bedsX (r:ℕ)(i:Site c)(p:Ready T x)(ht:1000 ≤radiusB x): beds T x q d l M r i=∑ w∈finW i S x r, plant S i w*pave T x q d l w M:=by
 unfold finW; rw [sum_filter]; unfold beds; refine sum_congr rfl fun w _=>?_ ; split
 next=>rfl
 next h=>by_cases hv:i∈grove S (w 0); rw [hideS T x q d l _ p ht (fun t=>h ⟨hv,t⟩),mul_zero]; simp [plant,hv]
lemma baseZ(r:ℕ) : ∑ i:Site c,beds T x q d l M r i=∑ v:Run (M.zoo x) (r+1),pes T x q d l M v:=by
 unfold beds; rw [sum_comm]; simp_rw [← sum_mul,plant_s,one_mul]; refine Eq.symm (Finset.sum_of_injOn stave stave_inj.injOn (fun v p=> mem_univ _) ?_ (fun v _=> (paved T x q d l v).symm)); rintro w h hv; apply dif_neg (fun h=> hv ?_); obtain ⟨v,hv⟩:=h; exact ⟨v,mem_univ _,hv⟩
lemma tallZ (k:Tab S)(t s A C D E v:ℝ)(u:Mast G c)(h:Medal T x A C D E v n l t k.1 k.2 u) : let Y:=satU G t u; ∑ i, Quill T x q d l (bunk S k Y) i=Souk.tallyX T x k.1 k.2 q d l Y:=by
 intro Y; unfold Quill; rw [sum_comm]; simp_rw [baseZ]; unfold Souk.tallyX pes; simp_rw [Finset.sum_add_distrib,←mul_sum]; let V:=bunk S k Y
 congr 1
 · congr 1
   · let A:= V.park; apply congrArg (-(1/2:ℝ)*·); exact sum_congr rfl fun i _=> (bS h.headX i).symm -- signature k p
   apply congrArg ((1/2:ℝ)*·); exact sum_congr rfl fun i _=>(bS h.stepX i).symm
 apply sum_congr rfl; intro i hI; rw [show (bunk S k Y).bush x= (1: LinkArray G (Frozen (bareStores S) x k.1)) from rfl]; exact (bS (h.spend q d) i).symm
end YM.CF.Tarn
