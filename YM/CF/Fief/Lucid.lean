import YM.CF.Fief.Gilt
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Jet Push.AbsoluteSums
local notation "G₅"=> SU.group
variable {c f n N X B:Side}{S:StepData (Domain N B) (Domain X B)}{G:Ratio (mid N B) (mid X B)}{a b e C H D:ℝ}{k l j:ℕ}
-- use rent branch exposures.B.S mat paid graph terms. charge veil.Path.R all. cost h
open Branch Corona
variable (G:Ratio c f)(Z:Support f)(k l:ℕ)
lemma surgeK (p:Grove (terr _) Z)(u:0<k) : G.count.val*k* coverNumber k (halo (l*k) (Z.image G.parent))≤ (2*Z.card+G.count.val*k)* ((l+3)+(l+3)+1)^4:=by
 obtain ⟨M,hM,R,h,F⟩:= ring_path (D:=Z) 1 (fun i t j u=> rooted p i t j u)
 obtain ⟨D,hD,H,h'⟩:= fuel G R M h k u
 let Y:= halo (l*k) (Z.image G.parent); have hp:covers ((l+2)*k) Y D:=by
    refine ⟨fun i t=> ?_, Corona.ship_halo _ (fun i hi j hj=> Relation.ReflTransGen.mono (fun x y (hX:Touch D (2*k) x y)=> ⟨hX.1,hX.2.1,hX.2.2.trans (by simp only [Nat.add_mul]; omega)⟩) i j (hD _ hi _ hj))⟩ -- tune
    obtain ⟨a,hp,z⟩:= halo_spec.mp (show i∈ Y from t); obtain ⟨b,u,rfl⟩:=mem_image.mp hp; obtain ⟨j,t,hM⟩:= F b u; obtain ⟨s,m,v⟩:=halo_spec.mp (h' _ t); rw [hM] at v; apply halo_spec.mpr; exact ⟨s,m,(separation_triangle _ (G.parent b) _).trans (by simp only [Nat.add_mul]; omega)⟩
 refine (Nat.mul_le_mul_left _ (tiling u hp)).trans ?_; rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (H.trans (by omega)) -- m≤Z.card*2
section weights
variable(h:0<k)(σ ε W:ℝ)(hp:0<σ)(hc:0 ≤ ε)
def tileN(l:ℕ) := ((l+3)+(l+3)+1)^4
variable {κ:ℝ}{o:Site c}{W:Support f→ℝ}
include h hp hc
lemma fen (g: 2*ε*(tileN l) ≤ σ/2*(G.count.val:ℝ)*k)(u:Grove (terr f) Z): Real.exp ( ε* coverNumber k (halo (l*k) (Z.image G.parent)))≤ Real.exp (ε*tileN l)*Branch.rent (σ/2) Z:=by
 unfold Branch.rent; rw [← Real.exp_add]; apply Real.exp_monotone
 have hK:0<(k:ℝ):=by exact_mod_cast h
 have he: (G.count.val*k:ℝ)*coverNumber k (halo (l*k) (Z.image G.parent)) ≤ (2*Z.card+G.count.val*k:ℝ)*(tileN l:ℝ):= by exact_mod_cast surgeK G Z k l u h
 apply le_of_mul_le_mul_right _ (mul_pos (Nat.cast_pos.mpr (show 0<G.count.val from G.count.property)) hK)
 nlinarith only [mul_le_mul_of_nonneg_right he hc,mul_le_mul_of_nonneg_left g (show 0 ≤ (Z.card:ℝ) by positivity)]
include hp
lemma venture (g:2*ε*tileN l≤σ/2*(G.count.val:ℝ)*k)(v:∀ S,0 ≤ W S)(p:∀ S,W S≠0 → Grove (terr f) S)(D:Finset (Support f))(m:ℕ)(q:∀ i∈D,m ≤ i.card) (Q:∀ i:Site f,hitE σ W i≤ κ) (hq:0≤κ)(z:Site c): (∑ S∈ D with z∈ halo (l*k) (Finset.image G.parent S), W S* Real.exp (ε*coverNumber k (halo (l*k) (Finset.image G.parent S))))≤ ((l*k+l*k+1)^4*G.count.val^4:ℕ)* (tollE σ m*(Real.exp (ε*tileN l)*κ)) :=by
 let C:=tollE σ m; let V:= Real.exp (ε*tileN l); have hm:0<C:=Real.exp_pos _; have hV:0<V:=Real.exp_pos _; let P:= D.filter fun S=> z∈halo (l*k) (Finset.image G.parent S); let T:= (univ:Finset (Site f)).filter fun i=>G.parent i∈halo (l*k) {z}
 let Y(S):=Branch.rent σ S* W S; have hh(S):0≤Y S:=mul_nonneg (Real.exp_pos _).le (v _)
 have he(S:Support f)(h:S∈P): W S*Real.exp (ε*coverNumber k (halo (l*k) (Finset.image G.parent S)))≤ C*V*Y S:=by
    by_cases ht:W S=0; · rw [ht,zero_mul]; exact mul_nonneg (mul_pos hm hV).le (hh _)
    apply le_trans (mul_le_mul_of_nonneg_left (fen G S k l ‹0<k› σ ε hp hc g (p _ ht)) (v _)); have hx:(σ/2)* (S.card:ℝ) ≤ -(σ/2)*m+σ*S.card:=by
       have he:(m:ℝ)≤ S.card:=by exact_mod_cast q _ (mem_filter.mp h).1
       nlinarith
    have hp:(Branch.rent (σ/2) S)≤ C*Branch.rent σ S:=by unfold Branch.rent C tollE; rw [←Real.exp_add]; exact Real.exp_le_exp.mpr hx
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hV.le) (v _)).trans_eq (by unfold Y; ring)
 have hX : ∑ i∈P,Y i≤ T.card*κ:=by
    let K(o)(S):= if o∈S then Y S else 0; have ht(o:Site f):∑ i∈P,K o i≤κ:=by
       unfold K; apply le_trans _ (Q o); rw [←sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun i v=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp v).2⟩) fun z x _=> hh z
    calc
     _ ≤ ∑ i∈P,∑ j∈T,K j i:= sum_le_sum (fun X h=>by
        obtain ⟨g,v,y⟩:= halo_spec.mp (show z∈Lattice.halo (l*k) (Finset.image G.parent X) from (mem_filter.mp h).2); obtain ⟨i,kX,rfl⟩:=mem_image.mp v; have hp: i∈T:=mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨z,mem_singleton_self _,(separation_comm ..).le.trans y⟩⟩; refine ((if_pos kX : K i X=_).symm.le).trans (single_le_sum (f:=fun j=>K j X) (fun i _=>?_) hp); unfold K; split; exact hh _; exact le_rfl)
     _ ≤ _:=by rw [sum_comm]; exact (sum_le_sum (fun i (_:i∈T)=> ht i)).trans_eq (by rw [sum_const,nsmul_eq_mul])
 change ∑ i∈P,_ ≤ _; refine (sum_le_sum (fun i t=>he i t)).trans ?_; rw [←mul_sum]; have ht : T.card≤(l*k+l*k+1)^4*G.count.val^4:= le_trans (Footprint.crowd G _) (Nat.mul_le_mul_right _ ((Corona.halo_size {z} (l*k)).trans (by simp)))
 exact (mul_le_mul_of_nonneg_left (hX.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) hq)) (mul_pos hm hV).le).trans_eq (by unfold C V; ring)
end weights
end YM.CF.Fief
