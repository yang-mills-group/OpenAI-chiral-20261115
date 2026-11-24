import YM.CF.Yaw.Park
import YM.CF.Rue.Poly
import YM.CF.Rill.Tilt
import YM.CF.Rill.Vent
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Eire Jet Scroll Rill.TasteZ
local notation "G_"=> SU.group
section
variable {n m:Side}
local notation "F_"=> Domain n m
lemma touchK(S:Support n): inspected S ⊆ Lattice.halo 12 S:=by
 intro i p; rcases mem_union.mp p with p|p; exact halo_subset _ _ p -- tune
 obtain ⟨j,g,t⟩:=mem_biUnion.mp p; split at t; simp at t
 next p=> obtain ⟨a,w,k⟩:=Finset.not_disjoint_iff.mp p; exact halo_spec.mpr ⟨a,w,terrain k t⟩
end
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B))(φ:S.ratio=Rush.ratio G)
local notation "c₁"=> Domain N B
local notation "c₂"=> Domain P B
local notation "E_"=> StepData (Domain N B) (Domain P B)
variable {r l n k k' m:ℕ}(x d e s s' K τ B₀:ℝ)(q h:Chi)
variable{S} (U:Loom (mid N B))(V:Loom (mid P B))(T:Tube SU.group S)
variable {e s s' d x K τ B₀} {t v b b' a β e0 v':ℝ}
local notation "B'"=> radiusB x
local notation "k_"=> ((l+90)*radiusB x)
local notation "bay"=> Stilo.bay
variable (M:Monk SU.group S)(J: List (Kite S r))(p:M.key=cook S J.toFinset)(A:Ride S) 
local notation "F"=> erosion ((l+70)*radiusB x) (bay A)
local notation "Y"=> (((M.V,M.U,β,M.z):HomeL (Domain N B) (Domain P B)))
local notation "D"=> cusp M.key x M.V
variable {J':Teller SU.group}
variable (hp:30*radiusB x ≤ r)(hx:1000≤radiusB x)(vK:∀ i∈ J.toFinset,Lattice.halo ((l+90)*radiusB x) (Eire.frameP S i)⊆Stilo.bay A) -- beware notation bay in variable
variable (f:Stilo.bay A ∩ RG.flags (temp x) M.V=M.key.flags)
local notation "γ"=> Atala.Bell
local notation "R"=> Rill.MarkP
-- Financing certificate on all physical extensions. No synthetic masks.
include p hp hx vK
lemma compK : M.key.dome r ⊆ erosion ((l+70)*radiusB x) (bay A):=way_g S J.toFinset F (fun i v=> (frame_s ..).trans ((halo_subset _ _).trans ((skyC (r:=r) S A).ports _ (vK i v)))) p _ le_rfl -- tune
include f
lemma norm_v : inspected M.key.flags ⊆ bay A:=by
 apply (touchK M.key.flags).trans; let X:= bay A; exact (chilling (by omega : 12 ≤ r) (show M.key.flags ⊆ M.key.place from subset_union_right)).trans ((compK M J p A hp hx vK).trans (Subset.trans (halo_subset _ _) (erosion_c ..))) -- param x
lemma earn_v {h:0 < β} (p':J'.Funds S T)(t:l≤18)(he:0< temp x)(hy:0 < d)(q0:2*d<firstRadius SU.group) (hK:0 < β)(X:MossX n l x (ray M.key x M.V) M.park T M.V M.k K d (fiery SU.group x S.patch.L) q)(u:a<s)(u':v<s')(vK':0<v)(Hv: Atala.Bell S (trot S M (ray M.key x M.V)) x T q d l β a v):
 R M F x s s' Y l n T q d:=by
 have hy':= star_p _ (show M.key.flags⊆ flags (temp x) M.V from (show M.key.flags ⊆ Stilo.bay A∩RG.flags (temp x) M.V from f.ge).trans inter_subset_right) f (norm_v M J p A hp hx vK f)
 exact sapien Y (fun i _ _=>rfl) f.le hy' he hx p' t hy q0 X hK u u' vK' (erosion_c ..) Hv
section lit
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (I:E→L[ℝ] Directions SU.group (Domain N B))(Z:Support (Domain P B))(X': Lattice.halo ((l+90)*radiusB x) (hatY S Z)⊆Stilo.bay A)
local notation "Nc"=> ({M with key:=cusp M.key x M.V}:Monk SU.group S)
local notation "r_"=> (monkD M ∘ (fun i=>Rill.TasteZ.hover M.V I i x Y))
local notation "k₁"=>[(M.key)]
variable (z':Ids (mid P B))(z:Ids (mid N B)) (U': E→ Rill.Arch G e)
include U V φ f p hp hx vK z' z U' X'
lemma herd_z {A_f K1:ℝ}(RP:Rill.MarkP M F x s s' Y l n T q d)
 (pu:Roof (mid N B) s t k' U)(pv:Roof (mid P B) s v k V)(p0:0<fiery SU.group x S.patch.L)(p1:fiery SU.group x S.patch.L < s)(p2:k+k'≤radiusB x)(p3:s' <firstRadius SU.group)(p4:looseV x M r m (M.sent x T q d l β))
 (vt:Ready T x)(g:∀ i, Agrees (halo 12 (halo (4*radiusB x) M.key.flags)) M.V ((r_ i).V))(t':1≤ τ)(u0:1 ≤ K)(hK:‖I‖ ≤ K)(hp':Rill.Cash (4*S.ratio.count.val+13) (A_f*K^n) τ ≤ e0) (vW: Rill.Wind e0 (·*·) n τ)(v':Rill.Wind e0 (fun i _=>i⁻¹) n τ)(vz:Rill.Wind e0 (knit h s') n τ)
 (ξ:∀ i:Bond (Domain N B),Tender (fun v=> Vmove x M.V v i) 0 A_f n)(ζ:∀ i:Bond (Domain P B), Tender (fun v=>((Nc).atop v x).sent x T q d l β i) 0 A_f n)
 (c:∀ i, Eire.Clan G S (T:=T) φ z z' (r_ i) U V q h l x d s' β (U' i)) (hX: K1 ≥ Rill.Cash (4*S.ratio.count.val+13) (A_f*K^n) τ)(hu:A_f*K^n ≤ K1): BeamV G e U' n Z K1 0:=by
 let S':=hatY S Z; let Z':= Lattice.halo 2 S'; have he:halo (k+k'+30) Z' ⊆ F:= (icing (by omega : k+k'+30+2 ≤ 20* B')).trans ((skyC (r:=r) S A).ports _ X'); have ht:TasteZ Y M U V F Z' x d s s' v t T q n r m l k k':=⟨RP,pu,pv,p0,p1,p2,p3,hx,((chilling (by omega : 5*radiusB x≤ r) (Subset.refl _)).trans (compK M J p A hp hx vK)),he,p4⟩
 have hv:=pay_r (N:=Nc) ht I (S:=S) φ (φ ▸ M.park) h t' vW v' vz ((chilling le_rfl ((halo_subset ..).trans he)).trans (erosion_c ..)) (show Beat (monkD M Y) Nc (bay A) from (cusp_d M.key (M:=M) rfl f M.V).toBeat) vt hK u0 hp' ξ ζ z z' g
 have hk(i): (U' i).val=_:= c i
 refine ⟨fun i p=>?_,fun i p=>?_⟩ -- hk comp
 ·
   have hx:S.ratio.parent i.1∈ hatY S Z:=mem_image_of_mem S.ratio.parent (p (by simp)); simp_rw [hk]; exact ⟨(hv.2.2 i (Subset.trans (chilling one_le_two (singleton_subset_iff.mpr hx)) (Subset.refl _))).bag hX,(hv.2.1 i (halo_subset _ _ hx)).bag hu⟩ -- casts
 have hK: i.1∈ cloudG G Z:= p (by simp); have hQ:i.1∈ hatY S Z:=by have ht:=(mem_filter.mp hK).2; rw [←φ] at ht; exact ((Ratio.embed_parent S.ratio i.1) ▸ mem_image_of_mem S.ratio.parent ht)
 simp_rw [hk]; exact (hv.1 i (halo_subset _ _ hQ)).bag hu
end lit
end YM.CF.Yaw
