import YM.CF.Lor.Theme
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
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
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open BoreP Fief rates Nacre Font Braid Rel Souk Girt
variable{k l:ℕ}
variable(Q:Patch)(k l:ℕ)(a C b s e:ℝ)(q:Chi)
local notation "κ"=> Jet.composeCost
lemma bodyZ (v:ℝ)(h:0<v)(hp:0<a)(hz:0<b)(ht:0<s)(he:s< firstRadius SU.group):∃ w:ℝ,0<w∧∀ᶠ x:ℝ in atTop,∀{m X B:Side}{T:Roam m X B}(F:Tube G₅ T)(Z: Monk G₅ T),T.patch=Q→ 40<(Domain m B).val →flags (temp x) Z.V⊆ Z.key.flags→ Ready F x→∀ β∈Set.Icc (y G₅ Q.L x/2) (2*y G₅ Q.L x),∀ L:ℝ,0<L→L≤ v*Scales.p G₅ Q.L x→‖Z.z‖≤L→∀ d:ℝ,MossX (k+2) l x Z.key Z.park F Z.V Z.k b d (fiery G₅ x Q.L) q→∀ {G:Ratio (mid m B) (mid X B)}(N: Scree.Loom (mid m B))(M:Scree.Loom (mid X B))(q':Chi)(H:T.ratio=ratio G)(J:Ids (mid m B))(P:Ids (mid X B))(R:Monk G₅ T→ Rent0 G e)(η:ℝ)(j j':ℕ), (∀ y,(R y).val= YF G N M q' s (H ▸ y.park) (y.V,J) (y.sent x F q d l β,P)) → Roof (mid m B) a η j N →Roof (mid X B) a η j' M→ j+j' ≤radiusB x →η<e →(∀ y,JointB G (R y).val η)→∀ i:Site (Domain m B),i∉ Z.key.dome (25*radiusB x) →(∀ C:ℝ,1<C→ Area (k:=k) (x:=x) G Z R i C (rumP Q.L 1 k 1 w L x) (2*rumP Q.L 1 k 2 w L x))∧(∀ᶠ t in 𝓝 0,let A:=Cay.rough (Z.atop t x) 0; Bride G F x d q l A (R A) β (radiusB x+1) i):=by
 obtain ⟨w,u,hW⟩:= rubies (k+2) l b v Q hz h; refine ⟨w,u,?_⟩
 filter_upwards [Atala.threshold Q (k+2) l (a/2) (s/2) b v (half_pos hp) (half_pos ht) hz h,hW, (year G₅ Q.L).eventually_gt_atTop 0, Work.E01.radiusB_tendsto.eventually_ge_atTop 1000] with x z y' tR hR m X B T F Z hx hq hβ hl β zB L hL hZ hy d p G N M q' H J P R η j j' k0 hM hN η' he' hx' i k'
 let K:=Directions G₅ (Domain m B); have hp':=y' T F Z hx β zB L hL hZ hy q d p; have htS:0<coupling β:=coupling_pos hp'.beta; let Q'(p:ℝ):=p*w/(coupling β*L); let T':=coupling β*L/w; have hT:0<T':=by unfold T'; positivity
 let X(x'):Monk G₅ T:= mixA x Z β w L x'
 have Ht(y:ℝ)(hp:|y|≤T'): Bell T (X (0,y)) x F q d l β (a/2) (s/2):=by
    let Y:= X (0,y); have ht : |Q' y| ≤ 1:=by unfold Q'; rw [abs_div,abs_mul,abs_of_nonneg u.le,abs_of_pos (mul_pos htS hL), div_le_one (mul_pos htS hL)]; exact (le_div_iff₀ u).mp hp
    have he:Y.V=Z.V:=by change (Z.atop 0 x).V=_; simp [Monk.atop,Vmove]
    apply z _ _ _ hx (by rw [he]; exact hβ) hq _ zB ((le_trans ?_ hy).trans hZ) d _ (by rw [he]; exact p)
    change ‖Q' y • Z.z‖ ≤_; rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) ht
 constructor
 · intro C g U Y _w t hu rwT W heW -- read $x needs binder v rename
   obtain ⟨f,k'⟩:= rubyK G F x d q l Z β a η L k q' J P s N M R H k0 hM hN η' he' hR hl hp' he hL u g hx' (fun y d=>⟨a/2,s/2,half_lt_self hp,half_pos ht,half_lt_self ht,Ht y d⟩) U Y i heW rwT _w (mem_filter.mp t).2 hu k'
   let V(U):=κ k U 1; have hu:T' ≤ 2*Scales.g SU.group Q.L x*L/w:=(div_le_div_iff_of_pos_right u).mpr (mul_le_mul_of_nonneg_right (Esti.compare_v SU.group Q.L x zB tR).1 hL.le)
   have hkz:0 ≤ V W:=nonneg_of_mul_nonneg_right (show 0≤2^k*T'*(V W) from f.nonneg) (by positivity) -- tune from f.nonneg
   have he(j:ℕ): (2^k*T')^j*κ k W 1≤rumP Q.L 1 k j w L x * W:=by
       refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0≤2^k*T') (mul_le_mul_of_nonneg_left hu (by positivity)) _) hkz).trans_eq (by unfold V rumP Jet.composeCost; ring)
   exact ⟨f.mono (by simpa only [pow_one] using he 1), k'.mono (by rw [mul_assoc (2:ℝ)]; exact mul_le_mul_of_nonneg_left (he 2) (by norm_num))⟩
 -- use seeX on mix even P' open
 have hP:∀ᶠ y in 𝓝 ((0,0):K×ℝ), Bride G F x d q l (X y) (R (X y)) β (radiusB x+1) i:=by
    let W(y:K×ℝ):= X y; have hp:|(0:ℝ)| ≤ T':=(abs_zero.le.trans hT.le); obtain ⟨f,g⟩:= hp'.pureS _ hp
    refine seeX G F x d q l β W ((0,0):K×ℝ) _ _ a s η N hM M hN H q' J P _ (fun i=>k0 _) (half_pos ht) (half_lt_self ‹0<a›) (half_lt_self ht) he η' hl hR ?_ ?_ (Eventually.of_forall fun _=>rfl) (Ht _ hp) i k'
    · exact continuousAt_pi.mpr (fun i=>(SU.fund_cont.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (g i).smooth.continuousAt)
    apply continuousAt_pi.mpr; intro j'; apply (SU.fund_cont.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
    have hx(y:K×ℝ): repine F x Z d l q w L y j' = (W y).sent x F q d l β j':=by rcases y with ⟨u',z⟩; have ht:= Cloak.belt F x Z d l q w L β (z*w/(coupling β*L)) u' u.ne' hL.ne'; rw [show z*w/(coupling β*L)*coupling β*L/w=z by field_simp] at ht; exact congrFun ht _
    exact ((f j').smooth.continuousAt).congr (Eventually.of_forall fun i=> congrArg SU.fund (hx i)) -- orientation
 have ht := ((show ContinuousAt (fun i:K=>(i,(0:ℝ))) 0 from by fun_prop).eventually hP); filter_upwards [ht] with i u; simp only [X,mixA, zero_mul,zero_div,zero_smul] at u; exact u
end YM.CF.Lor
