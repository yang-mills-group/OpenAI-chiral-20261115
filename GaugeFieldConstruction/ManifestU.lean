import GaugeFieldConstruction.RankSail
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
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
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d e:ℕ}{k:Side}
variable (n x k)
open TableF Taxi
abbrev knob(V:Pane k):Pane n:= snake (n:=n) x (onC k V)
lemma knob_E (U:Pane k)(e:Bond (More n)): knob n x k U e= U (wrap (More k) (prospect x e.1),e.2):= Lifted.onC_spec k U (prospect x e.1,e.2)
def knapp : tangD k→L[ℝ] tangD n:= ContinuousLinearMap.pi fun i:Bond (More n)=> ContinuousLinearMap.proj (wrap (More k) (prospect x i.1),i.2)
lemma Kturn(J:ℝ)(V:Pane k)(Q:tangD k) : knob n x k (Shield.solo J V Q)=Shield.solo J (knob n x k V) (knapp n x k Q):=by funext i; rw [knob_E]; unfold Shield.solo RG.increment; rw [knob_E]; rfl -- tune
lemma k_pitch {p:ℝ}(w:d+6<n.val)(u:d+6<k.val)(V:Pane k)(g:pingS p (knotX x d k) V): pingS p (knotX x d n) (knob n x k V):= (ping_view x d w (onC k V)).1 ((ping_W x d u V).2 g)
lemma Kink : ‖knapp n x k‖ ≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro a; exact norm_le_pi_norm i (wrap (More k) (prospect x a.1),a.2)
lemma MicroK(p:BudgetPoint)(w:d+6<n.val)(u:d+6<k.val)(V:Lit n){c:ℝ}(R:Micro p (knotX x d n) V c):Micro p (knotX x d k) (V∘knob n x k) c:=by
 refine ⟨R.1,Env.along R.2.1 (((snake_c x).comp (on_cont k)).measurable),fun U W z=>R.2.2.1 _ _ (cart_S (by omega) (Lifted.on_agree k (?_))),fun W z=> ?_⟩
 · rw [cart_T (show d<k.val by omega)]; exact z
 replace R:= R.2.2.2 _ (k_pitch n x k w u W z); let L:=knapp n x k
 exact (comps L (x:=0) (map_zero L|>.symm ▸ R) (Kink n x k)).germ (Eventually.of_forall fun i=> congrArg V (Kturn n x k _ W i).symm)
variable {n x k}
lemma pvi_U (L:Paper n)(w:d+1<n.val)(U:∀ i, LocalOn (knotX x d n) (L i))(i:jungle x d): LocalOn (cartO x d) (Pvi n x d L i):= fun J K p=>congrArg (feeV n i * ·) (U (hereV n i) _ _ (cart_S w p))
-- Press statement for all hosts but cost locus only on huge
lemma Tock_C {A:Paper n}{p:BudgetPoint}{c v:ℝ}(u:d+6 < n.val)(w:d+6 < k.val)(H:TrackD p (knotX x d n) v A c): TrackD p (knotX x d k) v (pR k (Pvi n x d A)) c:=by
 obtain ⟨Z,z,g⟩:=H; let V:= Pvi n x d A; let I:= jungle x d
 let f(i:I): Lit k:= fun X=> feeV k i * V i (onC k X)
 let W(i:I):= isolate (hereV k i) (f i); have he(i:I): Micro p (knotX x d k) (f i) (Z (hereV n i)):=by
    let a:= hereV n i; let L: Micro p (knotX x d k) (A a ∘ knob n x k) (Z a):= MicroK n x k _ u w _ (z a).1; have h0:=micro_ms (micro_ms L (feeV n i)) (feeV k i); rwa [feeV_n,feeV_n,one_mul,one_mul] at h0
 apply track_p (track_sum univ W (fun i=> papW k v (hereV k i)*Z (hereV n i)) (fun i _=> moorage _ (hereDom i (by omega)) _ (he i))); apply le_trans _ g; simp_rw [here_cost (n:=k) _ _ n]; let S:= (univ:Finset I).image (hereV n);
 refine Eq.trans_le ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun j _ _=> mul_nonneg (papW_v _) (z j).1.1)); symm
 apply sum_image; exact fun a ha b hb e=>hereI (x:=x) (d:=d) (by omega) e
lemma pR_morn {p:BudgetPoint}{c v:ℝ}(u:d+6<n.val)(A:Paper n)(H:TrackD p (knotX x d n) v A c):pR n (Pvi n x d A)=A:=pR_S n A (by omega) fun i=> (H.choose_spec.1 i).2
lemma pR_smir {p:BudgetPoint}{c v:ℝ}(u:d+6<n.val)(A:Paper n)(H:TrackD p (knotX x d n) v A c)(l:portable A)(k:Side):portable (pR k (Pvi n x d A)):=by refine pR_G (n:=n) (by omega) _ (pvi_U A (by omega) (fun i=> (H.choose_spec.1 i).1.2.2.1)) ?_ k; rw [pR_morn u A H]; exact l
end ArtCart
end MastTin
end YM.CF.XGarden
end
