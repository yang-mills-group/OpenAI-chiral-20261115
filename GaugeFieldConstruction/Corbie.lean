import GaugeFieldConstruction.Axe
import GaugeFieldConstruction.Rain
import GaugeFieldConstruction.Jupiter
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Branch Tenant Drapes Rill Sault Levier Thera Urn Nacre Salt Laic Moire
open XGarden Jet Broc
variable {N:Side}{a b e d c v K:ℝ}{H: Elm N Unit e a d} {V:Support (More N)}
namespace SliceRoof
abbrev coinH(K b:ℝ):Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](n:Side)(f:E→Bkg (More n))(x),TransK 7 f x K→ Allows 7 (Tulip.profile ∘ f) x b
lemma earns_q (p:0≤K):∃ b:ℝ,0≤b ∧ coinH K b:=by obtain ⟨Y,q,H⟩:=Proa.profile_X 7 K p; exact ⟨Y,q,fun _ _ _ _ _ _ p=>H _ _ p⟩
abbrev releaseQ (A:Elm N Unit e a d) (S:Support (More N)) (U:Pane N):Op (Single N):= if h:Tulip.profile U ∈ Openc (More N) e then A.F S () ⟨Tulip.profile U,h⟩ else 0
lemma release_L (A:Elm N Unit e a d)(S:Support (More N))(x:Pane N)(h:x∈ Clode N e) (p:0<e):
 ∀ u:Guard x e, releaseQ A S x=ivory A p x u S:=fun u=> dif_pos (lantern x u p) -- generic remove h
lemma re_L (A:Elm N Unit e a d)(S:Support (More N))(x: Pane N)(u:Guard x e)(p:0<e):releaseQ A S x=ivory A p x u S:=dif_pos (lantern x u p)
private lemma bound_H (t:Pane N)(p:t∈ Clode N e):Guard t e:= interior_subset (s:={x:Pane N|Guard x e}) p
abbrev DeskK (P:ℝ) (e:ℝ):ℝ:= composeCost 7 ((1+2^7/e)^7) P
lemma toll_Baro (A:Elm N Unit e a d)(S:Support (More N))(p:coinH K b)(he:0<e)(hv:0≤b)(i j: Single N): Baro K e 7 S (fun x=> releaseQ A S x i j) (DeskK b e * (A.W S i j)) ∧ ( (A.W S i j)≠0 → Grove (terr _) S∧ aptK i∈ S ∧ aptK j∈ S):=by
 let H:=A.coat S|>.1 (); let L:= H.expo i j; let f(x):=A.F S () x i j; let V:=DeskK b e
 have ht(x:Pane N)(p:x∈ Clode N e): releaseQ A S x i j=f (light e x he (bound_H x p)):=by rw [re_L A S x (bound_H x p) he]
 refine ⟨⟨mul_nonneg (by unfold DeskK composeCost; positivity) L.positive, ?_, fun x px y py hx=> ?_, fun E _ _ _ F x g w=> ?_⟩,fun w=>L.triggered w⟩
 · apply continuousOn_iff_continuous_restrict.mpr; have hp:Continuous (fun i: ↥(Clode N e)=>light e i.val he (bound_H i.val i.property)):= (Dial.profile_c.comp continuous_subtype_val).subtype_mk _; exact (L.connected.comp hp).congr (fun x=> (ht _ x.property).symm)
 · dsimp only; rw [ht _ px,ht _ py]
   let P:=light e x he (bound_H _ px); let Q:=light e y he (bound_H _ py); apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; refine (L.variation P Q).trans_eq ?_; rw [show (forum _ e).eval S P Q=0 from ?_,mul_zero]
   change Tulip.fare _ _ _/|e|=_; rw [show Tulip.fare S (Tulip.profile x) (Tulip.profile y)=0 from ?_, zero_div]; unfold Tulip.fare; apply sum_eq_zero; intro i p
   have hh:=hx i (mem_filter.mp p).2.1 (mem_filter.mp p).2.2; rw [show Tulip.profile x i=Tulip.profile y i from funext fun k=>by unfold Tulip.profile; rw [hh],sub_self,norm_zero]
 let U:=Tulip.profile ∘ F; have hU := p E N F x w; have l:Looks _ f:= H.fuel i j; have hh: Metric.ball (U x) e ⊆ Openc (More N) e:= fun r hr=>⟨F x, bound_H _ g, mem_ball_iff_norm.mp hr⟩
 let s:=A.W S i j; have hx:Allows 7 (equalizer f ∘ U) x (composeCost 7 (s*((1+2^7/e)^7)) b):=(allows_looks l L.connected hh he 7 L.bounded).comp hU; refine (hx.mono (le_of_eq (by unfold DeskK composeCost s; ring))).germ ?_
 filter_upwards [(cliff_n w).eventually (isOpen_interior.mem_nhds g)] with i h; change equalizer f (U i)=releaseQ _ _ _ _ _; rw [ht _ h]; exact dif_pos (light e _ he (bound_H (F i) h)).property
lemma norm_enter (S:Support (More N))(U:Pane N)(p:Guard U e)(g:0<e)(z:Skye.Seat N→ SU.E): releaseQ H S (gauge z U)=twist (tradew N z) (releaseQ H S U):=by rw [re_L _ _ _ (p.cov z) g,re_L _ _ _ p g]; exact seat_rent ..
-- Dollar coherence on true poses.
lemma backG (P:groupShape H) (t:Sweep N)(S:Support (More N))(V:Pane N)(p:Guard V e)(g:0<e): releaseQ H (actY t S) (flashA t V)= realR t true (releaseQ H S V):=by
 have hp: Guard (flashA t V) e:=keepC (xtra t.charge) (castX t) _ e p
 rw [re_L _ _ _ hp g,re_L _ _ _ p g]; let Q:=light e V g p; have h:= P t () S V Q rfl; rw [show Sour.fog t e Q=light e _ g hp from Subtype.ext (Sour.real_box t e V Q rfl)] at h; exact h
lemma releaseHerm (P:pure_Rim H)(x: Pane N)(S:Support (More N))(p:Guard x e)(g:0<e):star (releaseQ H S x)=releaseQ H S x:=by rw [re_L _ _ _ p g]; exact P S (light e _ g p) x p rfl
lemma subtractWind (P:pure_Rim H)(x:Pane N)(S:Support (More N))(p: Guard x e)(g:0<e)(q:groupShape H)(t:Sweep N):
 releaseQ H (actY t S) (flashA t x)= if detX t.s then -ech t (releaseQ H S x) else ech t (releaseQ H S x):=by
 rw [backG q t S x p g]; let F:= releaseQ H S x; have hu:star F=F:=releaseHerm P x S p g; have he:star (ech t F)=ech t F:=by unfold ech; simp only [singT,← map_star,← win_s,hu]
 simp only [realR,ite_true,bolt,hitL,Thera.jazz]; change (if detX t.s then -star (ech t F) else ech t F)=_; rw [he]
end SliceRoof
end YM.CF.Sour
end
