import SatinThinCanvases
import SatinThinRenew
import SatinThinWarp
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis.Head.Etch
variable (i k:ℕ){f r v d:ℕ}{a c:ℝ}
local notation "L"=> P.R.L
local notation "Δ"=> P.block
local notation "Ω" j:max=> side Y i j
local notation "Gξ" j:max=> Vale.apt (Y.ir i) P.block P.R.L j
local notation "w" => reserve P ℓ
variable (a':Axis)(s:ℤ)
def highTurn(P:Preparation)(f v:ℕ)(s:ℤ):ℤ:= (P.R.L.val:ℤ)^(v-f)*s
local notation "Xτ" j:max=> highTurn P f j s
lemma high_turn_start : highTurn P f f s=s:=by simp [highTurn]
lemma high_turn_succ (h: f ≤ v): highTurn P f (v+1) s=(L).val* highTurn P f v s:=by rw [highTurn,Nat.succ_sub h,pow_succ',highTurn,mul_assoc]
lemma high_turn_toll (h: f ≤r)(u:r≤v): highTurn P r v (highTurn P f r s)=highTurn P f v s:=by induction u with|refl=> exact high_turn_start _| step x ih=> rw [high_turn_succ _ (le_trans h x),high_turn_succ _ x,ih]
variable (x:Site (side Y i f))(p:f≤v)
lemma heel_swing : upRoot Y i p ((plane a' s).mills (side Y i f) x)=(plane a' (highTurn P f v s)).mills (side Y i v) (upRoot Y i p x):=by
 induction p with| refl=> simp only [upRoot,climbing_refl,high_turn_start]| step h ih=>
    apply node_inj (side Y i (_+1)); simp only [upRoot,climbing_succ _ _ h]; rw [mansion_L (Gξ _) P.R.odd_side]; unfold upRoot at ih; rw [ih,Shape.nodex,Shape.nodex,Shape.foldsT,mansion_L (Gξ _) P.R.odd_side,plane_broad,high_turn_succ _ h]; try rfl
include p in
lemma moving_band (t:node x ∈ band (Ω f) a' s d): node (upRoot Y i p x)∈band (Ω v) a' (Xτ v) d:=by
 induction p with|refl=> rwa [upRoot,climbing_refl,high_turn_start]| step h ih=>rw [upRoot,climbing_succ _ _ h,high_turn_succ _ h, mansion_L (Gξ _) P.R.odd_side]; exact band_anti a' _ (Nat.le_mul_of_pos_left _ (L).property) (band_root a' _ (Gξ _) _ ih)
variable (u:(Y.voyage i).kick≤k)(t:v≤Y.uv k)
include u t
lemma band_path (h: Mark (Ω f))(v': AtSupport false (band (Ω f) a' s (reserve P ℓ)) h): AtSupport false (band (Ω v) a' (highTurn P f v s) w) (convoy Y i k p h):=by
 induction p with| refl=> rwa [convoy,climbing_refl,high_turn_start]| step h ih=> rw [convoy,climbing_succ _ _ h,high_turn_succ _ h]; exact (weight Y i k ⟨u,t⟩ 0 (ih (by omega))).mono (margin_band _ _ (prepared P ℓ) (Gξ _) rfl P.R.coarse) -- ambiguity
omit u t
lemma band_true (a':Axis)(s:ℤ)(x:Site (Ω f))(h:w+12 ≤ d)(g:node x∈ band (Ω f) a' s d)(b:ℝ): AtSupport false (band (Ω f) a' s w) (routeTip Y i k b f x):=
 (route_owns Y i k f b x).mono (Subset.trans (Corona.halo_mono le_rfl (show {node x}⊆ band _ a' s d from Finset.singleton_subset_iff.mpr g)) (band_pad a' s h))
lemma cred_swing (b e:ℝ)(X:Pane n)(x:Site n): clothMark b e x (fling a' s n X)= clothMark b e ((plane a' s).mills n x) X:=by
 rw [fling_eq]; let z:Seat n:= wrap (More n) (2 • (s • step a')); let t:= Signed.mirror a'; let A:=affine t z (node x); let x':=(plane a' s).mills n x; have ht: node x'=A:=Shape.nodex ..
 have hu:=quad_move t (quad_mirror a') z (node x) X; rw [tax_mi a',one_mul] at hu
 change (if pingS e (Lattice.halo 10 {node x}) (pull t z X) then b/e^2*quadScore (node x) (pull t z X) else 0) = (if pingS e (Lattice.halo 10 {node x'}) X then b/e^2*quadScore (node x') X else 0); rw [ping_commutes,halo_plan,ht,hu]
lemma route_swing (q:ℝ) : routeTip Y i k q f ((plane a' s).mills (Ω f) x)= reflMark a' s (routeTip Y i k q f x):=by
 funext U; unfold routeTip turfMark reflMark; rw [Pi.smul_apply,Pi.smul_apply,theta_smul,theta_smul,theta_one,Complex.star_def,Complex.conj_ofReal,Complex.conj_ofReal]; rw [show (reflFields a' s U).1=fling a' s (Ω f) U.1 from rfl,cred_swing]
variable {b z A:ℝ}(hp:f≤r)(hz:r≤v)
include u t
lemma gap_swing : gapMark Y i k b z hp hz ((plane a' s).mills (Ω f) x)= reflMark a' (highTurn P f v s) (gapMark Y i k b z hp hz x):=by
 unfold gapMark principal extra_δ chamber; rw [heel_swing,heel_swing,route_swing,route_swing,ring_tour _ _ _ u _ t _ _ ((route_owns ..).mono (subset_univ _)),show ((L).val:ℤ)^(v-r)* _=highTurn P f v s from high_turn_toll s hp hz];
 funext w'; unfold reflMark; simp only [Pi.smul_apply,Pi.sub_apply,theta_smul,theta_sub,Complex.star_def,Complex.conj_ofReal]
lemma band_gap (h:w+12 ≤ d)(g:node x∈ band (Ω f) a' s d): AtSupport false (band (Ω v) a' (highTurn P f v s) w) (gapMark Y i k b z hp hz x):=by
 unfold gapMark principal extra_δ chamber; rw [sub_eq_add_neg]; apply AtSupport.smulM; refine AtSupport.addM ((band_true Y i k a' _ _ h (moving_band Y i _ _ x (hp.trans hz) g) _).smulM _) ((neg_one_smul (M:=Mark (Ω v)) ℂ _) ▸ AtSupport.smulM ?_ (-1)); rw [← high_turn_toll s hp hz]; exact band_path Y i k a' _ _ u t _ (band_true Y i k _ _ _ h (moving_band Y _ _ _ _ hp g) _) -- named α maybe syntax
omit u t
/- packing tests. -/
abbrev rural (e:ℕ):= cape_B e+cape_B e+e+e
abbrev repeatD (P:Preparation)(ℓ e:ℕ):= reserve P ℓ+12+rural e
lemma tenderD (H:Real.exp 1≤ P.x)(s i k:ℕ)(g:Ferry Y s i k): Twosome (tent Y H) (side Y i s) (solder Y i k g.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k g.depth s; let F:=solder Y i k g.depth s; have ht:=boxprice Y H i k g.depth s g.fire g.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
lemma graceful_clock (H:Real.exp 1≤ P.x)(g:Ferry Y v i k)(e:ℕ):
 Again.GraceA Δ (repeatD P ℓ e) (rural e) (gapMark Y i k b z hp hz) (solder Y i k g.depth v) (highTurn P f v) (reserve P ℓ):=by
 refine ⟨by unfold repeatD; omega, fun i' s x u=> band_gap Y i k i' s x g.depth g.enters hp hz (Nat.le_add_right _ _) u, fun i' s x=> gap_swing Y i k i' s x g.depth g.enters hp hz,?_⟩
 intro a t f' B YQ; let z:= Heat.gaugeShift Δ t; let v':= (highTurn P f v t); have hp:highTurn P f v z= Heat.gaugeShift Δ v':=by unfold v' z highTurn Heat.gaugeShift; ring
 have hx: AtSupport false (band (Ω v) a (Heat.gaugeShift Δ v') w) f':= hp ▸ YQ; rw [show B= _ from hp]; exact tenderD Y H v i k g a v' f' hx -- B deflet; hp rw z
variable {t':ℝ}
open Again
variable (l:List (Site (side Y i f)))
local notation "e"=> (RootBook Y i k f).p.B
lemma solid_call (h:outdoor (rural (RootBook Y i k f).p.B) l) : CityCall Y i k (fun i=>l.get i):=by
 have u(x y :Fin l.length)(hx: x≠y): rural (RootBook Y i k f).p.B < separation (node (l.get x)) (node (l.get y)):= by
    rcases lt_or_gt_of_ne hx with h0|h0; exact List.pairwise_iff_get.mp h x y h0; rw [separation_comm]; exact List.pairwise_iff_get.mp h y x h0
 refine ⟨fun i j g=>?_,fun i j g=>u _ _ (fun h=>g (h ▸ rfl))⟩
 by_contra hv; have ht:=u i j hv; dsimp only [Function.comp_apply] at g; rw [g,separation_self] at ht; omega
lemma gap_ticket (X:ShelterCost c Y f i k)(u':ReadDensity Y i k A hp hz b z t')(h:outdoor (rural e) l):
 ‖Journey.compass Y i k v (l.map (gapMark Y i k b z hp hz)).prod‖≤ steamRent P A f (side Y i f) (2*l.length) l.length:=by
 let α:=Fin l.length; let Z:= List.finRange l.length; let V:= Z.map Astr; have ht:CasePage V:=by
    unfold V CasePage; rw [List.map_map,show (QuadClock.host ∘ Astr) = _root_.id (α:=α) from rfl,List.map_id]; exact List.nodup_finRange _ -- tune
 have he:= layout_receipt Y X hp hz u' l.get (solid_call Y i k l h) V ht; have hv: V.map (menuClock Y i k l.get b z t' hp hz)= l.map (gapMark Y i k b z hp hz):=by
    unfold V; rw [List.map_map,show menuClock Y i k l.get b z t' hp hz ∘ Astr= (gapMark Y i k b z hp hz) ∘ l.get from funext fun _=> menu1 ..,←List.map_map,List.map_get_finRange l]; -- Z reducible?
 rw [hv] at he; apply he.trans_eq; congr 1
 · simp [Article,mul_comm] -- Lex card
 simp [V,Z]
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.graceful_clock
