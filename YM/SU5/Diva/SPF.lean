import YM.SU5.Diva.Canoe
/-! Adaptation of Fluxion,Audition,Duet. Testing ALL clans, same enrollment.
 Two tolerance orders: take R large first. The internal evaluation estimate
 is on the true spin/color/momentum form, invoked on auxiliarily-chosen sequences
 (does not need a continuum limit for these volumes). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{j:ℕ}
open Py.Rate.LocalLimit.Papal (Weaver)
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
namespace Twah
open Lead (Clan)
open YM.Stationary (Gaia)
open Lamour.Bridge
variable {I:Type*} (Z:I→Clan)(Y:ℕ→ I→Twah)(L:List I)(s:ℕ→ℕ) {Q:ℕ→Side}{N:Side}
-- free two component spin assignments. Composition Gibbs has explicit order.
abbrev Cellz(I:Type*):= I × Bool
abbrev colbase {I:Type*}(u:Stamp I): Cellz I:= (u.1,u.2.2)
abbrev actualSpin (A:Twah):= (A.up,A.low)
abbrev bodyF (a:I→Twah):= actualSpin ∘ a
def nearPoints(r:ℕ)(F:I→Twah)(q:Cellz I):= riseX (r:ℝ) ((F q.1).oasis q.2)
abbrev DirSpin := Fin 2 × Fin 2
def readS (a: DirSpin)(u:Slot)(b:Bool): Emu.Wing:=⟨if b then dnSpin a.2 else upSpin a.1,u,1⟩
def pilotS(D:I→DirSpin)(i:Stamp I):= readS (D i.1) i.2.1 i.2.2
variable (P:Cellz I→Gaia) {x v:Gaia} (D:I→DirSpin)
def germRho {I:Type*}(P:Cellz I→Gaia) (D:I→DirSpin)(i k:Stamp I):ℂ := let a:=pilotS D i; let b:=pilotS D k; let x:= P (colbase i)-P (colbase k); if signW a=signW b then 0 else if signW a then frank a b x else -(frank b a (-x))
def witness := chore Z (runes (germRho P D)) [] L
#check @witness
private lemma continuous_leap {y:Gaia}(p:y≠0) : ContinuousAt pencil y:=by
 refine ContinuousAt.smul (g:=gleamV) (f:=fun x:Gaia=>(Real.pi^2*‖x‖^4)⁻¹) ?_ ?_
 · exact ContinuousAt.inv₀ (f:=fun x:Gaia=> Real.pi^2*‖x‖^4) (by fun_prop) (mul_ne_zero (pow_ne_zero _ Real.pi_pos.ne') (pow_ne_zero _ (norm_pos_iff.mpr p).ne'))
 unfold gleamV; apply ContinuousAt.mul continuousAt_const; apply Continuous.continuousAt; exact continuous_finsetSum _ (fun i _=> ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ _)).smul continuous_const))
lemma pointF (a b:Emu.Wing)(u:ℕ→Gaia)(h:Tendsto u atTop (𝓝 x))(v:x=0→∀ᶠ i:ℕ in atTop,u i=0): Tendsto (fun i=>frank a b (u i)) atTop (𝓝 (frank a b x)):=by
 by_cases p:x=0; · exact tendsto_const_nhds.congr' ((v p).mono (fun i v=> congrArg (frank a b) (p.trans v.symm)))
 unfold frank; split; swap; · exact tendsto_const_nhds -- split tactic f lambda?
 exact ((show Continuous fun i:Peb=> i a.a b.a from continuous_id.matrix_elem a.a b.a).continuousAt.comp (continuous_leap p)).tendsto.comp h
abbrev crumbs (Y:ℕ→I→Twah)(n:ℕ)(p:Cellz I): Cover:= (Y n p.1).oasis p.2
def plateau := ∀ p q:Cellz I,P p=P q→∀ᶠ i:ℕ in atTop, crumbs Y i p=crumbs Y i q
def riseUp := ∀ v:Cellz I,Tendsto (fun i:ℕ=> nearPoints (s i) (Y i) v) atTop (𝓝 (P v))
variable (Yp:riseUp Y s P)(Yu:plateau Y P)
include Yp Yu
lemma pinStrong (u v:Stamp I): Tendsto (fun i=>germRho (nearPoints (s i) (Y i)) D u v) atTop (𝓝 (germRho P D u v)):=by
 let U := colbase u; let V:= colbase v; let p:=P U-P V; let F(i):= nearPoints (s i) (Y i); let X(i):= F i U-F i V; have hp:Tendsto X atTop (𝓝 p):= (Yp _).sub (Yp _)
 have ht(x:p=0):∀ᶠ i:ℕ in atTop,X i=0:=(Yu _ _ (sub_eq_zero.mp x:P U=P V)).mono fun i hi => sub_eq_zero.mpr (congrArg (riseX (s i)) hi)
 unfold germRho; dsimp only; split_ifs; · exact tendsto_const_nhds
 · exact pointF _ _ X hp ht
 exact (pointF (pilotS D v) (pilotS D u) (-X) hp.neg (by rw [neg_eq_zero]; intro g; filter_upwards [ht g] with i p; rw [Pi.neg_apply,p,neg_zero])).neg
omit Yp Yu
lemma fulcrum {F:List (Stamp I) → ℂ}{G:ℕ→ List (Stamp I) → ℂ}(H:∀ u, Tendsto (fun i=> G i u) atTop (𝓝 (F u)))(u:List (Stamp I)) : Tendsto (fun i=> chore Z (G i) u L) atTop (𝓝 (chore Z F u L)):=by induction L generalizing u with| nil=> exact H _| cons i L hx=> exact tendsto_finsetSum _ (fun i _=>hx _)
include Yp Yu
lemma witnessFlows : Tendsto (fun i=> witness Z L (nearPoints (s i) (Y i)) D) atTop (𝓝 (witness Z L P D)):= fulcrum Z L (fun v=>offer_v _ _ (pinStrong Y s P D Yp Yu) v) []
-- Product at any history T Pres shadow. Supply arrangement spine not needed for kernel cost, this part exact.
variable (Yh:Yard Q (fun i=> (s i:ℝ))) (Yt: ∀ i, bodyF (Y i)=D) (j) (h:1≤j)
include Yh Yt h
lemma colorTangent (M:ℕ→Jill.Male)(Ht:∀ i,Kea.Pad j (Q i))(t:∀ i,Wave (Single (Q i)))(p:∀ i, Sea (spar j (M i) (1:Pane (Q i))) (t i)) : Tendsto (fun i:ℕ=> alleyR (mateK (Q i)) (t i) (plait (Y i) Z L (s i) (Q i) (1,1))) atTop (𝓝 (witness Z L P D)):=by
 let P': Plot (Stamp I) (fun i:ℕ=> (s i:ℝ)):= ⟨fun i p=> crumbs Y i (colbase p),pilotS D,P ∘ colbase,fun x=> Yp _,fun x y=> Yu _ _⟩
 obtain ⟨u,v,g⟩:= lake_formal h
 let A(i):= (lake (Q i) j (M i)); have hx(i): A i = Dofu (Q i) (lakeP (Q i) j (M i)):=rfl
 have he(i:ℕ)(u:Stamp I): P'.tag (m:=i) 0 (Kea.tax emptyC) 1 u=pulse (Y i) (Q i) (s i) u:=by
    change nac _ _ _ _ _=nac _ _ _ _ _; rw [clear_canvas, show P'.seat u=pilotS (bodyF (Y i)) u from congrArg (fun A=>pilotS A u) (Yt i).symm]; rfl
 simp_rw [show ∀ i:ℕ, alleyR (mateK _) (t i) (plait _ Z L (s i) _ (1,1)) = _ from fun i=>jewel_bank (Y i) Z L (s i) h (Ht i) (M i) _ (p i)] -- tune
 apply fulcrum (F:=runes (germRho P D)) (G:=fun i=> runes _) Z L ?_
 intro x; refine (P'.sun (r:=u) (C:=1) (d:=fun _=>emptyC) (fun i=>too _) M (fun i:ℕ=>lakeP _ j (M i)) (fun _=>0) Yh v (by norm_num) (fun x:Slot=> Eventually.of_forall (fun i=> g _ (Ht i).1 (M i) x)) h (fun _=>1) x).congr fun i=> ?_
 simp_rw [show ∀ (w:Stamp I), P'.tag (m:=i) _ _ _ w=pulse (Y i) _ _ _ from he i]; rfl
omit Yh h Yp Yt Yu
variable [Fintype I] -- makes [Finite] Gaian inputs
abbrev sitesX(Y:I→Twah)(p:Cellz I):Cover:= (Y p.1).oasis p.2
def Spill(X:I→Twah)(D d:ℝ)(R:ℕ): Prop:= (∀ i, dist (nearPoints R X i) 0≤D) ∧∀ i j, sitesX X i ≠ sitesX X j → d≤ dist (nearPoints R X i) (nearPoints R X j)
omit [Fintype I] in
lemma may_cover {D d:ℝ}(p:0<d)(h:∀ i, Spill (Y i) D d (s i))(Yp:riseUp Y s P) : plateau Y P:=by
 intro x y g; filter_upwards [show ∀ᶠ i:ℕ in atTop, dist (nearPoints (s i) (Y i) x) (nearPoints (s i) (Y i) y)< d from ((Yp x).dist (Yp y)).eventually (gt_mem_nhds (show dist (P x) (P y)<d by rw [g,dist_self]; exact p))] with i ht; by_contra u; exact not_le.mpr ht ((h i).2 x y u)
variable{u v:ℝ}
private lemma room_spill (w:0<v)(hS:∀ i,Spill (Y i) u v (s i)) : ∃ (f:ℕ→ℕ)(P':Cellz I→Gaia), StrictMono f ∧ riseUp (Y∘f) (s∘ f) P' ∧ plateau (Y ∘ f) P':=by
 let A(n:ℕ):= nearPoints (s n) (Y n); obtain ⟨P',hf,f,hu,H⟩:= IsCompact.tendsto_subseq (x:=A) (isCompact_pi_infinite (fun _=> isCompact_closedBall 0 u)) (fun n i=> (hS n).1 i); let t:= tendsto_pi_nhds.mp H; have H:riseUp (Y ∘ f) (s ∘ f) P':= fun i=> t i
 exact ⟨f,P',hu,H, may_cover (Y∘f) (s∘f) P' w (fun i=> hS (f i)) H⟩
open Py.Rate.LocalLimit.Papal (meanF)
include h
/-- Against *same*-level free compound. For any UV viewer with a compact arity menu. Coordinates
 are generic continuum zoom grid points. Does not take f bounded amount lift; Ξ Diesel to be applied
 after this proof. No cost limits inferred from other-history spins.
-/
theorem aroma (ε:ℝ)(v:u>0)(D':ℝ)(p:0<ε):∀ᶠ R:ℕ in atTop,∀ Y:I→Twah, Spill Y D' u R → bodyF Y=D → Clarity (meanF (plait Y Z L R) (witness Z L (nearPoints R Y) D)) j ε:=by
 let K'(R:ℕ) (Y:I→Twah) (N:Side) (M:Jill.Male):Prop:= Py.Rate.LocalLimit.Papal.translucent (meanF (plait Y Z L R) (witness Z L (nearPoints R Y) D)) j ε N M
 change ∀ᶠ R:ℕ in atTop,∀ Y:I→Twah, Spill Y D' u R → bodyF Y=D → ∀ᶠ N:Side in atTop, Even N.val → ∀ M:Jill.Male,K' R Y N M
 by_contra o
 have hp (n:ℕ) :∃ (R:ℕ) (Y:I→Twah), n < R ∧ Spill Y D' u R ∧ bodyF Y=D ∧ ∃ᶠ N:Side in atTop, ¬(Even N.val→∀ M:Jill.Male,K' R Y N M):=by
   obtain ⟨R,p₀,t⟩:= ((not_eventually.mp o).and_eventually (eventually_gt_atTop n)).exists; rcases not_forall.mp p₀ with ⟨Y,hY⟩; apply Exists.intro R; refine ⟨Y,t,?_,?_,?_⟩; exact (_root_.not_imp.mp hY).1; exact (_root_.not_imp.mp (_root_.not_imp.mp hY).2).1; exact not_eventually.mp (_root_.not_imp.mp (_root_.not_imp.mp hY).2).2
 choose C V hc hv hD hV using hp
 obtain ⟨f,P,Q,hP,uP⟩:=room_spill V C v hv
 let s:= C∘ f; let Y:= V∘f; have ht(i):0<(s i:ℝ):=by exact_mod_cast (Nat.zero_le (f i)).trans_lt (hc (f i))
 have hs: Tendsto (fun i:ℕ=>(s i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp ((tendsto_atTop_mono (fun i=> (hc i).le) tendsto_id).comp Q.tendsto_atTop)
 have hz(i:ℕ):∃ (N:Side) (M:Jill.Male),Kea.Pad j N ∧ (s i:ℝ)* Ember.pinch N ≤ (2:ℝ)⁻¹^i ∧ ¬ K' (s i) (Y i) N M :=by
    obtain ⟨z,U⟩:= Glaze.pick_depth (p:=(show 0< (2:ℝ)⁻¹^i/(s i:ℝ) from (by have e:= ht i; positivity))) -- tune
    obtain ⟨N,p,g,t⟩:= ((hV (f i)).and_eventually ((ownsHalo h).and (eventually_ge_atTop (⟨z+1,by omega⟩:Side)))).exists
    push Not at p; obtain ⟨v,M,x⟩:=p; refine ⟨N,M,(g v).1, (mul_comm _ _).le.trans ((le_div_iff₀ (ht i)).1 (U (by change z+1≤N.val at t; omega))), x⟩
 choose N M hN w W using hz
 unfold K' Py.Rate.LocalLimit.Papal.translucent at W; push Not at W; choose x e hc using W
 have hy:Yard N (fun i=>(s i:ℝ)):= ⟨ht,hs,squeeze_zero (fun i=> mul_nonneg (ht i).le (Ember.pinch_pos _).le) w (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),fun i=>(hN i).1⟩
 have he:= (colorTangent j Z Y L s P D hP uP hy (fun i=> hD (f i)) h M hN x e).sub (witnessFlows Z Y L s P D hP uP); let g(i:ℕ):=alleyR (mateK (N i)) (x i); rw [sub_self,tendsto_zero_iff_norm_tendsto_zero] at he; obtain ⟨i,t⟩:=(he.eventually (gt_mem_nhds p)).exists; have hv:=hc i
 rw [show meanF (plait (Y i) Z L (s i)) (witness Z L (nearPoints (s i) (Y i)) D) (N i) (1,1)= _ from (show _=(plait (Y i) Z L (s i) (N i) (1,1)-witness Z L (nearPoints (s i) (Y i)) D • (1: FC (Single (N i)))) from rfl),map_sub,map_smul,alley_one h (hN i) (x i) (e i),smul_eq_mul,mul_one] at hv
 exact not_lt_of_ge hv.le t
end Twah
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Twah.colorTangent
#print axioms YM.CF.Buffered.Ballad.Twah.aroma
