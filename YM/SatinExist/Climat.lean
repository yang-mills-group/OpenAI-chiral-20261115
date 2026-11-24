import YM.SatinExist.ExpressP
import YM.SatinExist.Chelo
import YM.SatinExist.Ione
/-!
 # Real stitch payments. Convergence.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3700
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry TopologicalSpace
namespace Spine
open Aria Casting
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld LineDeriv
open _root_.YM.Boundary Spectral Poin
local notation "j"=> (3:Axis)
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) 
local notation "ξ"=>P.advocate 3 x j
local notation "CX"=> P.ManyF j (P.advocate 3 x j)
local notation "ν"=> P.seasons j (P.advocate 3 x j)
local notation "λ'"=> P.ColorHil j (P.advocate 3 x j)
local notation "ω"=> P.heaven j (P.advocate 3 x j)
local notation "gtW"=>P.pillar j (P.advocate 3 x j)
local notation "G"=> P.cartage j (P.advocate 3 x j)
local notation "Φ"=> Bench (P.seasons j (P.advocate 3 x j))
local notation "η"=> (P.seasons j (P.advocate 3 x j)).E
local notation "T"=> M (P.seasons j (P.advocate 3 x j))
local notation "K"=> Cache (P.seasons j (P.advocate 3 x j))
local notation "χ" i:max J:max=> (A i).pivot P J
section
variable (F:(P.ManyF j (P.advocate 3 x j)).Op) (r:ℕ) (t:P.Concerto x A r F)
include t
lemma Concerto.thin3 : Tendsto (fun i=>(A i).realWidth P 3) atTop (𝓝 0):=by
    simp_rw [← P.bookRig]; change Tendsto _ _ (𝓝 ((0:ℝ≥0):ℝ)); exact NNReal.tendsto_coe.mpr t.thin
lemma open_C {a b :ℝ}(d:0 < a)(v:0 < b): Brakes (fun i=> gtW (A i) (-a) b 0) (Par (ν) r (Real.toNNReal a)*F*Par (ν) r b.toNNReal) := by
 let s:= min a b; have hx:s≤a:= min_le_left ..; have ht:s≤b:=min_le_right ..; have hz:0 < s:= lt_min d v; have hh:= (t.purchase s.toNNReal (Real.toNNReal_pos.mpr hz))
 let y:=s.toNNReal; let W:=η (a-s).toNNReal; let X:=η (b-s).toNNReal; have hW:Brakes (fun _:ℕ=>W) W:= Brakes.by_budget tendsto_const_nhds; have hX:Brakes (fun _:ℕ=>X) X:=Brakes.by_budget tendsto_const_nhds
 apply ((hW.weave hh).weave hX).sameC
 · filter_upwards [(Concerto.thin3 P x A F r t).eventually (gt_mem_nhds hz)] with i e; let D:= A i; change D.realWidth P j < s at e; have he:= P.bigger_door j ξ D (-a) b (-s) s 0 (neg_le_neg hx) ht (by unfold Apron.time_panel; simp only [Pi.zero_apply]; linarith only [e]) (by unfold Apron.time_edge; simp only [Pi.zero_apply]; linarith only [e]); rw [show -s - -a=a-s from by abel] at he
   show W*gtW D (-(s.toNNReal:ℝ)) (s.toNNReal:ℝ) 0*X= _
   rw [Real.coe_toNNReal _ hz.le]; exact he.symm
 let Z:=F; have t':0< y:=Real.toNNReal_pos.mpr hz;
 have hw(t:ℝ)(v:s≤t): Par (ν) r y*η (t-s).toNNReal=Par (ν) r t.toNNReal:=by have e:=landDiv (ν) t.toNNReal r y t' (Real.toNNReal_le_toNNReal v); rw [show t.toNNReal-y=(t-s).toNNReal from NNReal.eq (by rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal v), Real.coe_toNNReal _ (hz.le.trans v), Real.coe_toNNReal _ (sub_nonneg.mpr v)]; rw [show (y:ℝ)=s from Real.coe_toNNReal _ hz.le])] at e; exact e.symm
 have hw': W * Par (ν) r y=Par (ν) r a.toNNReal:=by
    have H:=congrArg star (hw a hx); rw [star_mul,(parRev (ν) y r t').star_eq, show star (η _) = η (a-s).toNNReal from (ν).sym _, (parRev (ν) _ _ (Real.toNNReal_pos.mpr d)).star_eq] at H; exact H
 have u:plated (ν) F (r:=r) (s.toNNReal:ℝ) = Par (ν) r y * F* Par (ν) r y:=by simp only [plated,Real.toNNReal_coe]; rfl
 rw [u]
 change W*(Par _ _ _ * _ * _)*X=_; simp only [mul_assoc]; rw [hw b ht,←mul_assoc W,hw'] -- tune X
lemma C_window {a b:ℝ} (p:E4) (v:a < p j)(u:p j < b): Brakes (fun i=>gtW (A i) a b (lens p)) (T (sepV j p)*Par (ν) r (p j-a).toNNReal *F* Par (ν) r (b-p j).toNNReal*T (-sepV j p)):=by
 simp_rw [P.moves_edge, show a-p j= -(p j-a) from by abel]; have he:=P.open_C x A F r t (sub_pos.mpr v) (sub_pos.mpr u)
 have hp(X:(CX).Op):Brakes (fun _:ℕ => X) X:=Brakes.by_budget tendsto_const_nhds
 exact ((hp (T (sepV j p))|>.weave he|>.weave (hp _)).sameC (Eventually.of_forall fun i=>rfl) (by simp [mul_assoc])) -- order
end
section Gallery
variable {n:ℕ}(B: ℕ→Fin n→P.Apron)(D:Fin n→(P.ManyF 3 (P.advocate 3 x 3)).Op)(M':Fin n→ℕ)(V: ∀ k,P.Concerto x (fun i=> B i k) (M' k) (D k))
variable (p:Points n)(u v:Fin n→ℝ)
local notation "z'"=> stage_ace j p
variable (a b:ℝ)(d:GateK (stage_ace j p) u v b)(c:a<b)(t:StepsW (stage_ace j p) a)
private lemma appeasedC {X:Hilbert} {Y:Type*}(l:List Y)(F:ℕ→Y→ X.Op)(Z:Y→ X.Op)(h: ∀ y, Brakes (fun i=> F i y) (Z y)): Brakes (fun i=> (l.map (F i)).prod) ((l.map Z).prod):=by
 induction l with | nil=> exact Brakes.by_budget tendsto_const_nhds | cons i l ih=> exact (h i).weave ih
private lemma whole_mapC {n:ℕ}{Y:Type*}(f:Fin n→Y): (Each n).map f=List.ofFn f:=by induction n with | zero=> rw [List.ofFn_zero]; rfl | succ n ih=> rw [List.ofFn_succ]; unfold Each; rw [List.finRange_succ,List.map_cons,List.map_map]; exact congrArg (List.cons (f 0)) (ih (f ∘ Fin.succ))
abbrev galleries(m:ℕ): (P.ManyF j (P.advocate 3 x j)).Op:= ((Each n).map (fun i=> gtW (B m i) (u i) (v i) (Vants p i))).prod
local notation "G'"=> P.galleries x B p u v
local notation "R'"=> fun i:Fin n=> M' i
local notation "F'"=> fun i:Fin n=> D i
abbrev roundsC (i:Fin n):= rebate (ν) D M' (fun k=> sepV j (p k)) (stage_ace j p) u v i
local notation "Y'"=> P.roundsC x D M' p u v
include V d c
lemma cir_C : Brakes (P.galleries x B p u v) ((List.ofFn (Y')).prod):=by
 rw [← whole_mapC]; unfold galleries; apply appeasedC
 intro y; obtain ⟨a,b⟩:=msumK (ν) ω (P.transportsK x j) (stage_ace j p) u v a b d c y; exact P.C_window x _ _ _ (V y) _ a b -- check params msum
lemma passP_C : ∀ᶠ m in atTop,∀ i, u i < P.porchY j (B m) (Vants p) i ∧ P.resignY j (B m) (Vants p) i < v i:=by
 refine eventually_all.mpr ?_; intro i; obtain ⟨w,y⟩:=msumK (ν) ω (P.transportsK x j) (stage_ace j p) u v a b d c i
 let X:= V i
 let F(m:ℕ):=(B m i).realWidth P j; have h:Tendsto F atTop (𝓝 0):= Concerto.thin3 _ _ _ _ _ (V i)
 let r:= stage_ace j p i; filter_upwards [h.eventually (gt_mem_nhds (sub_pos.mpr w)),h.eventually (gt_mem_nhds (sub_pos.mpr y))] with m t z
 change u i < (stage_ace j p) i-F m ∧ (stage_ace j p) i+F m<v i; constructor <;> linarith only [t,z]
lemma seenK_C : ∀ᶠ m in atTop, P.Turnstile j (B m) (Each n) (Vants p):=by
 -- Gate comparison adjacency + propagation. Need generate adjacency of all vs actual. simpler induct on n from Gate & p. Heights hull.[u,v]
 have hp(m:ℕ)(h:∀ i, u i < P.porchY j (B m) (Vants p) i ∧ P.resignY j (B m) (Vants p) i < v i): P.Turnstile j (B m) (Each n) (Vants p):=by
    -- intrinsic lemma
    suffices H:∀ {n:ℕ}(z u v X X':Fin n→ℝ)(b:ℝ), GateK z u v b → (∀ i,u i<X i ∧ X' i<v i) → ∀ m:ℕ,(Each n).Pairwise (fun i k=> X' i < X k) ∧ ∀ i:Fin n,b<X i from (H _ _ _ _ _ b d h 0).1 -- tune b<X true
    clear d; intro n; induction n with
    | zero=> intro z u v X X' b h t n; exact ⟨List.Pairwise.nil,fun i=>Fin.elim0 i⟩
    | succ n ih=>
       intro z u v X X' b h t m; obtain ⟨w,a,c,d⟩:=h; obtain ⟨he,hv⟩:=ih (Fin.tail z) (Fin.tail u) (Fin.tail v) (Fin.tail X) (Fin.tail X') _ d (fun i=>t i.succ) m
       unfold Each; rw [List.finRange_succ]; refine ⟨List.pairwise_cons.mpr ⟨?_,List.pairwise_map.mpr he⟩,fun i=> Fin.cases (w ▸ (t 0).1) (fun x=>a.trans (c.trans (hv x))) i⟩
       intro j' z; obtain ⟨k,e,rfl⟩:= List.mem_map.mp z; exact (t 0).2.trans (hv k)
 filter_upwards [P.passP_C x B D M' V p u v a b d c] with m w; exact hp m w -- indentation
include t

abbrev promisesC (f:Times n):= waveArc (P.seasons 3 (P.advocate 3 x 3)) (P.heaven 3 (P.advocate 3 x 3)) M' D p.ofLp f
lemma offerE_C : P.promisesC x D M' p (EuGift j p a) = (η (b-a).toNNReal) ((List.ofFn (Y')).prod ω):=by
 unfold promisesC waveArc; let B':= (R'); let C':= (F'); let M:=(ν); let z:= EuGift j p a; let f:=stage_ace j p; let v':= momentsE f a
 let t':=fun i:Fin n=> parabola M (pedestal 0 B' i) (-(z i)*Complex.I); have h: t'=slew M (pedestal 0 B') v':=by ext1 i; change parabola M _ (-(OS.Semigroup.duration (v' i)*Complex.I)*Complex.I)= Par M _ (v' i); rw [neg_mul,mul_assoc,Complex.I_mul_I,mul_neg, mul_one,neg_neg]
 let Dx(q:Fin n):= sepV j (p q); change regiaN M ω n t' C' 0 Dx=_; rw [h]; have he:= galaK M ω (P.transportsK x j) 0 C' B' Dx (stage_ace j p) u v a b d c 0
 rw [neg_zero,tini, show Par M 0 (b-a).toNNReal=M.E (b-a).toNNReal from M.roots_heat (Real.toNNReal_pos.mpr (sub_pos.mpr c))] at he
 exact he
lemma reportE_C : Tendsto (fun m=> P.memorial j ξ (B m) (Each n) (Vants p)) atTop (𝓝 (inner ℂ ω (P.promisesC x D M' p (EuGift j p a)))):=by
 rw [P.offerE_C x B D M' V p u v a b d c t]; let Z:=stage_ace j p
 rw [← OS.Semigroup.swing, P.heaven_hot]
 have hp:= P.cir_C x B D M' V p u v a b d c
 apply (tendsto_const_nhds.inner (hp.brakes ω)).congr'
 filter_upwards [P.passP_C x B D M' V p u v a b d c] with m s; exact (P.pill_memorial j _ _ _ _ u v (fun i _=> s i) (adjacency Z u v a b d)).symm
omit t d c
variable (s:Equiv.Perm (Fin n))
lemma reading_C(Q:P.Ellis 3 x)(a:ℝ)(h:DiningE j p s a): Tendsto (fun m=> P.commonWell 3 x (B m) (Vants p) (Each n)) atTop
    (𝓝 (inner ℂ ω (P.promisesC x (D∘s) (M'∘s) (nextSeam p s) (EuGift j (nextSeam p s) a)))):=by
 let X:=nextSeam p s; let B' (m):= B m ∘ s; let z:= stage_ace j X
 obtain ⟨b,w,t⟩:=points_offer z a h; obtain ⟨u,v,d⟩:= heirs z b t
 apply (P.reportE_C x B' (D ∘ s) (M' ∘ s) (fun k=> V (s k)) X u v a b d w h).congr'
 let L:=Each n; let s':=L.map s; have hMatch:L.Perm s':=by
    apply List.perm_ext_iff_of_nodup (by exact List.nodup_finRange n) ((List.nodup_finRange n).map s.injective) |>.mpr
    intro i; have he:=List.mem_finRange i; refine ⟨fun _=>List.mem_map.mpr ⟨s.symm i,List.mem_finRange _,s.apply_symm_apply _⟩,fun _=>he⟩
 filter_upwards [P.seenK_C x B' (D ∘ s) (M' ∘ s) (fun k=> V (s k)) X u v a b d w] with m e
 let ν':= B m; let D':=Vants p; have hp:P.Turnstile j ν' s' D':= List.pairwise_map.mpr e
 rw [P.common_cult 3 x _ _ _ Q hMatch hp]; -- recursive equality memorial map
 suffices H:∀ L:List (Fin n), P.memorial j ξ (ν'∘s) L (D'∘s)=P.memorial j ξ ν' (L.map s) D' from H L
 intro L; unfold memorial; rw [← rector_view (ν) ω _ _ _ (P.heaven_hot j ξ) 0, ← rector_view (ν) ω _ _ _ (P.heaven_hot j ξ) 0]; congr 2
 generalize (0:ℝ)=g; induction L generalizing g with
 | nil=> rfl
 | cons i L ih=> rw [rector_left,List.map_cons,rector_left,ih]; rfl
end Gallery
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
