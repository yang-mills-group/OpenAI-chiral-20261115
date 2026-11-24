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
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) (j:Axis)
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
variable (V:P.PowerNames x A)
variable {n:ℕ}(B:Fin n→List Axis)(p:Points n)(u v:Fin n→ℝ)
abbrev stage_ace(j:Axis)(q:Points n): Fin n→ ℝ:= fun i=> q i j
abbrev reachU (m:ℕ): Fin n→ P.Apron:= fun i=> χ m (B i)
abbrev Vants (q:Points n): Fin n→ Vantage:= fun i=> lens (q i)
local notation "z'"=> stage_ace j p
variable (a b:ℝ)(d:GateK (stage_ace j p) u v b)(c:a<b)(t:StepsW (stage_ace j p) a)
private lemma appeased {X:Hilbert} {Y:Type*}(l:List Y)(F:ℕ→Y→ X.Op)(Z:Y→ X.Op)(h: ∀ y, Brakes (fun i=> F i y) (Z y)): Brakes (fun i=> (l.map (F i)).prod) ((l.map Z).prod):=by
 induction l with | nil=> exact Brakes.by_budget tendsto_const_nhds | cons i l ih=> exact (h i).weave ih
private lemma whole_map {n:ℕ}{Y:Type*}(f:Fin n→Y): (Each n).map f=List.ofFn f:=by induction n with | zero=> rw [List.ofFn_zero]; rfl | succ n ih=> rw [List.ofFn_succ]; unfold Each; rw [List.finRange_succ,List.map_cons,List.map_map]; exact congrArg (List.cons (f 0)) (ih (f ∘ Fin.succ))
abbrev gallery_LocalFieldBounds(m:ℕ): (P.ManyF j (P.advocate 3 x j)).Op:= ((Each n).map (fun i=> gtW (P.reachU A B m i) (u i) (v i) (Vants p i))).prod
local notation "G'"=> P.gallery_LocalFieldBounds x A j B p u v
local notation "R'"=> fun i:Fin n=> V.rate j (B i)
local notation "F'"=> fun i:Fin n=> V.fields j (B i)
abbrev PowerNames.rounds (i:Fin n):= rebate (ν) ((V.fields j)∘B) ((V.rate j)∘B) (fun k=> sepV j (p k)) (stage_ace j p) u v i
local notation "Y'"=> V.rounds P x A j B p u v
include V d c
lemma PowerNames.circles : Brakes (P.gallery_LocalFieldBounds x A j B p u v) ((List.ofFn (Y')).prod):=by
 rw [← whole_map]; unfold gallery_LocalFieldBounds; apply appeased
 intro y; obtain ⟨a,b⟩:=msumK (ν) ω (P.transportsK x j) (stage_ace j p) u v a b d c y; exact P.certificate x A j _ _ (B y) _ (V.price ..) (V.paid _ _) _ a b -- check params msum
lemma PowerNames.passP : ∀ᶠ m in atTop,∀ i, u i < P.porchY j (P.reachU A B m) (Vants p) i ∧ P.resignY j (P.reachU A B m) (Vants p) i < v i:=by
 refine eventually_all.mpr ?_; intro i; obtain ⟨w,y⟩:=msumK (ν) ω (P.transportsK x j) (stage_ace j p) u v a b d c i
 let X:= V.price j (B i)
 let F(m:ℕ):=(P.reachU A B m i).realWidth P j; have h:Tendsto F atTop (𝓝 0):= X.prices.thin
 let r:= stage_ace j p i; filter_upwards [h.eventually (gt_mem_nhds (sub_pos.mpr w)),h.eventually (gt_mem_nhds (sub_pos.mpr y))] with m t z
 change u i < (stage_ace j p) i-F m ∧ (stage_ace j p) i+F m<v i; constructor <;> linarith only [t,z]
lemma PowerNames.seenK : ∀ᶠ m in atTop, P.Turnstile j (P.reachU A B m) (Each n) (Vants p):=by
 -- Gate comparison adjacency + propagation. Need generate adjacency of all vs actual. simpler induct on n from Gate & p. Heights hull.[u,v]
 have hp(m:ℕ)(h:∀ i, u i < P.porchY j (P.reachU A B m) (Vants p) i ∧ P.resignY j (P.reachU A B m) (Vants p) i < v i): P.Turnstile j (P.reachU A B m) (Each n) (Vants p):=by
    -- intrinsic lemma
    suffices H:∀ {n:ℕ}(z u v X X':Fin n→ℝ)(b:ℝ), GateK z u v b → (∀ i,u i<X i ∧ X' i<v i) → ∀ m:ℕ,(Each n).Pairwise (fun i j=> X' i < X j) ∧ ∀ i:Fin n,b<X i from (H _ _ _ _ _ b d h 0).1 -- tune b<X true
    clear d; intro n; induction n with
    | zero=> intro z u v X X' b h t n; exact ⟨List.Pairwise.nil,fun i=>Fin.elim0 i⟩
    | succ n ih=>
       intro z u v X X' b h t m; obtain ⟨w,a,c,d⟩:=h; obtain ⟨he,hv⟩:=ih (Fin.tail z) (Fin.tail u) (Fin.tail v) (Fin.tail X) (Fin.tail X') _ d (fun i=>t i.succ) m
       unfold Each; rw [List.finRange_succ]; refine ⟨List.pairwise_cons.mpr ⟨?_,List.pairwise_map.mpr he⟩,fun i=> Fin.cases (w ▸ (t 0).1) (fun x=>a.trans (c.trans (hv x))) i⟩
       intro j z; obtain ⟨k,e,rfl⟩:= List.mem_map.mp z; exact (t 0).2.trans (hv k)
 filter_upwards [V.passP P x A j B p u v a b d c] with m w; exact hp m w -- indentation
include t
abbrev EuGift (j:Axis)(q:Points n)(a:ℝ): Times n:= fun i=> OS.Semigroup.duration (momentsE (stage_ace j q) a i)*Complex.I
abbrev PowerNames.promiseW (f:Times n):= waveArc (P.seasons j (P.advocate 3 x j)) (P.heaven j (P.advocate 3 x j)) ((V.rate j) ∘ B) ((V.fields j)∘B) p.ofLp f
omit V d c in
lemma EuGift_ready : EuGift j p a ∈ _root_.YM.SatinJets.OrientedTimes n:=by
 intro i; change 0 < (EuGift j p a i).im; have hp: 0 < (momentsE (stage_ace j p) a i:ℝ):= show 0 < momentsE (stage_ace j p) a i from (Stair_gate _ a).mp t i
 simpa [EuGift,OS.Semigroup.duration] using hp
lemma PowerNames.offerE : V.promiseW P x A j B p (EuGift j p a) = (η (b-a).toNNReal) ((List.ofFn (Y')).prod ω):=by
 unfold PowerNames.promiseW waveArc; let B':= (R'); let C':= (F'); let M:=(ν); let z:= EuGift j p a; let f:=stage_ace j p; let v':= momentsE f a
 let t':=fun i:Fin n=> parabola M (pedestal 0 B' i) (-(z i)*Complex.I); have h: t'=slew M (pedestal 0 B') v':=by ext1 i; change parabola M _ (-(OS.Semigroup.duration (v' i)*Complex.I)*Complex.I)= Par M _ (v' i); rw [neg_mul,mul_assoc,Complex.I_mul_I,mul_neg, mul_one,neg_neg]
 let D(q:Fin n):= sepV j (p q); change regiaN M ω n t' C' 0 D=_; rw [h]; have he:= galaK M ω (P.transportsK x j) 0 C' B' D (stage_ace j p) u v a b d c 0
 rw [neg_zero,tini, show Par M 0 (b-a).toNNReal=M.E (b-a).toNNReal from M.roots_heat (Real.toNNReal_pos.mpr (sub_pos.mpr c))] at he
 exact he
lemma PowerNames.reportE : Tendsto (fun m=> P.memorial j ξ (P.reachU A B m) (Each n) (Vants p)) atTop (𝓝 (inner ℂ ω (V.promiseW P x A j B p (EuGift j p a)))):=by
 rw [V.offerE P x A j B p u v a b d c t]; let Z:=stage_ace j p
 rw [← OS.Semigroup.swing, P.heaven_hot]
 have hp:= V.circles P x A j B p u v a b d c
 apply (tendsto_const_nhds.inner (hp.brakes ω)).congr'
 filter_upwards [V.passP P x A j B p u v a b d c] with m s; exact (P.pill_memorial j _ _ _ _ u v (fun i _=> s i) (adjacency Z u v a b d)).symm
omit d c
variable (J:P.Ellis 3 x)
include J
lemma BureauE : Tendsto (fun m=> P.commonWell 3 x (P.reachU A B m) (Vants p) (Each n)) atTop (𝓝 (inner ℂ ω (V.promiseW P x A j B p (EuGift j p a)))):=by
 obtain ⟨b,w,q⟩:=points_offer _ a t
 obtain ⟨u,v,d⟩:=heirs _ b q
 apply (V.reportE P x A j B p u v a b d w t).congr'
 filter_upwards [V.seenK P x A j B p u v a b d w] with m q; exact (P.common_cult 3 x _ _ _ J (List.Perm.refl _) q).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
