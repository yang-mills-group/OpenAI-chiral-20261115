import YM.SatinExist.Seaspray
/-!
 # Permutative seam accounting on ALL time axes. Allows continuing even near disordered external leg first. W algebra in H-c.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3700
set_option maxHeartbeats 400000
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
local notation "ω'"=> P.Asp x j
local notation "gtW"=>P.pillar j (P.advocate 3 x j)
local notation "G"=> P.cartage j (P.advocate 3 x j)
local notation "Φ"=> Bench (P.seasons j (P.advocate 3 x j))
local notation "η"=> (P.seasons j (P.advocate 3 x j)).E
local notation "T"=> M (P.seasons j (P.advocate 3 x j))
local notation "K"=> Cache (P.seasons j (P.advocate 3 x j))
local notation "χ" i:max J:max=> (A i).pivot P J
variable (V:P.PowerNames x A)
variable {n:ℕ}(B:Fin n→List Axis)(p:Points n)
local notation "r"=> V.rate j ∘ B
local notation "F"=> V.fields j ∘ B
local notation "W"=> V.action P x A j
variable (s: Equiv.Perm (Fin n))
def DiningE (j:Axis)(q:Points n)(s:Equiv.Perm (Fin n))(a:ℝ):Prop:= StepsW ((stage_ace j q) ∘ s) a
abbrev nextSeam (s:Equiv.Perm (Fin n)):= WithLp.toLp 2 (p.ofLp ∘ s)
lemma perm_w(Q:P.Ellis 3 x)(a:ℝ)(h:DiningE j p s a): Tendsto (fun m=> P.commonWell 3 x (P.reachU A B m) (Vants p) (Each n)) atTop
    (𝓝 (inner ℂ ω (V.promiseW P x A j (B ∘ s) (nextSeam p s) (EuGift j (nextSeam p s) a)))):=by
 let X:=nextSeam p s; let B':= B ∘ s; let z:= stage_ace j X
 obtain ⟨b,w,t⟩:=points_offer z a h; obtain ⟨u,v,d⟩:= heirs z b t
 apply (V.reportE P x A j B' X u v a b d w h).congr'
 let L:=Each n; let s':=L.map s; have hMatch:L.Perm s':=by
    apply List.perm_ext_iff_of_nodup (by exact List.nodup_finRange n) ((List.nodup_finRange n).map s.injective) |>.mpr
    intro i; have he:=List.mem_finRange i; refine ⟨fun _=>List.mem_map.mpr ⟨s.symm i,List.mem_finRange _,s.apply_symm_apply _⟩,fun _=>he⟩
 filter_upwards [V.seenK P x A j B' X u v a b d w] with m e
 let ν':= P.reachU A B m; let D':=Vants p; have hp:P.Turnstile j ν' s' D':= List.pairwise_map.mpr e
 rw [P.common_cult 3 x _ _ _ Q hMatch hp]; -- recursive equality memorial map
 suffices H:∀ L:List (Fin n), P.memorial j ξ (ν'∘s) L (D'∘s)=P.memorial j ξ ν' (L.map s) D' from H L
 intro L; unfold memorial; rw [← rector_view (ν) ω _ _ _ (P.heaven_hot j ξ) 0, ← rector_view (ν) ω _ _ _ (P.heaven_hot j ξ) 0]; congr 2
 generalize (0:ℝ)=g; induction L generalizing g with
 | nil=> rfl
 | cons i L ih=> rw [rector_left,List.map_cons,rector_left,ih]; rfl
variable (a:ℝ)
section Follows
variable (f:Fin n→Test4)(Ω: Bench (P.seasons j (P.advocate 3 x j)))
-- corresponding preinit thermal product
abbrev HBills (s:ℝ≥0) (k:ℕ) := SatinJets.accord (P.seasons j (P.advocate 3 x j)) (fun i=> gtW (χ k (B i)) (-(s:ℝ)) (s:ℝ) 0) f Ω
abbrev posBills (s:ℝ≥0) := SatinJets.accord (P.seasons j (P.advocate 3 x j)) (fun i=> V.trace j (B i) s) f Ω
abbrev TestBills := inCourse (P.seasons j (P.advocate 3 x j)) (V.rate j ∘ B) (V.fields j ∘ B) 0 f Ω
abbrev labelBills (i:Fin n):= (V.action P x A j (B i)) (f i)
lemma beat_bills (e:ℝ≥0)(d:0<e): pays_to (P.seasons j (P.advocate 3 x j)) atTop (P.HBills x A j B f Ω e) (P.posBills x A j V B f Ω e) := by
 induction n with
 | zero=> exact fun _=> tendsto_const_nhds
 | succ n ih=>
    let X':=(P.seasons j (P.advocate 3 x j)); have he:=(V.price j (B 0)).prices.paid (e:ℝ) d
    simp_rw [one_smul] at he
    obtain ⟨g,z⟩:=he.costs
    have ht:= SatinJets.purchase X' _ _ he.brakes g z (f 0) (P.posBills x A j V (Fin.tail B) (Fin.tail f) Ω e) _ (ih (Fin.tail B) (Fin.tail f)) 0
    have hw(a:(CX).Op)(f:Test4):ℑ X' a f 0=ℑ₀ X' a f:=by ext1 y; apply Subtype.ext; have hm:= CF.Buffered.Afterglow.Hierarchy.Seld.native X' a f y 0; rw [CF.Buffered.Afterglow.Hierarchy.Seld.home] at hm; exact hm
    simp_rw [hw] at ht; exact ht
lemma empty_stove (v:Bench (P.seasons j (P.advocate 3 x j))): stove (ν) 0 v=v:=stove_zero ..
lemma granted_W : (List.ofFn (P.labelBills x A j V B f)).prod Ω=P.TestBills x A j V B f Ω:=by
 induction n with
 | zero=> rw [List.ofFn_zero]; rfl
 | succ n ih=> let f':= Fin.tail f; let A':= Fin.tail B; let L:= P.labelBills x A j V B f; rw [List.ofFn_succ,List.prod_cons];
               change L 0 ((List.ofFn (P.labelBills x A j V A' f')).prod Ω)= stove (ν) 0 (L 0 (P.TestBills x A j V A' f' Ω)); rw [ih,P.empty_stove]
lemma heat_limit : pays_to (ν) (𝓝[>] (0:ℝ≥0)) (P.posBills x A j V B f Ω) (P.TestBills x A j V B f Ω) :=by
 induction n with
 | zero=> exact fun _=> tendsto_const_nhds
 | succ n ih=>
    let B':= Fin.tail B; let f':= Fin.tail f; let Y:= P.TestBills x A j V B' f' Ω
    let X:= P.labelBills x A j V B f; let D:= P.posBills x A j V B' f' Ω; let v:= B 0; let s:= V.rate j v; let u:= 𝓝[>] (0:ℝ≥0); let S:=ν; let Z:= V.trace j v; let C':=V.fields j v;
    have he:pays_to S u (fun i:ℝ≥0=> ℑ₀ S (Z i) (f 0) (D i)) (X 0 Y):= δLimit S s Z C' (f 0) Y u id tendsto_id D (ih B' f') (V.paid j (B 0)) -- order
    change pays_to S u _ (stove S 0 (X 0 Y)); rw [stove_zero]; exact he
end Follows
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
