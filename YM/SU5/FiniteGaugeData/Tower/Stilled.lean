import YM.SU5.FiniteGaugeData.Tower.Helmsman
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set
/-!
# From rung projection to full axis ground

p_s decreasing integral-grid projections tending strongly to p_axis. Include
all time weights here so no assumption of monotonicity through strong-continuity
projection in space. p_axis lies in continuous subspace automatically. `ground`
for vacuum selection means annihilated by spatial AND Euclidean energy;
not heat only (possible nonzero spatial frequencies at energy 0 before speed
or rotation tested). -/
section close
variable {H:Hilbert}
open Submodule
private lemma solidProj(U:Submodule ℂ H)[CompleteSpace U]:IsClosed (U:Set H):=(completeSpace_coe_iff_isComplete.mp (show CompleteSpace (U:Set H) from inferInstanceAs (CompleteSpace U))).isClosed
lemma project_to_project (p q:Submodule ℂ H)[CompleteSpace p][CompleteSpace q](h:p ≤ q)(x:H):
 p.starProjection (q.starProjection x)=p.starProjection x := by
 apply ext_inner_left ℂ
 intro y; rw [← Submodule.inner_starProjection_left_eq_right,← Submodule.inner_starProjection_left_eq_right q, starProjection_eq_self_iff.mpr (h (starProjection_apply_mem p y)), Submodule.inner_starProjection_left_eq_right]

lemma falling (p:ℕ→Submodule ℂ H)[∀n,CompleteSpace (p n)] (h:Antitone p) (X:Submodule ℂ H)[CompleteSpace X](w:X=⨅i:ℕ,p i)(x:H):
 Tendsto (fun i=> (p i).starProjection x) atTop (𝓝 (X.starProjection x)):=by
 let d(i:ℕ):H:= (p i).starProjection x
 let q(i:ℕ):= ‖d i‖^2
 let s:=⨅ i:ℕ,q i
 have he(i j:ℕ)(t:i≤j):dist (d i) (d j)^2=q i-q j:=by
    have ht: (p i).starProjection (d j)=d j:=by rw [Submodule.starProjection_eq_self_iff]; exact h t (starProjection_apply_mem _ _)
    have hh: inner ℂ (d i) (d j)=inner ℂ (d j) (d j):=by
       nth_rw 1 [show d i=_ from rfl]
       change inner ℂ ((p i).starProjection x) (d j)=inner ℂ ((p j).starProjection x) (d j)
       rw [inner_starProjection_left_eq_right,ht, inner_starProjection_left_eq_right,starProjection_eq_self_iff.mpr ((p j).starProjection_apply_mem x)]
    rw [dist_eq_norm,norm_sub_sq (𝕜:=ℂ),hh,inner_self_eq_norm_sq]; unfold q; ring
 have hN(i j:ℕ)(t:i ≤ j):q j ≤ q i:= by have ht:=he i j t; linarith [sq_nonneg (dist (d i) (d j))]
 have hb:BddBelow (Set.range q):= ⟨0,by rintro _ ⟨i,rfl⟩; exact sq_nonneg _⟩
 have ht:Tendsto q atTop (𝓝 s):=tendsto_atTop_ciInf (show Antitone q from fun x y=>hN x y) hb
 have hc:CauchySeq d:=by
    apply Metric.cauchySeq_iff'.mpr; intro ε k
    obtain ⟨i,g⟩:=(ht.eventually (gt_mem_nhds (lt_add_of_pos_right s (pow_pos k 2)))).exists
    refine ⟨i,fun j h=>?_⟩
    rw [dist_comm]; apply (sq_lt_sq₀ dist_nonneg k.le).1; rw [he _ _ h]; have ht:s ≤ q j:=ciInf_le hb _; change q i < _ at g; linarith
 obtain ⟨y,hY⟩:=cauchySeq_tendsto_of_complete hc
 have hy:y∈X:=by
    rw [w,Submodule.mem_iInf]; intro i
    have he:IsClosed (p i:Set H):= solidProj _
    refine he.mem_of_tendsto hY ((eventually_ge_atTop i).mono (fun j t=>h t ((p j).starProjection_apply_mem x)))
 have hf:y=X.starProjection x:= by
    symm; apply eq_starProjection_of_mem_of_inner_eq_zero hy
    intro v u
    have ht:Tendsto (fun i=>inner ℂ (x - (d i)) v) atTop (𝓝 (inner ℂ (x-y) v)):= ((tendsto_const_nhds (x:=x)).sub hY).inner (tendsto_const_nhds (x:=v))
    refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Eventually.of_forall fun i=> ?_))
    rw [w] at u; exact (Submodule.starProjection_inner_eq_zero _ _ (((Submodule.mem_iInf _).mp u) i)).symm
 exact hf ▸ hY
end close

variable {Λ:Preparation}{lp:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus lp))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H Q.circuit j 0 strict C
local notation "S₀" s:max=> office Y H V s Q j strict C
local notation "g₀" s:max=> ((S₀ s).toMoving)
local notation "Ω"=>floorV Y H Q.circuit j 0 strict C
local notation "P₀" s:max=> Console.sky (S₀ s) (look j)
local notation "Y₀"=> (clockdrive Y H V Q.circuit j 0 strict C).monoAxis j
local notation "Λ'" s:max=> Moving.aligned (g₀ s) (look j)
def Conserves : Submodule ℂ (Ark.Ht Y H Q.circuit j 0 strict C):= (Y₀).ground ⊓ (Λ' s)
local notation "Yₜ" s:max=>Conserves Y H V s Q j strict C
instance whole_space: CompleteSpace (Yₜ s):=by
 have h: IsClosed ((Yₜ s):Set A):=IsClosed.inter (solidProj (Y₀).ground) (solidProj (Λ' s))
 exact h.completeSpace_coe
lemma formal(x:A): x∈Yₜ s ↔
 (∀i:ℝ≥0,advance Y H V Q.circuit j 0 strict C i x=x)∧(∀ i:Trans j,∀ z:ℤ,sailV Y H V s Q.circuit j 0 strict i.val i.property C (2*z) x=x):=by
 change x∈ (Y₀).ground ⊓ Λ' s ↔ _; rw [Submodule.mem_inf,(Y₀).fixed, Moving.aligned_ok];
 suffices ∀ i:Trans j, ∀ n:ℤ, ((g₀ s).move i).wind n = sailV Y H V s Q.circuit j 0 strict (i:Axis) i.property C (2*n) by
    simp_rw [this,look_all j, forall_true_left]; rfl
 intro i n; exact on_ladder Y H V s Q.circuit j 0 strict C i n
lemma names: (Yₜ s).starProjection=P₀ s:=by
 ext1 x
 let d:= Moving.pause (g₀ s) (look j)
 let P:= (Y₀).orth
 change _=P (d x)
 apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
 · change P (d x)∈(Y₀).ground ⊓ Λ' s
   exact ⟨(Y₀).ground.starProjection_apply_mem _,(S₀ s).steady_lives (look j) ((g₀ s).par (look j) x)⟩
 intro v t; change v ∈(Y₀).ground ⊓ (Λ' s) at t
 unfold P d; rw [inner_sub_left, (Y₀).ground.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr t.1,(g₀ s).swing (look j),(g₀ s).pin v t.2,sub_self] -- orth abbrev
lemma nested : Antitone (fun i=> Conserves Y H V i Q j strict C):=by
 intro v u h x e
 rw [formal Y H V _ Q] at *
 refine ⟨e.1,fun i t=>?_⟩
 rw [sailV_high Y H V _ _ _ _ _ _ _ _ (2*t) u h,smill,mul_left_comm _ (2:ℤ)]
 exact e.2 _ _
abbrev Aurora:Submodule ℂ (Ark.Ht Y H Q.circuit j 0 strict C):= ⨅ i:ℕ,(Yₜ i)
local notation "E₀"=>Aurora Y H V Q j strict C
instance glowing: CompleteSpace (E₀):=by
 have h:IsClosed ((E₀):Set A):=by rw [Submodule.coe_iInf]; exact isClosed_iInter fun i=> solidProj _
 exact h.completeSpace_coe
lemma strands(x:A):Tendsto (fun n=> (P₀ n) x) atTop (𝓝 ((E₀).starProjection x)):=by simp_rw [← names]; exact falling _ (nested Y H V Q j strict C) _ rfl _
lemma belongs: Ω∈ E₀:= by
 rw [Aurora,Submodule.mem_iInf]; intro i
 rw [formal]; exact ⟨fun _=> advance_vacuum Y H V .., fun _ _=>sailV_vac ..⟩
lemma floor_rise(p:E₀)(n:ℝ≥0):advance Y H V Q.circuit j 0 strict C n p.val=p.val:=(formal Y H V 0 Q j strict C _|>.1 (((Submodule.mem_iInf _).mp p.property) 0)).1 n
end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.strands
