import YM.SU5.Selected.Pioneer

/-! # Harvest **all slots on ONE phase**. Packing geometry

Stay true to this choice of prescription on Papal.mixed_law_with_ground. Refine
`Pannier/Vintage` argument (replicate all axes) here in new namespace for pair of frames needed
for variance. Test chosen at positive time (and privilege only that location, then can use
stationarity to translate by mesh units). Does not purport to test mass or dynamics.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 210000
noncomputable section
namespace YM.CF.Pannier.Chancel.Survival
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace Mir Lifted Advance
open Py.Rate.Pannier Afterglow Afterglow.Tower Afterglow.Tower.SlabMark -- avoid region
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra

variable {B:ℕ} (K:Calibration) (j:Axis)
abbrev camp (B : ℕ) : Cover := fun _ => (B:ℤ)
private lemma sits {x : Cover} (p : x∈ Sen (camp B) B) (a : Axis) : (B:ℤ)+1 ≤ x a ∧ x a ≤ 3*(B:ℤ)+1 := by
 obtain ⟨i,e,rfl⟩:=mem_image.mp p; obtain ⟨w,z⟩:=box_test.mp e; specialize w a; specialize z a; change _≤ i a+ (nodeC (camp B)) a ∧ i a + (nodeC (camp B)) a ≤ _; unfold nodeC; simp only [Pi.smul_apply,Pi.add_apply,Pi.one_apply,camp]; change _≤ i a+(2*↑B+1)∧ i a+(2*↑B+1)≤_; omega
lemma marches (p : K.ℓ≤B) : Tower.region j 0 K.ℓ (Sen (camp B) B) := by
 intro x t; obtain ⟨h,_⟩:= sits t j; omega
variable {m n : Side}
lemma offered (h: K.ℓ ≤ B) (p : 6*B+1≤ n.val) : Islet n (camp B) B ⊆ band n j (0:ℤ) K.ℓ := by
 rw [sen_islet]; exact enters_arc K j (x:=0) (fun i p'=> by obtain ⟨a,b⟩:= sits p' j; constructor <;> omega) rfl
lemma unmix (h: K.ℓ ≤ B) (p : 6*B+1≤ n.val) : Disjoint (hyphen j 0 (Islet n (camp B) B)) (Islet n (camp B) B) := west K j 0 _ (offered K j h p)
lemma combined_cow (v:Axis) (p:0<B) :
    cows v (hyphen j 0 (Islet n (camp B) B) ∪ Islet n (camp B) B) (8*B) := by
 refine ⟨-4 * (B:ℤ),?_⟩; intro x hx
 -- reflected coords from across_coord and dist if v=j; anon otherwise. use Sen
 rw [sen_islet] at hx
 rcases mem_union.mp hx with h|h
 · obtain ⟨y,hy,rfl⟩:= mem_image.mp h; obtain ⟨z,h',rfl⟩:= mem_image.mp hy; obtain ⟨d,e⟩:= sits h' v; let y:=wrap (More n) z
   by_cases f:j=v
   · subst v; have hz : (plane j 0).anon n y j= - (y j):= by simpa only [Int.cast_zero,sub_zero] using across_coord j 0 y
     exact ⟨-z j,by omega,by omega, show ((↑(-z j):Per (More n))) = (plane j 0).anon n y j from by rw [hz, Int.cast_neg]; rfl⟩
   have hh : (plane j 0).anon n y v= y v := by simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,f]; -- tune namespace
   exact ⟨ z v, by omega, by omega, hh.symm⟩
 obtain ⟨z,h',rfl⟩:= mem_image.mp h; obtain ⟨d,e⟩:= sits h' v; exact ⟨z v, by omega, by omega, rfl⟩

private lemma goldilock (x y:ℕ)(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
 -- Lean details as in Trefl
 have he : x < 2^x*y:= lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_mul_of_pos_right _ p)
 let P(k:ℕ):= x≤ 2 * (2^k)*y
 have ht: ∃ k,P k:= ⟨x,by unfold P; linarith⟩
 refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
 generalize e:Nat.find ht=k
 cases k with
 | zero=> simpa using v
 | succ k=> have h:=Nat.find_min ht (by omega:k< Nat.find ht); change ¬ x ≤ _ at h; change ¬ x ≤ 2*(2^k)*y at h; rw [pow_succ']; omega

-- two Flight on `F.broad=...` (still pay object by name!)
variable {ν: Buffered.Mark n→ℂ}{M:Tulip.Male}{R:ℝ}{i k w d t:ℕ}{γ τ:ℝ}
local notation "S" => (Islet n (camp B) B)
local notation "F₀" => Flight i M w d t γ τ
lemma excursion (c: Cliplet n k) (h:c.broad=S) (p: StageTw K ν i R d M)
    (f: Perron i M w d t γ τ c) (e: K.ℓ≤B)(v : 8*B+addgap K≤ n.val) :
    Flight i M w d t γ τ [c.mirror j 0,c] := by
 have a:F₀ [c]:= Flight.alone f
 let t':= a.reflect j 0 (p.across j 0) p.hire
 apply t'.tack _ a
 rw [Flight.reflect_consistent]
 refine ?_; simpa [whereV,h] using unmix K j e (v.trans' (by have hx:0<addgap K:= addgap_pos; omega))
lemma data_bill (c: Cliplet n k) : probe [c.mirror j 0,c]= reflMark j 0 c.frame * c.frame:= by
 simp only [probe_cons,probe_nil,mul_one]; rfl
lemma two_pack (c: Cliplet n k) (h:c.broad=S) (p: StageTw K ν i R d M)
    (f: Perron i M w d t γ τ c) (e: K.ℓ≤B)(v: 8*B+addgap K≤ n.val)(p':n=K.c m)(hB:0<B):
    ∃ (U: List (Cliplet n k)) (u : ℕ), Flight i M w d t γ τ U ∧ 0<u ∧ u*2=U.length ∧
       U.length ≤ (More n).val^4 ∧ (More n).val^4 ≤ u*(4*(8*B+addgap K))^4 ∧
       ‖ν (reflMark j 0 c.frame * c.frame)‖^u ≤ ‖ν (probe U)‖:=by
 obtain ⟨k',a,l⟩:= goldilock n.val _ (show 0 < 8*B+addgap K from Nat.add_pos_right _ addgap_pos) v
 have ht(v:Axis) : cows v (whereV [c.mirror j 0,c]) (8*B) := by
    change cows v ((hyphen j 0 c.broad) ∪ (c.broad ∪ ∅)) _; rw [union_empty,h]; exact combined_cow j v hB
 obtain ⟨V,q,dJ,hJ⟩ := p.scatter p' a univ [c.mirror j 0,c] (excursion K j c h p f e v) (fun i _=> ht i)
 rw [card_fin 4] at dJ hJ -- Axis abbreviation
 simp only [List.length_cons,List.length_nil] at dJ
 refine ⟨V,(2^k')^4,q,by positivity,dJ.symm,?_,?_,?_⟩
 · rw [dJ]; change _ ≤ (n.val*2)^4; rw [mul_pow]; gcongr
   · exact (Nat.le_mul_of_pos_right _ (Nat.add_pos_right _ (show 0<addgap K from addgap_pos))).trans a -- extra
   · decide
 · rw [←mul_pow]; apply pow_le_pow_left'; change n.val*2≤_; exact (Nat.mul_le_mul_right 2 l).trans_eq (by ring)
 rw [data_bill] at hJ; exact hJ

end YM.CF.Pannier.Chancel.Survival
