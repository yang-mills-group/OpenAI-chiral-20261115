import YM.CF.Mew.Sup
import YM.CF.Mew.Lace
import YM.CF.Vow.Peso
import YM.CF.Rue.Coin
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function NormedSpace Filter Metric Finset MeasureTheory
open Skye Scree Jet Vow Lattice Wilson RG Forge Cube
open scoped Topology ContDiff BigOperators Matrix
variable{n: Side}{P:BudgetPoint}{I J Z:Type}[Fintype I][Fintype Z][DecidableEq Z]
local notation "DN"=> tangD n
structure Kine (n:Side)(V:BudgetPoint) where
 Var : Type
 cap : Var→Set (Pane n)
 paid :∀ i,IsOpen (cap i)
 reads: Var → Finset (Pressure.Bond (More n))
 o:Seat n
abbrev Stirs (K:Kine n P)(f:K.Var→Pane n→ℂ)(c:ℝ):Prop:=∀ i:K.Var,∀ u∈K.cap i,Signs P K.o (f i ∘ gyrate (K.reads i) u) c
structure Bough (K:Kine n P) where
 k: ℕ
 p: k ≤ P.order
 i: K.Var
 U:Pane n
 h: U∈K.cap i
 y: Fin k→tangD n
 bound: ∀ i,P.dirBound K.o (y i)
abbrev ViewK (K:Kine n P) := Option (Bough K)
variable(S: I → Kine n P)(W:I→J→ℝ)(p:∀ i j,0 ≤ W i j)(u:∀ i,∃ j,0<W i j)(V:J→ℝ)
def PileK(K:Kine n P)(U:K.Var→Pane n→ℂ)(p: Option (Bough K)):ℂ:=match p with
 | none=>0
 | some x=> iteratedFDeriv ℝ x.k (U x.i ∘ gyrate (K.reads x.i) x.U) 0 x.y
lemma grade_unit(z:ℂ)(o:Seat n){U:tangD n→ℂ}{c:ℝ}(p:Signs P o U c):Signs P o (z • U) (‖z‖*c):=by
 refine ⟨by have hx:=p.grade; positivity,contDiffAt_const.smul p.paid,fun k hk i ht=>?_⟩; rw [iteratedFDeriv_const_smul_apply (p.paid.of_le (by exact_mod_cast hk)),_root_.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (p.token k hk i ht) (norm_nonneg _)
variable (F:∀ i,Z → (S i).Var→ Pane n→ℂ) -- Z actually Key.B
structure Shady (F:∀ i,(S i).Var→Pane n→ℂ):Prop where
 pay: ∃ y:I→ℝ, (∀ i,0 ≤ y i)∧(∀ i,Stirs (S i) (F i) (y i))∧ (∀ k:J,∑ i,W i k*y i ≤ V k)
-- transfer of norm budget, Cauchy residues even without common choice envelope; ORD unchanged.
variable (G:∀ i,Key Z→(S i).Var→Pane n→ℂ)(g:∀ z∈ hill Z,Shady S W V (fun i=> G i z))(hp:∀ i (j:(S i).Var) U,U∈(S i).cap j→ River (fun z=> G i z j U))
local notation "HX" i:max z:max => (fun k x y=> cutI (fun w:Key Z => G k w x y) i z)
include hp g u p
lemma shade_c(i':Z)(z:Key Z)(hz:z∈hill Z):Shady S W V (fun k x y=> cutI (fun w:Key Z=>G k w x y) i' z):=by
 let K(a:ℝ): Key Z:= update z i' (homeB a); have hK(a:ℝ):K a∈ hill Z:= fill_I hz _ (homeC _); let v(i:I)(a:ℝ)(j:(S i).Var)(x:Pane n):ℂ:= (homeB a)⁻¹ • G i (K a) j x
 choose U hu t H using fun i:ℝ=>(g _ (hK i)).pay
 have ht(a i): Stirs (S i) (v i a) (U a i):=by intro j x e; have h' :=grade_unit (homeB a)⁻¹ _ (t a i j x e); rw [norm_inv, home_q,inv_one,one_mul] at h'; exact h'
 have he (i:I):∃ C:ℝ,0 ≤ C∧∀ a:ℝ, Stirs (S i) (v i a) C:=by
    obtain ⟨j,hj⟩:= u i; have hx(a):U a i ≤ V j / W i j:= (le_div_iff₀ hj).mpr (by rw [mul_comm]; exact (single_le_sum (fun i _=>mul_nonneg (p i j) (hu a i)) (mem_univ i)).trans (H a j)); have hv':= (hu 0 i).trans (hx 0)
    exact ⟨_,hv',fun a k x g=>⟨hv',(ht a i k x g).paid,fun l hl v h=> ((ht a i k x g).token l hl v h).trans (hx a)⟩⟩
 choose C pC hc using he
 let s:=HX i' z
 have hπ(i j X)(t:X∈(S i).cap j):= Rue.rank_pi ((S i).paid j) (fun (y:Pane n) (hy:y∈(S i).cap j) a=> hc i a j y hy) (fun U u=> (stayB (hp i j U u) hz i').stronglyMeasurable) (pC i) sky X t
 let T (i)(x:ViewK (S i))(a:ℝ):ℂ:= PileK (S i) (v i a) x
 have hσ(i:I)(x:ViewK (S i)):Integrable (T i x) sky ∧ PileK (S i) (s i) x=∫ a,T i x a ∂sky:=by
    cases x; exact ⟨integrable_const _ ,(integral_zero _ _).symm⟩
    rename_i o; obtain ⟨p,g⟩:= (hπ _ _ _ o.h).2 o.k o.p; let D:= ContinuousMultilinearMap.apply ℝ (fun _ : Fin o.k=> tangD n) ℂ o.y
    refine ⟨D.integrable_comp p, ?_⟩; change D (iteratedFDeriv ℝ o.k (fun z=>∫ a:ℝ,v i a o.i (gyrate ((S i).reads o.i) o.U z)∂sky) 0)= _; rw [g,←D.integral_comp_comm p]; rfl
 let W':=fun (i:I) (x:ViewK (S i))=>‖PileK (S i) (s i) x‖
 have hW(j:J)(f:∀ i,ViewK (S i)):∑ i,W i j* W' i (f i) ≤ V j:=by
    refine (sum_le_sum (g:=fun i=>W i j*(∫ a,‖T i (f i) a‖ ∂sky)) ?_ ).trans ?_; · intro i _; apply mul_le_mul_of_nonneg_left _ (p i j); unfold W'; rw [(hσ i _).2]; exact norm_integral_le_integral_norm _
    have hh (i:I): Integrable (fun a=>W i j*‖T i (f i) a‖) sky:= ((hσ i (f i)).1.norm).const_mul _
    simp_rw [← integral_const_mul]; rw [←integral_finsetSum _ (fun k _=> hh k)]; refine le_trans (integral_mono (integrable_finsetSum _ fun k _=> hh k) (integrable_const (V j)) (fun a=>?_)) (le_of_eq (by simp)); change ∑ k,W k j*_ ≤ _; apply le_trans _ (H a j); refine sum_le_sum (fun k _=>mul_le_mul_of_nonneg_left ?_ (p k j)); unfold T; cases h:f k with
    | none=> rw [PileK,norm_zero]; exact hu a _
    | some v=> exact (ht a k v.i v.U v.h).token v.k v.p v.y v.bound
 obtain ⟨b,h,hB,q⟩:=pulse_max (fun i=> ViewK (S i)) (fun i=>⟨none⟩) W p u W' (fun i j=>norm_nonneg _) V hW
 exact ⟨b,h,fun i j o t=> ⟨h i,(hπ _ _ _ t).1,fun k p y s=>hB i (some ⟨k,p,j,o,t,y,s⟩)⟩,q⟩
lemma shade_l (l:List Z)(z:Key Z)(hz:z∈hill Z): Shady S W V (fun k x y=> lance (fun w: Key Z=> G k w x y) l z):=by induction l generalizing G with
 | nil=> exact g _ hz
 | cons i j h=> exact h (fun k z x y=> cutI (fun w=>G k w x y) i z) (fun x y=> shade_c S W p u V G g hp i x y) (fun i' k y p=>(hp i' k y p).flow i)
end YM.CF.Mew
