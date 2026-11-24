import YM.CF.Mew.Rain
import YM.CF.Mew.Tube
import YM.CF.Roots.Sort

/-!
# Uniform port. Vary test-lists even in a single `pay` sale

All donors (including idle Axis) jointly at *the same Key*. Enables Σ saves
while varying the tariff books with the parameters. Adapt `Mew.shade_c`.
-/
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
variable{n: Side}{P:BudgetPoint}{I J Z:Type}[Fintype I][Fintype Z][LinearOrder Z]
variable(S: I → Kine n P)(W:I→J→ℝ)(p:∀ i j,0 ≤ W i j)(u:∀ i,∃ j,0<W i j)(V:J→ℝ)

-- cost-one even at idle Key (undifferentiated factor)
def trimB (cut : Bool) (a : ℝ) : ℂ:= if cut then (homeB a)⁻¹ else 1
lemma trim_face (cut : Bool) : Continuous (trimB cut) ∧ ∀ a,‖trimB cut a‖=1 := by
 unfold trimB; split
 · exact ⟨(continuous_circleMap ..).inv₀ (fun x=> norm_ne_zero_iff.mp (by rw [←homeB,home_q]; norm_num)),fun x=>by rw [norm_inv,home_q,inv_one]⟩
 exact ⟨continuous_const,fun _=> norm_one⟩
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
abbrev entrance (cut:Bool) (f:Key Z → A)(i:Z)(v:Key Z) : A := ∫ a:ℝ, trimB cut a • f (update v i (homeB a)) ∂sky
lemma entranceV (f:Key Z→A)(p:River f)(cut:Bool)(i:Z)(z:Key Z)(hz:z∈hill Z) :
    entrance cut f i z = if cut then cutI f i z else f (update z i 0) := by
 split
 · rename_i h; subst cut; rfl
 rename_i h; rw [entrance, ca_uc f p z i hz 0 (mem_ball_self (by norm_num))]; unfold feed_K; unfold trimB; apply integral_congr_ae; apply ae_of_all; intro a
 have ha:homeB a≠0:=norm_ne_zero_iff.mp (by rw [home_q]; norm_num)
 simp only [if_neg h,sub_zero,mul_inv_cancel₀ ha]
lemma entrance_bill (f:Key Z→A)(p:River f)(cut:Bool)(i:Z):River (entrance cut f i) := by
 cases cut
 · refine (p.stay i).cong fun z w=>?_; exact (entranceV f p _ i z w).trans (if_neg Bool.false_ne_true)
 refine (p.flow i).cong fun z w=>?_ ; rfl

variable (G : ∀ i, Key Z → (S i).Var → Pane n → ℂ)(g:∀ z ∈ hill Z,Shady S W V (fun i=>G i z))(hp:∀ i (j:(S i).Var) U,River (fun z=>G i z j U))
include hp g u p
lemma allPad (f : ∀ i,(S i).Var→ Bool)(i':Z)(z:Key Z)(hz:z∈hill Z):
    Shady S W V (fun i k V=> entrance (f i k) (fun z=> G i z k V) i' z) := by
 let K(a:ℝ): Key Z:= update z i' (homeB a); have hK(a:ℝ):K a∈ hill Z:= fill_I hz _ (homeC _); let v(i:I)(a:ℝ)(j:(S i).Var)(x:Pane n):ℂ:= trimB (f i j) a • G i (K a) j x
 choose U hu t H using fun i:ℝ=>(g _ (hK i)).pay
 have ht(a i): Stirs (S i) (v i a) (U a i):=by intro j x e; have h' :=grade_unit (trimB (f i j) a) _ (t a i j x e); rw [(trim_face _).2 a,one_mul] at h'; exact h'
 have he (i:I):∃ C:ℝ,0 ≤ C∧∀ a:ℝ, Stirs (S i) (v i a) C:=by
    obtain ⟨j,hj⟩:= u i; have hx(a):U a i ≤ V j / W i j:= (le_div_iff₀ hj).mpr (by rw [mul_comm]; exact (single_le_sum (fun i _=>mul_nonneg (p i j) (hu a i)) (mem_univ i)).trans (H a j)); have hv':= (hu 0 i).trans (hx 0)
    exact ⟨_,hv',fun a k x g=>⟨hv',(ht a i k x g).paid,fun l hl v h=> ((ht a i k x g).token l hl v h).trans (hx a)⟩⟩
 choose C pC hc using he
 let s:= fun (k : I) (x:(S k).Var)(y:Pane n)=> entrance (f k x) (fun z=> G k z x y) i' z
 have hD(i:I)(j:(S i).Var)(U:Pane n):Continuous (fun a=>v i a j U):= (trim_face (f i j)).1.smul ((hp i j U).shore.comp_continuous ((under_r i' z).comp (continuous_circleMap ..)) hK)
 have hπ(i j X)(t:X∈(S i).cap j):= Rue.rank_pi ((S i).paid j) (fun (y:Pane n) (hy:y∈(S i).cap j) a=> hc i a j y hy) (fun U u=> (hD i j U).stronglyMeasurable) (pC i) sky X t
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
omit hp g u p

abbrev portTrack (f : Z→Bool)(G : Key Z→ A) : List Z→ Key Z→ A
 | [] => G
 | i::l => portTrack f (entrance (f i) G i) l

include hp g u p
lemma eachTrack (f : ∀ i,(S i).Var→ Z → Bool)(l:List Z)(z:Key Z)(hz:z∈hill Z):
    Shady S W V (fun i k V=> portTrack (f i k) (fun z=>G i z k V) l z) := by
 induction l generalizing G with
 | nil=> exact g z hz
 | cons i l ih=>
    let G'(k:I)(z:Key Z)(j:(S k).Var)(V:Pane n):= entrance (f k j i) (fun x=> G k x j V) i z
    exact ih G' (fun x q=> allPad S W p u V G g hp (fun k j=> f k j i) i x q) (fun k j U=> entrance_bill (fun z=> G k z j U) (hp k j U) _ i)
omit hp g u p
lemma trackEnd (f : Z → Bool) (F : Key Z→ A) (p:River F) (l:List Z) (t:l.Nodup) :
    portTrack f F l 0= tipI F (l.filter f) := by
 induction l generalizing F with
 | nil=> rfl
 | cons i l ih=>
    obtain ⟨h,u⟩:= List.nodup_cons.mp t
    unfold portTrack; rw [ih _ (entrance_bill F p _ i) u,List.filter_cons]; split
    · rename_i v; exact lace_C _ (fun z (w:z∈hill Z)=> (entranceV F p _ i z w).trans (if_pos v)) roots
    rename_i v; exact (lace_C (l.filter f) (fun z (w:z∈hill Z)=> (entranceV F p _ i z w).trans (show _ = (F ∘dune i) z from if_neg v)) roots).trans (tip_V i _ (fun q => h (List.mem_filter.mp q).1))

abbrev Archive (X : Kine n P) (A:Type) : Kine n P where
 Var:= A × X.Var
 cap:= fun i=> X.cap i.2
 paid:= fun i=> X.paid i.2
 reads:=fun i=> X.reads i.2
 o:=X.o

include hp g u p
/-- Keep one assignment for each address i (independent even of the coefficient index L). -/
lemma charterTip :
    ∃ y:I→ℝ,(∀ i,0 ≤ y i)∧(∀ (L:Finset Z) i, Stirs (S i) (fun j U=>tipI (fun z=> G i z j U) (Cue Z L)) (y i))∧
        ∀ k:J,∑ i,W i k*y i ≤ V k := by
 let A(i):=Archive (S i) (Finset Z)
 let L:= cue Z
 have ht:L.Nodup:= Finset.sort_nodup ..
 let G'(k:I)(z:Key Z)(j:(A k).Var):= G k z j.2
 let f(k:I)(j:(A k).Var)(c:Z):= decide (c∈j.1)
 have hx(x:Key Z)(u:x∈hill Z):Shady A W V (fun i=> G' i x):=by
    obtain ⟨y,w,t,v⟩:=(g x u).pay; exact ⟨y,w,fun i j=>t i j.2,v⟩
 obtain ⟨y,h,t,e⟩:= (eachTrack A W p u V G' hx (fun _ j _=> hp _ _ _) f L 0 roots).pay
 refine ⟨y,h,fun B i j=>?_ ,e⟩
 let l : (A i).Var := (B,j); let C:= Cue Z B; let J:=(L.filter (f i l)); have hz:J.toFinset=B:= by ext x; simp [J,f,l,L,cue,Cue]
 have he(U:Pane n):tipI (fun z=>G i z j U) C = portTrack (f i l) (fun z=> G i z j U) L 0:= by
    rw [trackEnd _ _ (hp i j U) L ht]; let H:= Roots.orbit_ζ (t:=J) (hp i j U) (ht.filter _); rw [hz] at H; exact H
 unfold C at he; simp_rw [he]; exact t i l
end YM.CF.Mew
#print axioms YM.CF.Mew.charterTip
