import Organdy.Ketch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


open Push.Local Next.Rank.Spindle Next.SectorChange
open Scree
open scoped Classical
variable {c:Side}{r:Ratio c n}{L:Support c}
  {α b ζ e k β τ:ℝ}{m l:ℕ}
  {W:Config G n→ℂ}{A:Ink (Chip n)}
  {R: Rules G}
  {F X Y:Larva.Dir n}{U:Config G n}{o:Site n}

variable {x d u y :ℝ}
open Larva (Domaine)
variable {J:Type*}

private lemma land_count {I V:Type*}[Fintype I][Fintype V]
 (A:I→Finset V)(h:Pairwise (Disjoint on A))
 (g:V→Prop)(C:Finset I)(D:Finset V) (t:∀ i∈C, ¬∀w∈A i,g w)(e:∀i,¬g i→i∈D):
 C.card ≤ D.card :=by
 let s:=C
 have b(i:↥s):∃ w,w∈A i.val ∧ ¬g w:=by
   obtain ⟨v,t⟩:=not_forall.mp (t _ i.property)
   exact ⟨_,Classical.not_imp.mp t⟩
 choose w a p using b
 have k: Injective w:=by
   intro i j e
   by_contra y
   exact disjoint_left.mp (h (Subtype.coe_injective.ne y)) (a i) (show w i∈A _ from e.symm ▸ a j)
 exact Eq.ge (show (univ.image w).card=s.card by rw [card_image_of_injective _ k];simp)|>.trans
   (card_le_card (by intro v t;obtain ⟨i,g,rfl⟩:=mem_image.mp t;exact e _ (p i)))

-- sum_go. trap measures actual =4*bad units. define helper for good. 
variable [Fintype J]{z:Site n}
private abbrev sniff (r:Ratio c n)(m:ℕ)(L:Support c)(Y0:Finset (Cell n)):Site n→Prop:=withinCore r L (face_anchors Y0) (hallBill m)
private lemma waste {D:Ballroom J n}
 {Y0:Finset (Cell n)}
 (g:D.Space l z)
 (p:Odd r.count.val)
 (s:hallBill m ≤ r.count.val/2):
  let T:=univ.filter (fun i=>¬∀w∈D.area l z i,sniff r m L Y0 w)
  (4:ℝ)*(T.card:ℝ) ≤ trap r m L + trap_s m Y0:=by
 intro E
 have y:E.card≤_:=le_trans (land_count (D.area l z) g (sniff r m L Y0) E (univ.filter fun w=>¬withinCore r L (face_anchors Y0) (hallBill m) w) (fun i v=>(mem_filter.mp v).2) (fun w v=>mem_filter.mpr ⟨mem_univ _,v⟩)) (land_fee (r:=r) L Y0 p s)
 apply (mul_le_mul_of_nonneg_left ((Nat.cast_le (α:=ℝ)).mpr y) (by norm_num:(0:ℝ)≤4)).trans
 unfold trap trap_s;push_cast; exact le_of_eq (by ring)

lemma viewfind (B:Z.Bounds q θ η a)(P:Attached M Z)
 (j:BudgetPoint)
 (C:Wicket R ζ b k x α j.threshold v d u y)
 (h:Domaine l ζ j.threshold α b W A)
 {D:Ballroom J n}
 (g:D.Space l z)
 (p:Odd r.count.val)(s:hallBill m ≤ r.count.val/2)
 (dB:0<β)
 {T t H ε:ℝ} (hT:0 ≤ T) (jH:0≤H)
 (tX: |t| * (u^2+(b*k)^2) ≤ 4*H)
 (tY: |t| * (y*(2*u+y)) ≤ T)
 (Y0: Finset (Cell n)):
   let V:=soiree q k (Real.sqrt x * coupling β) A z D
   let φ:= canvas j.threshold t (Fintype.card J*(b*k)^2) (nectar x W z D)
   ShelfScene B P j r m β v ε (Fintype.card J*T + H*(trap r m L+trap_s m Y0)) L Y0 t φ V:=by
 intro V φ U X Y _ h' h0 h1
 subst Y0
 let Δ:=misdemean j.threshold U; let G1:=sniff r m L Δ
 let E:=univ.filter (fun i=>¬∀w∈D.area l z i,G1 w)
 have hp: (4:ℝ)*E.card≤_:=waste (Y0:=Δ) (L:=L) g p s
 let Z₀:=starFeed B P r L (face_anchors Δ) m Y β X

 by_cases z0:Drier G j.threshold U; swap
 · have d1: |V Z₀| ≤ Fintype.card J*(b*k)^2:=soiree_limit z D C.kpos h.purse Z₀
   have hD:=darkness j.threshold t _ (nectar x W z D) _ d1 z0
   exact hD.trans (le_add_of_nonneg_right (by
     have h₁:0≤trap r m L+trap_s m Δ:=(by positivity: (0:ℝ)≤4*E.card).trans hp
     change 0≤ (Fintype.card J:ℝ)*T+H*(trap r m L+trap_s m Δ)
     exact add_nonneg (mul_nonneg (by positivity) hT) (mul_nonneg jH h₁)))
 let J0(i:J):=(cistern x W z (D.path i) (D.post i) U).re
 let J1(i:J):=compose q k (Real.sqrt x * coupling β) A z (D.path i) (D.post i) Z₀
 have hm(i:J): t*(J0 i - J1 i) ≤ T + (if i∈E then 4*H else 0):=by
    refine (le_abs_self _).trans ?_;rw [abs_mul]; split
    · have d: |J0 i|≤u^2:=(Complex.abs_re_le_norm _).trans (cistern_rate h C ..)
      have t': |J1 i|≤(b*k)^2:=compose_limit C.kpos h.purse .. 
      exact (mul_le_mul_of_nonneg_left ((abs_sub ..).trans (add_le_add d t')) (abs_nonneg _)).trans
        (tX.trans (le_add_of_nonneg_left hT))

    rename_i hW
    have g1:∀w∈D.area l z i,G1 w :=by
       by_contra h'
       exact hW (mem_filter.mpr ⟨mem_univ _,h'⟩)
    have g2 (o)(y:o∈({D.post i,D.back z i}:Finset _)):Onyx r L (mists j.threshold U) m l o:=by
       intro v t
       have tv:separation o v ≤ l+2:=by simpa [halo_spec] using t
       exact g1 v (halo_spec.mpr ⟨o,y,tv⟩)
    have q:=cistern_cost B P C h z (D.path i) (D.post i) (g2 _ (mem_insert_self ..)) (g2 (D.back z i) (by simp)) h1 z0 h0 dB
    rw [add_zero]
    exact (mul_le_mul_of_nonneg_left q (abs_nonneg t)).trans tY
 unfold φ canvas
 rw [if_pos z0]
 apply sub_le_iff_le_add'.mp
 change t*(∑i,J0 i) - t*(∑i,J1 i)≤_
 rw [←mul_sub,←sum_sub_distrib,mul_sum]
 refine (sum_le_sum (fun i _=>hm i)).trans ?_
 rw [sum_add_distrib,←sum_filter]
 simp only [sum_const,card_univ,nsmul_eq_mul,filter_mem_eq_inter,univ_inter]
 exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hp jH).trans' (le_of_eq (by ring)))
