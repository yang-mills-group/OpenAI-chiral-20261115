import YM.SU5.Relativistic.Thatch
import YM.SU5.Relativistic.Rubbish
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
local notation "J"=> Link N
local notation "O"=> Face (Per N)
local notation "V"=> Site C
variable (G: Gauge)(p:Clip){σ a b:ℝ}(B:PathData G)
open scoped Classical
local notation "S"=> Config G N

def Beat(R:ℝ)(x: S):= (univ:Finset V).filter fun i=>¬ ∀ j:P_, PathData.kept p R (setDown L i j) x
lemma beat_g (R:ℝ)(x:S)(i:T_)(v:i∈(Beat L G p R x)ᶜ)(j:P_): PathData.kept p R (setDown L i j) x:= by by_contra w; exact mem_compl.mp v (mem_filter.mpr ⟨mem_univ _,fun v=> w (v j)⟩)
lemma beat_guard (t:ℝ)(x:S)(i:T_)(v:i∈(Beat L G p t x)ᶜ): tray L G i x∈ Mild W_ G t:=by
 intro a z; have he:= beat_g L G p t x i ‹_› a.1 (zipFace L i a); rw [ort_s L x (tray L G i x) i (fun _ _=> rfl) a z] at he; simpa only [zipFace, separation_self,Nat.cast_zero,zero_div, Real.exp_zero,mul_one] using he

open Pressure (temp radiusB)
lemma beat_budget (p: Clip): ∀ᶠ r:ℝ in atTop,∀ {C N:Side}(t:Ratio C N)(x:Config G N), (Beat t G p (temp r) x).card≤ (flags (temp r) x).card * hose r:=by
 -- notation independent
 filter_upwards [Work.E04.eventually_room 0 p.relaxation p.radius_pos,eventually_gt_atTop (0:ℝ)] with r he h C N L x; let B:=halo (radiusB r) (flags (temp r) x); let f(i:Site N):=((slot L).symm i).1; have hp: 0<temp r:= (BProof.thresh_eq h) ▸ BProof.coin_pos r (-1/2) 1 0
 apply le_trans _ (Corona.halo_size (flags (temp r) x) (radiusB r)); refine (card_le_card (t:= B.image f) ?_).trans card_image_le; intro i v; have hs:= (mem_filter.mp v).2; obtain ⟨j,k⟩:= not_forall.mp hs; obtain ⟨q,l⟩:=not_forall.mp k; let u:=setDown L i j; have hx:=lt_of_not_ge l; let n:= separation u q.1
 have hh : n+1≤ radiusB r/50:= he.2 n (by rw [add_zero]; exact hx.trans_le (G.chord_le_two _))
 refine mem_image.mpr ⟨u,halo_spec.mpr ⟨q.1,(flags_spec ..).2 ⟨q,WilsonStartup.anchor_visit _,lt_of_le_of_lt ?_ hx⟩,le_trans (Eq.le (separation_comm ..)) (show n≤ radiusB r from by omega)⟩,?_⟩
 · exact le_mul_of_one_le_right hp.le (Real.one_le_exp (div_nonneg (by positivity) p.radius_pos.le))
 exact congrArg Prod.fst ((slot L).symm_apply_apply (i,j))

variable {T:BudgetPoint}
local notation "t_"=> T.threshold
private lemma pillar(x:S)(i:Face (Per N)): B.baseTerm p T x i= clipped p t_ (G.chord (faceValue x i))+ ‖column B (kiosk p t_ x) i‖^2/2:=by
 unfold column kiosk PathData.baseTerm; by_cases v: kept p t_ i.1 x
 · simp only [v,↓reduceIte]; rfl
 simp [v]
lemma beats_cost (R:ℕ)(x:S)(u:B.Bounds p σ a b)(ha:1≤ p.relaxation*σ) (r:ℝ)(hr:0<r) (hB:(1+1/r)*vane σ a R ≤ r*p.linear) (g:r<1/4):
 let t:= T.threshold; let α:=1-4*r; let Q:=tollD G p t x
 2*r*Q+α/2*∑ i∈(Beat L G p t x)ᶜ, boxE G B R p (tray L G i x)≤∑ i:Face (Per N),B.baseTerm p T x i:=by
 intro t α Q; let A:=(Beat L G p t x)ᶜ; let θ:=kiosk p t x
 let f(i:Face (Per N)):=clipped p t (G.chord (faceValue x i)); let Z(i:Face (Per N)):= column B θ i; let F(i:Face (Per N)):= cutlow B θ i R
 simp_rw [pillar,sum_add_distrib, ← sum_div]; change 2*r*Q+α/2*_≤ Q+(∑ i:Face (Per N),‖Z i‖^2)/2
 have hf:∑ i:Face (Per N),‖Z i-F i‖^2 ≤ vane σ a R*(p.linear⁻¹*Q):=(tail_G u θ (ticket_s ha T.threshold_pos.le x) R).1
 have hv(i): ‖F i‖^2≤ (1+r)*‖Z i‖^2+(1+1/r)*‖Z i-F i‖^2:=by
    let a:= ‖Z i‖; let b:= ‖Z i-F i‖; have he:‖F i‖≤ a+b:=le_trans (le_of_eq (congrArg norm (show F i= Z i-(Z i-F i) by abel))) (norm_sub_le ..)
    refine (pow_le_pow_left₀ (norm_nonneg _) he 2).trans ?_; rw [show (1+r)*a^2+(1+1/r)*b^2=((1+r)*r*a^2+(1+r)*b^2)/r from by field_simp; ring]; rw [le_div_iff₀ hr]; nlinarith only [sq_nonneg (r*a-b)] -- rw a b tune
 have hy : ∑ i ∈ A, p.direct*crateB G (tray L G i x)≤ 2*Q:=by
    let P:= A.biUnion (mounted L)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (f:=f) (subset_univ P) fun i _ _=> clip_pos _ T.threshold_pos.le (G.chord_nonneg _)) zero_le_two); unfold P; rw [sum_biUnion,mul_sum]; swap
    · intro i h j p e -- tune
      exact Finset.disjoint_left.mpr (fun {a} v u=>by obtain ⟨x,h,rfl⟩:=mem_map.mp v; obtain ⟨y,p,g⟩:=mem_map.mp u; exact room_diff L i j e _ _ g.symm)
    refine sum_le_sum fun i h=>le_of_eq ?_; unfold mounted crateB; rw [sum_map,mul_sum,mul_sum]; refine sum_congr rfl fun j hP=> ?_; have he:=(show tray L G i x∈ Mild W_ G t from beat_guard L G p t x i h)
    have hx:= (show girth G (tray L G i x) j≤t from he j hP)
    unfold f; rw [show chip L i j=zipFace L i j from rfl, ort_s L x (tray L G i x) i (fun _ _=> rfl) j hP,clipped,if_pos hx]; unfold girth; ring
 let W(i:T_):= ∑ j∈plumb W_ R,‖Pressure.shorten B R 1 (tray L G i x) j‖^2
 have hw: (∑ i∈ A,W i)≤ ∑ i:Face (Per N), ‖F i‖^2:=by
    let P:= A.biUnion (plumage L R); refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (f:=fun i=> ‖F i‖^2) (subset_univ P) fun _ _ _=>sq_nonneg _); unfold P; rw [sum_biUnion]; swap
    · intro i h j p e; exact Finset.disjoint_left.mpr fun {a} g x=>by obtain ⟨v,t,rfl⟩:=mem_map.mp g; obtain ⟨u,q,w⟩:=mem_map.mp x; exact room_diff L i j e _ _ w.symm
    apply sum_le_sum; intro i g; unfold W plumage; rw [sum_map]; refine le_of_eq (sum_congr rfl fun j e=>?_); rw [←plum_s L x (tray L G i x) B R i j e (fun _ _=>rfl)]; refine congrArg (fun a:G.Color=> ‖a‖^2) (tsum_congr fun l=>?_); unfold Pressure.shortenTerm; rw [mul_one,show chip L i j=zipFace L i j from rfl]; split; next q=>
      have he:= beat_g L G p t x i g j.1; change _=(B.row j.2 l).1 • kiosk p t x _ (setDown L i j.1); unfold kiosk; rw [if_pos he] <;> rfl
    next q=> rfl
 have hs:= sum_le_sum (s:=univ) fun i _=> hv i; rw [sum_add_distrib, ←mul_sum,←mul_sum] at hs
 have hp:0≤Q:=toll_pos x p T.threshold_pos.le; have hl:= mul_le_mul_of_nonneg_left hf (show 0≤1+1/r by positivity); have hr':0 < p.linear:= p.tail_pos
 have ht:(1+1/r)*(vane σ a R*(p.linear⁻¹*Q))≤ r*Q:=by
   calc _=((1+1/r)*vane σ a R)*(p.linear⁻¹*Q):=by ring
        _≤ (r*p.linear)*(p.linear⁻¹*Q):= mul_le_mul_of_nonneg_right hB (by positivity)
        _=_:=by field_simp
 have hW:0<α:=by unfold α; linarith; -- capture newline
 have hE:= hw.trans (hs.trans (add_le_add_right (hl.trans ht) _)); unfold boxE; rw [sum_add_distrib]; apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hy hE) (div_nonneg hW.le zero_le_two)) _); unfold α; let X:= ∑ i:Face (Per N),‖Z i‖^2; change 2*r*Q+(1-4*r)/2*(2*Q+((1+r)*X+r*Q))≤ _; have hx:0≤X:=sum_nonneg fun _ _=>sq_nonneg _; change _ ≤ Q+X/2
 nlinarith only [hp,hx,mul_nonneg hr.le hp,mul_nonneg hr.le hx,mul_nonneg (sq_nonneg r) hp,mul_nonneg (sq_nonneg r) hx]
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.beats_cost
